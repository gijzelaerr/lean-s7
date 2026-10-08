# ruff: noqa: BLE001  (any python-snap7 exception, whatever its type, counts as a rejection)
"""Run the conformance corpus against python-snap7's own codecs.

Differential evidence only: python-snap7 is not the protocol specification, so a
disagreement is a lead that needs independent evidence, not a verdict. Every case
is classified as

* ``agree``       python-snap7 produced the corpus result;
* ``gap``         python-snap7 has no API that expresses the case;
* ``ambiguity``   results differ only in bytes the protocol leaves unspecified
                  (for example padding after the current length of a STRING);
* ``disagree``    python-snap7 accepted/rejected or produced different bytes.

The classification of every case is recorded in
``integration/python_snap7_baseline-<version>.json``. The run fails when any case's status
differs from the baseline, so a python-snap7 fix, a regression or a corpus change
is noticed. ``--update-baseline`` rewrites it after review. One baseline is kept per reviewed python-snap7 version. No sockets or controllers are used.

    python integration/python_snap7_consumer.py [--update-baseline] [--list STATUS]
"""

from __future__ import annotations

import argparse
import datetime
import importlib.metadata
import inspect
import json
import struct
import sys
from collections import Counter
from collections.abc import Callable
from pathlib import Path
from typing import Any

from snap7.connection import ISOTCPConnection
from snap7.datatypes import S7Area, S7WordLen
from snap7.s7protocol import S7Protocol
from snap7.util import getters, setters

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "conformance" / "v1"

AGREE, GAP, AMBIGUITY, DISAGREE = "agree", "gap", "ambiguity", "disagree"


class Gap(Exception):
    """python-snap7 has no API that expresses this case."""


def expand(spec: Any) -> bytes:
    """Expand a corpus byte specification (integer array or chunk object)."""
    if isinstance(spec, list):
        return bytes(spec)
    out = bytearray()
    for chunk in spec["chunks"]:
        if "hex" in chunk:
            out += bytes.fromhex(chunk["hex"])
        elif "bytes" in chunk:
            out += bytes(chunk["bytes"])
        else:
            repeat = chunk["repeat"]
            byte = repeat["byte"] if "byte" in repeat else int(repeat["byte_hex"], 16)
            out += bytes([byte]) * repeat["count"]
    return bytes(out)


class Outcome:
    def __init__(self, status: str, detail: str = "") -> None:
        self.status = status
        self.detail = detail


def agree() -> Outcome:
    return Outcome(AGREE)


def differ(detail: str) -> Outcome:
    return Outcome(DISAGREE, detail)


def verdict(
    expected: dict[str, Any], accepted: bool, matches: bool, detail: str
) -> Outcome:
    """Compare accept/reject and, for accepted cases, whether the result matched."""
    want = expected["status"] == "accept"
    if want != accepted:
        return differ(
            f"corpus {expected['status']}, python-snap7 {'accepted' if accepted else 'rejected'}"
        )
    if accepted and not matches:
        return differ(detail)
    return agree()


class FakeSocket:
    def __init__(self, data: bytes) -> None:
        self.buffer = bytearray(data)

    def recv(self, count: int) -> bytes:
        chunk = bytes(self.buffer[:count])
        del self.buffer[:count]
        return chunk


def connection() -> ISOTCPConnection:
    return ISOTCPConnection("127.0.0.1")


# --- TPKT / COTP ---------------------------------------------------------------


def tpkt_encode(case: dict[str, Any]) -> Outcome:
    payload = expand(case["payload"])
    try:
        packet = connection()._build_tpkt(payload)
    except Exception:
        return verdict(case["expected"], False, False, "")
    expected = case["expected"]
    return verdict(
        expected,
        True,
        expected["status"] == "accept" and packet == expand(expected["packet"]),
        "packet bytes differ",
    )


def tpkt_decode(case: dict[str, Any]) -> Outcome:
    # python-snap7 has no standalone TPKT decoder: receive_data() composes the
    # TPKT header, a socket stream and the COTP data header.
    expected = case["expected"]
    packet = expand(case["packet"])
    if expected["status"] == "accept":
        payload = expand(expected["payload"])
        if payload[:3] != b"\x02\xf0\x80":
            raise Gap(
                "accepted TPKT payload is not a COTP data TPDU; python-snap7 cannot decode TPKT alone"
            )
    conn = connection()
    conn.connected = True
    conn.socket = FakeSocket(packet)  # type: ignore[assignment]
    try:
        data = conn.receive_data()
    except Exception:
        return verdict(expected, False, False, "")
    return verdict(
        expected,
        True,
        expected["status"] == "accept" and data == payload[3:],
        "payload differs",
    )


def cotp_encode(case: dict[str, Any]) -> Outcome:
    if not case["end_of_transmission"]:
        raise Gap("_build_cotp_dt always sets the end-of-transmission bit")
    packet = connection()._build_cotp_dt(expand(case["payload"]))
    if packet != expand(case["expected"]):
        return differ("COTP DT bytes differ")
    return agree()


def cotp_decode(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    if expected["status"] == "accept" and not expected["end_of_transmission"]:
        raise Gap("python-snap7 does not expose the end-of-transmission flag")
    try:
        data = connection()._parse_cotp_data(expand(case["packet"]))
    except Exception:
        return verdict(expected, False, False, "")
    return verdict(
        expected,
        True,
        expected["status"] == "accept" and data == expand(expected["payload"]),
        "payload differs",
    )


# --- S7 ------------------------------------------------------------------------


def ack_data(parameters: bytes, data: bytes) -> bytes:
    return (
        struct.pack(">BBHHHHBB", 0x32, 3, 0, 1, len(parameters), len(data), 0, 0)
        + parameters
        + data
    )


def s7_response(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    protocol = S7Protocol()
    pdu = ack_data(bytes(case["parameters"]), bytes(case["data"]))
    try:
        parsed = protocol.parse_response(pdu)
        if case["operation"] == "read":
            payload = bytes(
                protocol.extract_read_data(
                    parsed, S7WordLen.BYTE, case["requested_bytes"]
                )
            )
            return verdict(
                expected,
                True,
                payload == bytes(expected.get("payload", [])),
                f"payload {list(payload)} vs {expected.get('payload')}",
            )
        # python-snap7's write check never looks at the response function.
        protocol.check_write_response(parsed)
        return verdict(expected, True, True, "")
    except Exception:
        return verdict(expected, False, False, "")


def s7_upload(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    protocol = S7Protocol()
    try:
        parsed = protocol.parse_response(bytes(case["pdu"]))
        payload, is_last = protocol.parse_upload_fragment(parsed)
    except Exception:
        return verdict(expected, False, False, "")
    if expected["status"] == "accept":
        matches = (
            payload == bytes(expected["payload"]) and is_last == expected["is_last"]
        )
        return verdict(
            expected, True, matches, f"fragment {payload.hex()}/{is_last} differs"
        )
    return verdict(expected, True, False, "")


def userdata_response(group: int, sub: int, payload: bytes, seq: int = 1) -> bytes:
    """A well-formed USER_DATA response around ``payload`` (reference 1)."""
    parameters = bytes([0, 1, 0x12, 8, 0x12, 0x80 | group, sub, seq, 0, 0, 0, 0])
    data = bytes([0xFF, 9]) + struct.pack(">H", len(payload)) + payload
    return (
        struct.pack(">BBHHHH", 0x32, 7, 0, 1, len(parameters), len(data))
        + parameters
        + data
    )


def datetime_of(fields: dict[str, int]) -> datetime.datetime:
    return datetime.datetime(
        fields["year"],
        fields["month"],
        fields["day"],
        fields["hour"],
        fields["minute"],
        fields["second"],
        fields["millisecond"] * 1000,
        tzinfo=datetime.UTC,
    )


# --- S7 requests ---------------------------------------------------------------

SECRET = "SECRET"
REQUESTS: dict[str, Callable[[S7Protocol], bytes]] = {
    "read_clock": lambda p: p.build_get_clock_request(),
    "list_blocks": lambda p: p.build_list_blocks_request(),
    "list_data_blocks": lambda p: p.build_list_blocks_of_type_request(0x41),
    "plc_stop": lambda p: p.build_plc_control_request("stop"),
    "plc_hot_start": lambda p: p.build_plc_control_request("hot_start"),
    "plc_cold_start": lambda p: p.build_plc_control_request("cold_start"),
    "start_db_upload": lambda p: p.build_start_upload_request(0x41, 1),
    "upload_fragment": lambda p: p.build_upload_request(7),
    "end_upload": lambda p: p.build_end_upload_request(7),
    "set_clock": lambda p: p.build_set_clock_request(
        datetime.datetime(2026, 9, 23, 12, 34, 56, 789000, tzinfo=datetime.UTC)
    ),
    "set_password": lambda p: p.build_set_session_password_request(
        p.encode_password(SECRET)
    ),
    "clear_password": lambda p: p.build_clear_session_password_request(),
    "get_db_info": lambda p: p.build_get_block_info_request(0x41, 1),
    "download_fragment_response": lambda p: p.build_download_fragment_response(
        1, False, b"\xde\xad"
    ),
    "final_download_fragment_response": lambda p: p.build_download_fragment_response(
        1, True, b"\xbe\xef"
    ),
    "download_ended_response": lambda p: p.build_download_ended_response(1),
}


def s7_request(case: dict[str, Any]) -> Outcome:
    builder = REQUESTS.get(case["operation"])
    if builder is None:
        raise Gap(f"no python-snap7 builder for {case['operation']}")
    want = bytes(case["expected_packet"])
    try:
        got = builder(S7Protocol())
    except AttributeError as error:
        raise Gap(f"this python-snap7 lacks the builder: {error}") from error
    except Exception as error:
        return differ(f"builder raised {type(error).__name__}: {error}")
    if got == want:
        return agree()
    if (
        case["operation"] == "set_clock"
        and got[:-1] == want[:-1]
        and (got[-1] & 0xF0) == (want[-1] & 0xF0)
    ):
        return Outcome(
            AMBIGUITY,
            "only the weekday nibble differs: python-snap7 derives it from the date",
        )
    first = next(
        (i for i, (a, b) in enumerate(zip(got, want, strict=False)) if a != b),
        min(len(got), len(want)),
    )
    return differ(
        f"packet differs at byte {first}: python-snap7 {got.hex()} corpus {want.hex()}"
    )


# --- USER_DATA responses and management codecs --------------------------------


# (group, subfunction) of the USER_DATA services whose success acknowledgement carries no data.
NO_DATA_SERVICES = {(7, 2), (5, 1), (5, 2)}


def userdata_case(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    group = case.get("group", case.get("expected_group"))
    sub = case.get("subfunction", case.get("expected_subfunction"))
    protocol = S7Protocol()
    try:
        parsed = protocol.parse_response(bytes(case["pdu"]))
        if "reference" in case:
            protocol.sequence = case["reference"]
            protocol.validate_pdu_reference(parsed["sequence"])
        # Services that return no data (set clock, session passwords) are acknowledged
        # with return code 0x0a; python-snap7 after #940 accepts that only when asked.
        options = (
            {"accept_null_ack": True}
            if (group, sub) in NO_DATA_SERVICES
            and "accept_null_ack"
            in inspect.signature(protocol.check_userdata_response).parameters
            else {}
        )
        protocol.check_userdata_response(parsed, group, sub, **options)
    except Exception:
        return verdict(expected, False, False, "")
    if expected["status"] != "accept":
        return verdict(expected, True, False, "")
    parameters = parsed.get("parameters") or {}
    data = parsed.get("data") or {}
    got = {
        "sequence": parameters.get("sequence_number"),
        "has_more": bool(parameters.get("last_data_unit")),
        "payload": list(data.get("data", b"")),
    }
    # Single-response operation cases state only the payload.
    want = {
        "sequence": expected.get("sequence"),
        "has_more": expected.get("has_more_data"),
        "payload": expected["payload"],
    }
    want = {key: value for key, value in want.items() if value is not None}
    got = {key: got[key] for key in want}
    return verdict(expected, True, got == want, f"{got} vs {want}")


def block_counts(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    protocol = S7Protocol()
    try:
        parsed = protocol.parse_response(
            userdata_response(3, 1, bytes(case["payload"]))
        )
        counts = protocol.parse_list_blocks_response(parsed)
    except Exception:
        return verdict(expected, False, False, "")
    if expected["status"] != "accept":
        return verdict(expected, True, False, "")
    names = {
        "OBCount": "organization_blocks",
        "FBCount": "function_blocks",
        "FCCount": "functions",
        "SFBCount": "system_function_blocks",
        "SFCCount": "system_functions",
        "DBCount": "data_blocks",
        "SDBCount": "system_data_blocks",
    }
    got = {names[key]: value for key, value in counts.items() if key in names}
    return verdict(
        expected, True, got == expected["counts"], f"{got} vs {expected['counts']}"
    )


def block_list(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    protocol = S7Protocol()
    try:
        parsed = protocol.parse_response(
            userdata_response(3, 2, bytes(case["payload"]))
        )
        numbers = protocol.parse_list_blocks_of_type_response(parsed)
    except Exception:
        return verdict(expected, False, False, "")
    if expected["status"] != "accept":
        return verdict(expected, True, False, "")
    want = [entry["number"] for entry in expected["entries"]]
    return verdict(expected, True, list(numbers) == want, f"{numbers} vs {want}")


def block_info(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    protocol = S7Protocol()
    try:
        parsed = protocol.parse_response(
            userdata_response(3, 3, bytes(case["payload"]))
        )
        info = protocol.parse_get_block_info_response(parsed)
    except Exception:
        return verdict(expected, False, False, "")
    if expected["status"] != "accept":
        return verdict(expected, True, False, "")
    want = expected["info"]
    pairs = {
        "number": (info.get("block_number"), want["number"]),
        "mc7": (info.get("mc7_size"), want["mc7_size"]),
        "load": (info.get("load_size"), want["load_size"]),
        "local": (info.get("local_data"), want["local_data_size"]),
        "sbb": (info.get("sbb_length"), want["sbb_size"]),
        "checksum": (info.get("checksum"), want["checksum"]),
        "version": (info.get("version"), want["version"]),
        "flags": (info.get("block_flags"), want["flags"]),
        "language": (info.get("block_lang"), want["language"]),
        "outer type": (info.get("block_type"), want["block_type"]),
        "code date": (list(info.get("code_date", b"")), want["code_date"]),
        "interface date": (list(info.get("intf_date", b"")), want["interface_date"]),
    }
    wrong = [f"{k}: {a!r} vs {b!r}" for k, (a, b) in pairs.items() if a != b]
    return verdict(expected, True, not wrong, "; ".join(wrong))


# --- Clock ---------------------------------------------------------------------


def s7_weekday(fields: dict[str, int]) -> int:
    """S7 DATE_AND_TIME weekday: Sunday = 1 ... Saturday = 7 (native Snap7: tm_wday + 1)."""
    return datetime_of(fields).isoweekday() % 7 + 1


def clock_case(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    wire = expand(case["data"])
    protocol = S7Protocol()
    issues: list[str] = []
    if case["operation"] == "roundtrip":
        fields = case["input_value"]
        if expected["status"] != "accept" and fields["weekday"] not in range(1, 8):
            raise Gap(
                "python-snap7 derives the weekday from the date; it cannot be supplied"
            )
        try:
            request = protocol.build_set_clock_request(datetime_of(fields))
        except Exception:
            return verdict(expected, False, False, "")
        if expected["status"] != "accept":
            return verdict(expected, True, False, "")
        payload = request[-10:]
        encoded = expand(expected["encoded"])
        # The final byte is the millisecond digit and weekday nibble: the corpus
        # supplies an arbitrary weekday, python-snap7 computes one. Compare the rest
        # exactly, then check python-snap7's weekday against the S7 convention.
        if payload[:9] != encoded[:9] or (payload[9] & 0xF0) != (encoded[9] & 0xF0):
            return differ(f"encoded {payload.hex()}, corpus {encoded.hex()}")
        if payload[9] & 0x0F != s7_weekday(fields):
            issues.append(
                f"weekday nibble {payload[9] & 0x0F}, S7 convention (Sunday=1) {s7_weekday(fields)}"
            )
    # Decode: python-snap7 reads an eight-byte clock (no century byte), while the
    # request it builds above, native Snap7 and the corpus use the ten-byte form.
    try:
        parsed = protocol.parse_response(userdata_response(7, 1, wire))
        decoded = protocol.parse_get_clock_response(parsed)
    except Exception as error:
        if expected["status"] == "accept":
            issues.append(f"ten-byte clock reply rejected: {error}")
            return differ("; ".join(issues))
        return agree()
    if expected["status"] != "accept":
        visible_digits_valid = all(
            (byte >> 4) <= 9 and (byte & 0x0F) <= 9 for byte in wire[2:8]
        )
        if visible_digits_valid:
            return Outcome(
                AMBIGUITY,
                "python-snap7 decodes no weekday or milliseconds, the only invalid fields",
            )
        return differ("ten-byte clock payload with invalid BCD digits accepted")
    want = expected["value"]
    got = (
        decoded.year,
        decoded.month,
        decoded.day,
        decoded.hour,
        decoded.minute,
        decoded.second,
    )
    ref = (
        want["year"],
        want["month"],
        want["day"],
        want["hour"],
        want["minute"],
        want["second"],
    )
    return verdict(expected, True, got == ref, f"{got} vs {ref}")


# --- Writes and multi-item -----------------------------------------------------


def word_write(case: dict[str, Any]) -> Outcome:
    protocol = S7Protocol()
    payload = bytes(case["payload"])
    try:
        request = protocol.build_write_request(S7Area.DB, 1, 0, S7WordLen.WORD, payload)
    except Exception as error:
        return differ(f"builder raised {type(error).__name__}: {error}")
    bit_length = case["count"] * case["element_bytes"] * 8
    tail = request[-(len(payload) + 4) :]
    if tail[4:] != bytes(case["expected_payload"]):
        return differ(f"data payload {tail[4:].hex()} differs")
    if struct.unpack(">H", tail[2:4])[0] != bit_length:
        return differ(
            f"bit length {struct.unpack('>H', tail[2:4])[0]}, corpus {bit_length}"
        )
    return agree()


def multi_item(case: dict[str, Any]) -> Outcome:
    if case["operation"] != "read":
        raise Gap("python-snap7 has no multi-variable write builder")
    protocol = S7Protocol()
    items = [(0x84, r["db_number"], r["start"], r["count"]) for r in case["ranges"]]
    want_request = bytes(case["request_pdu"])
    expected = case["expected"]
    if expected["status"] == "accept":
        try:
            got = protocol.build_multi_read_request(items)
        except Exception as error:
            return differ(f"multi-read builder raised {error}")
        if got != want_request:
            return differ(
                f"request differs: python-snap7 {got.hex()} corpus {want_request.hex()}"
            )
    protocol = S7Protocol()
    try:
        parsed = protocol.parse_response(bytes(case["response_pdu"]))
        blocks = protocol.extract_multi_read_data(parsed, len(items))
    except Exception:
        if expected["status"] == "accept":
            return differ("response with a failed item aborts the whole multi-read")
        return agree()
    if expected["status"] != "accept":
        return verdict(expected, True, False, "")
    want = [
        bytes(i["payload"]) if i["status"] == "success" else None
        for i in expected["items"]
    ]
    return verdict(
        expected, True, [bytes(b) for b in blocks] == want, f"{blocks} vs {want}"
    )


# --- Typed values --------------------------------------------------------------

INTEGERS: dict[str, tuple[Callable[..., Any], Callable[..., Any] | None, int, str]] = {
    "uint8": (getters.get_usint, setters.set_usint, 1, ">B"),
    "int8": (getters.get_sint, setters.set_sint, 1, ">b"),
    "uint16": (getters.get_uint, setters.set_uint, 2, ">H"),
    "int16": (getters.get_int, setters.set_int, 2, ">h"),
    "uint32": (getters.get_udint, setters.set_udint, 4, ">I"),
    "int32": (getters.get_dint, setters.set_dint, 4, ">i"),
    "uint64": (getters.get_ulint, setters.set_lword, 8, ">Q"),
    "int64": (getters.get_lint, None, 8, ">q"),
}


def integer_case(case: dict[str, Any]) -> Outcome:
    getter, setter, size, _ = INTEGERS[case["codec"]]
    expected = case["expected"]
    data = bytearray(expand(case["data"]))
    try:
        value = getter(data, case["offset"])
        if len(data) < case["offset"] + size:
            raise IndexError
    except Exception:
        return verdict(expected, False, False, "")
    if expected["status"] != "accept":
        return verdict(expected, True, False, "")
    detail = ""
    matches = str(value) == expected["value"]
    if not matches:
        detail = f"decoded {value}, corpus {expected['value']}"
    if matches and setter is None:
        return Outcome(GAP, "no signed 64-bit encoder in python-snap7 (decoder agrees)")
    if matches and setter is not None:
        buffer = bytearray(size)
        try:
            setter(buffer, 0, int(case["input_value"]))
        except Exception as error:
            return differ(f"encoder rejected {case['input_value']}: {error}")
        if bytes(buffer) != expand(expected["encoded"]):
            return differ(
                f"encoded {bytes(buffer).hex()}, corpus {expand(expected['encoded']).hex()}"
            )
    return verdict(expected, True, matches, detail)


def string_case(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    wide = case["encoding"] == "utf-16-be"
    getter = getters.get_wstring if wide else getters.get_string
    if case["operation"] == "roundtrip" and expected["status"] != "accept":
        # Corpus requires the *encoder* to refuse this input or capacity.
        scratch = bytearray(4 + 2 * 16382)
        try:
            if wide:
                setters.set_wstring(scratch, 0, case["input_value"], case["maximum"])
            else:
                setters.set_string(scratch, 0, case["input_value"], case["maximum"])
        except Exception:
            return agree()
        return differ("corpus rejects the encode request, python-snap7 accepted it")
    data = bytearray(expand(case["data"]))
    offset = case["offset"]
    try:
        value = getter(data, offset)
        if expected["status"] == "accept":
            header = 4 if wide else 2
            declared = (
                struct.unpack(">H", data[offset : offset + 2])[0]
                if wide
                else data[offset]
            )
            if len(data) < offset + header + declared * (2 if wide else 1):
                raise IndexError("short storage")
    except Exception:
        return verdict(expected, False, False, "")
    if expected["status"] != "accept":
        return verdict(expected, True, False, "")
    if value != expected["value"]:
        return differ(f"decoded {value!r}, corpus {expected['value']!r}")
    if case["operation"] != "roundtrip":
        return agree()
    want = expand(expected["encoded"])
    buffer = bytearray(len(want))
    try:
        if wide:
            setters.set_wstring(buffer, 0, case["input_value"], case["maximum"])
        else:
            setters.set_string(buffer, 0, case["input_value"], case["maximum"])
    except Exception as error:
        return differ(f"encoder rejected the input: {error}")
    if bytes(buffer) == want:
        return agree()
    header = 4 if wide else 2
    used = header + len(case["input_value"]) * (2 if wide else 1)
    if bytes(buffer[:used]) == want[:used]:
        return Outcome(AMBIGUITY, "bytes after the current length differ")
    return differ(f"encoded {bytes(buffer).hex()}, corpus {want.hex()}")


def assemble(
    protocol: S7Protocol,
    responses: list[bytes],
    group: int,
    sub: int,
    references: list[int],
) -> tuple[bool, list[int], int | None]:
    """Parse, validate and concatenate a USER_DATA fragment sequence.

    python-snap7 has no assembler, so this follows the loop its clients would
    run: validate each reply and stop at the one without the continuation flag.
    Returns (completed, payload, index of the rejected or last fragment)."""
    payload: list[int] = []
    for index, (pdu, reference) in enumerate(zip(responses, references, strict=True)):
        try:
            parsed = protocol.parse_response(pdu)
            protocol.sequence = reference
            protocol.validate_pdu_reference(parsed["sequence"])
            protocol.check_userdata_response(parsed, group, sub)
        except Exception:
            return False, payload, index
        payload += list((parsed.get("data") or {}).get("data", b""))
        if not (parsed.get("parameters") or {}).get("last_data_unit"):
            return True, payload, index
    return False, payload, None


def userdata_conversation(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    responses = [bytes(pdu) for pdu in case["response_pdus"]]
    done, payload, stop = assemble(
        S7Protocol(),
        responses,
        case["expected_group"],
        case["expected_subfunction"],
        [case["reference"]] * len(responses),
    )
    if expected["status"] != "accept" and done and stop != len(responses) - 1:
        return Outcome(
            GAP,
            "python-snap7 has no assembler: a loop that stops at the final fragment "
            "never sees the fragment the corpus rejects",
        )
    if expected["status"] != "accept" and done and len(payload) > case["maximum_bytes"]:
        return Outcome(
            GAP,
            f"python-snap7 has no assembly byte limit (assembled {len(payload)} bytes, "
            f"corpus limit {case['maximum_bytes']})",
        )
    return verdict(expected, done, payload == expected.get("payload"), f"{payload}")


def management_continuation(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    steps = case["steps"]
    group, sub = case["group"], case["subfunction"]
    protocol = S7Protocol()
    done, payload, stop = assemble(
        protocol,
        [bytes(step["response_pdu"]) for step in steps],
        group,
        sub,
        [step["reference"] for step in steps],
    )
    if expected["status"] != "accept":
        result = verdict(expected, done, False, "")
        if result.status == AGREE and stop != expected["failed_step"]:
            result = differ(
                f"rejected at step {stop}, corpus step {expected['failed_step']}"
            )
        return result
    result = verdict(
        expected, done, payload == expected["assembled_payload"], f"{payload}"
    )
    if result.status != AGREE:
        return result
    # Follow-up requests: each is built from the previous reply's sequence number.
    for index in range(1, len(steps)):
        previous = protocol.parse_response(bytes(steps[index - 1]["response_pdu"]))
        protocol.sequence = (steps[index]["reference"] - 1) & 0xFFFF
        got = protocol.build_userdata_followup_request(
            group, sub, previous["parameters"]["sequence_number"]
        )
        want = bytes(steps[index]["request_pdu"])
        if got != want:
            return differ(
                f"follow-up {index}: python-snap7 {got.hex()} corpus {want.hex()}"
            )
    return agree()


def address_case(case: dict[str, Any]) -> Outcome:
    area = case["area"]
    word_len = {28: S7WordLen.COUNTER, 29: S7WordLen.TIMER}.get(area, S7WordLen.BYTE)
    want = bytes(case["packet"])[7:]  # strip TPKT and COTP
    try:
        got = S7Protocol().build_read_request(
            S7Area(area), 1 if area == 132 else 0, case["start_bytes"], word_len, 2
        )
    except Exception as error:
        return differ(f"builder raised {type(error).__name__}: {error}")
    if got == want:
        return agree()
    first = next(
        (i for i, (a, b) in enumerate(zip(got, want, strict=False)) if a != b), 0
    )
    return differ(
        f"differs at byte {first}: python-snap7 {got.hex()} corpus {want.hex()}"
    )


def chunk_case(case: dict[str, Any]) -> Outcome:
    from snap7.client import Client

    if case["response_overhead_bytes"] != 18:
        raise Gap("python-snap7 hard-codes an 18-byte read response overhead")
    client = Client()
    client.pdu_length = case["pdu_bytes"]
    word_len = {1: S7WordLen.BYTE, 2: S7WordLen.WORD, 4: S7WordLen.DWORD}[
        case["element_bytes"]
    ]
    try:
        most = client._read_chunk_count(word_len)
    except Exception as error:
        return differ(f"python-snap7 rejected the negotiated PDU: {error}")
    counts: list[int] = []
    starts: list[int] = []
    offset = 0
    while offset < case["count"]:
        size = min(case["count"] - offset, most)
        counts.append(size)
        starts.append(offset * client._element_address_step(word_len))
        offset += size
    if counts == case["expected_counts"] and starts == case["expected_byte_starts"]:
        return agree()
    return differ(f"chunks {counts} at {starts}, corpus {case['expected_counts']}")


def operation_string_read(case: dict[str, Any]) -> Outcome:
    expected = case["expected"]
    if expected.get("category") == "capacity-changed":
        raise Gap("capacity consistency across two reads is client state, not a codec")
    if expected.get("category") == "initial-header":
        raise Gap("the initial header check belongs to the client's first read")
    wide = case["encoding"] == "utf-16-be"
    getter = getters.get_wstring if wide else getters.get_string
    try:
        value = getter(bytearray(case["body"]), 0)
    except Exception:
        return verdict(expected, False, False, "")
    return verdict(expected, True, value == expected.get("value"), f"decoded {value!r}")


def unmapped(reason: str) -> Callable[[dict[str, Any]], Outcome]:
    """Cases of a corpus array that python-snap7 has no counterpart for."""

    def adapter(case: dict[str, Any]) -> Outcome:
        raise Gap(reason)

    adapter.__name__ = "unmapped"
    return adapter


# S7Protocol methods an adapter needs; absent in older python-snap7 versions.
REQUIRES: dict[str, tuple[str, ...]] = {
    "s7_upload": ("parse_upload_fragment",),
    "block_counts": ("parse_list_blocks_response",),
    "block_list": ("parse_list_blocks_of_type_response",),
    "block_info": ("parse_get_block_info_response",),
    "userdata_case": ("check_userdata_response",),
    "multi_item": ("build_multi_read_request", "extract_multi_read_data"),
    "clock_case": ("build_set_clock_request", "parse_get_clock_response"),
}


def missing_api(adapter: Callable[[dict[str, Any]], Outcome]) -> str | None:
    for name in REQUIRES.get(adapter.__name__, ()):
        if not hasattr(S7Protocol, name):
            return name
    return None


# --- Driver --------------------------------------------------------------------

ADAPTERS: list[tuple[str, str, Callable[[dict[str, Any]], Outcome]]] = [
    ("tpkt.json", "encode_cases", tpkt_encode),
    ("tpkt.json", "decode_cases", tpkt_decode),
    ("cotp-data.json", "encode_cases", cotp_encode),
    ("cotp-data.json", "decode_cases", cotp_decode),
    ("s7.json", "response_cases", s7_response),
    ("s7.json", "upload_cases", s7_upload),
    ("s7.json", "request_cases", s7_request),
    ("s7.json", "userdata_cases", userdata_case),
    ("s7.json", "block_count_cases", block_counts),
    ("s7.json", "block_list_cases", block_list),
    ("s7.json", "block_info_cases", block_info),
    ("s7.json", "write_cases", word_write),
    ("s7.json", "multi_item_cases", multi_item),
    ("management.json", "decoder_cases", userdata_case),
    ("values.json", "clock_codec_cases", clock_case),
    ("values.json", "integer_cases", integer_case),
    ("values.json", "string_codec_cases", string_case),
    ("s7.json", "userdata_conversation_cases", userdata_conversation),
    ("s7.json", "address_cases", address_case),
    ("s7.json", "chunk_cases", chunk_case),
    ("management.json", "continuation_cases", management_continuation),
    ("operations.json", "single_userdata_cases", userdata_case),
    ("operations.json", "string_read_cases", operation_string_read),
    (
        "operations.json",
        "write_progress_cases",
        unmapped("python-snap7 keeps no per-chunk acknowledged/uncertain write record"),
    ),
    (
        "operations.json",
        "retry_policy_cases",
        unmapped("python-snap7 has no operation-aware replay policy API"),
    ),
    (
        "conversations.json",
        "cases",
        unmapped(
            "lifecycle and retry conversations are client state, no python-snap7 API"
        ),
    ),
    (
        "sessions.json",
        "cases",
        unmapped("session-phase transitions are client state, no python-snap7 API"),
    ),
]


def run() -> dict[str, Outcome]:
    results: dict[str, Outcome] = {}
    for name, array, adapter in ADAPTERS:
        corpus = json.loads((CORPUS / name).read_text(encoding="utf-8"))
        if corpus["schema_version"] != 1:
            raise SystemExit(f"{name}: unsupported schema version")
        absent = missing_api(adapter)
        for case in corpus[array]:
            key = f"{name}/{array}/{case['id']}"
            if absent:
                results[key] = Outcome(
                    GAP, f"this python-snap7 has no S7Protocol.{absent}"
                )
                continue
            try:
                results[key] = adapter(case)
            except Gap as reason:
                results[key] = Outcome(GAP, str(reason))
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--update-baseline", action="store_true")
    parser.add_argument(
        "--no-baseline",
        action="store_true",
        help="print the results without comparing with or writing a baseline "
        "(for unreleased builds that report an already reviewed version)",
    )
    parser.add_argument(
        "--list", choices=[GAP, AMBIGUITY, DISAGREE, AGREE], action="append"
    )
    args = parser.parse_args()

    installed = importlib.metadata.version("python-snap7")
    baseline_path = Path(__file__).with_name(f"python_snap7_baseline-{installed}.json")
    if not baseline_path.exists() and not args.update_baseline and not args.no_baseline:
        raise SystemExit(
            f"no reviewed baseline for python-snap7 {installed}; review the disagreements "
            "with --list disagree and record them with --update-baseline"
        )
    results = run()
    counts = Counter(outcome.status for outcome in results.values())
    print(
        f"python-snap7 {installed}: {len(results)} cases, "
        + ", ".join(f"{k} {counts[k]}" for k in (AGREE, GAP, AMBIGUITY, DISAGREE))
    )
    for status in args.list or []:
        for key, outcome in sorted(results.items()):
            if outcome.status == status:
                print(f"  [{status}] {key}: {outcome.detail}")

    if args.no_baseline:
        return 0

    recorded = {
        key: {"status": outcome.status, "detail": outcome.detail}
        for key, outcome in sorted(results.items())
    }
    if args.update_baseline:
        baseline_path.write_text(
            json.dumps(recorded, indent=1, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        print(f"wrote {baseline_path}")
        return 0
    baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
    problems = []
    for key in sorted(set(baseline) | set(recorded)):
        before = baseline.get(key, {}).get("status")
        after = recorded.get(key, {}).get("status")
        if before != after:
            problems.append(f"{key}: baseline {before}, now {after}")
    if problems:
        print("classification differs from the reviewed baseline:", file=sys.stderr)
        for line in problems:
            print("  " + line, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
