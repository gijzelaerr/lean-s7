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
``integration/python_snap7_baseline.json``. The run fails when any case's status
differs from the baseline, so a python-snap7 fix, a regression or a corpus change
is noticed. ``--update-baseline`` rewrites it after review. Pinned dependency:
python-snap7 3.0.0. No sockets or controllers are used.

    python integration/python_snap7_consumer.py [--update-baseline] [--list STATUS]
"""

from __future__ import annotations

import argparse
import json
import struct
import sys
from collections import Counter
from collections.abc import Callable
from pathlib import Path
from typing import Any

import snap7
from snap7.connection import ISOTCPConnection
from snap7.s7protocol import S7Protocol
from snap7.util import getters, setters

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "conformance" / "v1"
BASELINE = Path(__file__).with_name("python_snap7_baseline.json")
PINNED_VERSION = "3.0.0"

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
                protocol.extract_read_data(parsed, 0, case["requested_bytes"])
            )  # type: ignore[arg-type]
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
        payload = protocol.parse_upload_response(parsed)
    except Exception:
        return verdict(expected, False, False, "")
    if expected["status"] == "accept":
        # The continuation flag is parsed by python-snap7 only as a raw parameter.
        return verdict(
            expected,
            True,
            payload == bytes(expected["payload"]),
            "fragment payload differs",
        )
    return verdict(expected, True, False, "")


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


# --- Driver --------------------------------------------------------------------

ADAPTERS: list[tuple[str, str, Callable[[dict[str, Any]], Outcome]]] = [
    ("tpkt.json", "encode_cases", tpkt_encode),
    ("tpkt.json", "decode_cases", tpkt_decode),
    ("cotp-data.json", "encode_cases", cotp_encode),
    ("cotp-data.json", "decode_cases", cotp_decode),
    ("s7.json", "response_cases", s7_response),
    ("s7.json", "upload_cases", s7_upload),
    ("values.json", "integer_cases", integer_case),
    ("values.json", "string_codec_cases", string_case),
]


def run() -> dict[str, Outcome]:
    results: dict[str, Outcome] = {}
    for name, array, adapter in ADAPTERS:
        corpus = json.loads((CORPUS / name).read_text(encoding="utf-8"))
        if corpus["schema_version"] != 1:
            raise SystemExit(f"{name}: unsupported schema version")
        for case in corpus[array]:
            key = f"{name}/{array}/{case['id']}"
            try:
                results[key] = adapter(case)
            except Gap as reason:
                results[key] = Outcome(GAP, str(reason))
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--update-baseline", action="store_true")
    parser.add_argument(
        "--list", choices=[GAP, AMBIGUITY, DISAGREE, AGREE], action="append"
    )
    args = parser.parse_args()

    installed = getattr(snap7, "__version__", PINNED_VERSION)
    if installed != PINNED_VERSION:
        print(
            f"warning: tested with python-snap7 {PINNED_VERSION}, found {installed}",
            file=sys.stderr,
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

    recorded = {
        key: {"status": outcome.status, "detail": outcome.detail}
        for key, outcome in sorted(results.items())
    }
    if args.update_baseline:
        BASELINE.write_text(
            json.dumps(recorded, indent=1, ensure_ascii=False) + "\n", encoding="utf-8"
        )
        print(f"wrote {BASELINE}")
        return 0
    baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
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
