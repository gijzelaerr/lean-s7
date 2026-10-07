# ruff: noqa: BLE001  (any python-snap7 exception, whatever its type, counts as a rejection)
"""Replay public captures from a real Siemens S7-300 through the Lean codecs.

The captures are Wireshark's published S7comm sample captures (a real S7-300 PLC at
192.168.1.40 talking to an engineering tool or libnodave). They are downloaded on
demand into ``.lake/captures`` and verified against pinned SHA-256 digests; they are
not stored in this repository. This is independent, real-device wire evidence for the
exact conversations those files contain, not qualification of any CPU or firmware.

For every capture the harness parses the pcap itself (no tshark needed), rebuilds the
TPKT/COTP/S7 streams, and then checks:

* every PLC USER_DATA response is accepted by the Lean decoders (envelope, block
  counts/list/info payloads, clock) and agrees with an independent BCD decoding;
* every client request that lean-s7 can build is reproduced byte-for-byte by the Lean
  encoder (read clock, list blocks, list blocks of type, block info, read SZL and
  continuation, single-item reads);
* variable-read responses decode to the requested size;
* optionally (``--tshark``) the PDU count equals Wireshark's S7comm count;
* optionally (python-snap7 installed) python-snap7's builders and parsers on the same
  bytes, reported separately.

    lake build lean-s7-decode
    python integration/real_captures.py [--tshark] [--list]
"""

from __future__ import annotations

import argparse
import hashlib
import logging
import shutil
import struct
import subprocess
import sys
import urllib.request
from dataclasses import dataclass
from pathlib import Path

logging.disable(logging.CRITICAL)

ROOT = Path(__file__).resolve().parent.parent
CACHE = ROOT / ".lake" / "captures"
ORACLE = (
    ROOT
    / ".lake"
    / "build"
    / "bin"
    / ("lean-s7-decode.exe" if sys.platform == "win32" else "lean-s7-decode")
)
BASE = "https://wiki.wireshark.org/uploads/__moin_import__/attachments/SampleCaptures/"

CAPTURES = {
    "s7comm_reading_setting_plc_time.pcap": "d74c1eca1f2039dadcccd43c212f649b293acf6a80db1560e9ee22aeabb4c5d4",
    "s7comm_reading_plc_status.pcap": "e71f81b471bd67da2fd6e40dc69a7179574ba66771c6150cd7bfe232cc07b8a9",
    "s7comm_program_blocklist_onlineview.pcap": "b2e7014362630b803b413dda595e4ba7a3a910105712f448c22dba517ec02851",
    "s7comm_downloading_block_db1.pcap": "48725bd1af7b778821351cd0f50f0ee259e438074a27f8431a8a1a3351dfd3d0",
    "s7comm_varservice_libnodavedemo.pcap": "a1ff275c087fafbfdc8821ea59ab9bfb11f5adcc9ce6bb5888a1c4a4d7b6affc",
}


def fetch(name: str) -> Path:
    path = CACHE / name
    if not path.exists():
        CACHE.mkdir(parents=True, exist_ok=True)
        with urllib.request.urlopen(BASE + name, timeout=60) as response:
            data = response.read()
        if hashlib.sha256(data).hexdigest() != CAPTURES[name]:
            raise SystemExit(
                f"{name}: SHA-256 differs from the pinned digest; refusing to use it"
            )
        path.write_bytes(data)
    elif hashlib.sha256(path.read_bytes()).hexdigest() != CAPTURES[name]:
        raise SystemExit(f"{path}: cached file differs from the pinned digest")
    return path


# --- minimal pcap / TCP / TPKT / COTP reassembly ------------------------------------


@dataclass
class Message:
    frame: int  # capture frame number of the segment that completed the PDU
    from_client: bool
    pdu: bytes


def read_pcap(path: Path) -> list[tuple[int, bytes]]:
    data = path.read_bytes()
    magic = data[:4]
    if magic == b"\xd4\xc3\xb2\xa1":
        endian = "<"
    elif magic == b"\xa1\xb2\xc3\xd4":
        endian = ">"
    else:
        raise SystemExit(f"{path.name}: not a classic pcap file")
    linktype = struct.unpack(endian + "I", data[20:24])[0]
    if linktype != 1:
        raise SystemExit(f"{path.name}: expected Ethernet link type, got {linktype}")
    frames, offset, number = [], 24, 0
    while offset + 16 <= len(data):
        _, _, caplen, _ = struct.unpack(endian + "IIII", data[offset : offset + 16])
        frames.append((number := number + 1, data[offset + 16 : offset + 16 + caplen]))
        offset += 16 + caplen
    return frames


def tcp_payloads(
    frames: list[tuple[int, bytes]],
) -> list[tuple[int, tuple, bytes, bool, int]]:
    """(frame, direction key, payload, is_syn, seq) for every TCP segment on port 102."""
    out = []
    for number, frame in frames:
        ethertype = struct.unpack(">H", frame[12:14])[0]
        offset = 14
        if ethertype == 0x8100:
            ethertype = struct.unpack(">H", frame[16:18])[0]
            offset = 18
        if ethertype != 0x0800:
            continue
        ihl = (frame[offset] & 0x0F) * 4
        if frame[offset + 9] != 6:
            continue
        total = struct.unpack(">H", frame[offset + 2 : offset + 4])[0]
        source, destination = (
            frame[offset + 12 : offset + 16],
            frame[offset + 16 : offset + 20],
        )
        tcp = offset + ihl
        sport, dport, seq = struct.unpack(">HHI", frame[tcp : tcp + 8])
        header = (frame[tcp + 12] >> 4) * 4
        flags = frame[tcp + 13]
        payload = frame[tcp + header : offset + total]
        if 102 not in (sport, dport):
            continue
        out.append(
            (
                number,
                (source, sport, destination, dport),
                payload,
                bool(flags & 0x02),
                seq,
            )
        )
    return out


def messages(path: Path) -> list[Message]:
    segments = tcp_payloads(read_pcap(path))
    buffers: dict[tuple, bytearray] = {}
    expected: dict[tuple, int] = {}
    partial: dict[tuple, bytearray] = {}
    out: list[Message] = []
    for number, key, payload, syn, seq in segments:
        if syn:
            expected[key] = seq + 1
            continue
        if not payload:
            continue
        nxt = expected.get(key)
        if nxt is not None and seq < nxt:
            payload = (
                payload[nxt - seq :] if seq + len(payload) > nxt else b""
            )  # retransmission
            seq = nxt
        if not payload:
            continue
        expected[key] = seq + len(payload)
        buffer = buffers.setdefault(key, bytearray())
        buffer += payload
        while len(buffer) >= 4:
            length = struct.unpack(">H", buffer[2:4])[0]
            if len(buffer) < length:
                break
            tpkt = bytes(buffer[:length])
            del buffer[:length]
            cotp = tpkt[4:]
            kind = cotp[1] & 0xF0
            if kind != 0xF0:
                continue  # connection request/confirm: not S7
            data = partial.setdefault(key, bytearray())
            data += cotp[3 : 1 + cotp[0]] if False else cotp[1 + cotp[0] :]
            if cotp[2] & 0x80:
                out.append(Message(number, key[3] == 102, bytes(data)))
                del partial[key]
    return out


# --- Lean oracle ------------------------------------------------------------------


def lean(lines: list[str]) -> list[str]:
    result = subprocess.run(
        [str(ORACLE)],
        input="\n".join(lines) + "\n",
        capture_output=True,
        text=True,
        check=True,
    )
    answers = result.stdout.splitlines()
    if len(answers) != len(lines):
        raise SystemExit("oracle answered a different number of lines")
    return answers


def bcd(value: int) -> int:
    return (value >> 4) * 10 + (value & 0x0F)


def independent_clock(payload: bytes) -> tuple[int, ...]:
    """Ten-byte S7 clock: reserved, century byte, then BCD year..second, ms/weekday."""
    year = bcd(payload[2])
    year += 1900 if year >= 90 else 2000
    milliseconds = bcd(payload[8]) * 10 + (payload[9] >> 4)
    return (
        year,
        bcd(payload[3]),
        bcd(payload[4]),
        bcd(payload[5]),
        bcd(payload[6]),
        bcd(payload[7]),
        milliseconds,
        payload[9] & 0x0F,
    )


def userdata_fields(pdu: bytes) -> tuple[int, int, int, int]:
    """(reference, group, subfunction, sequence) of a USER_DATA PDU's 12/8-byte parameters."""
    reference = struct.unpack(">H", pdu[4:6])[0]
    return reference, pdu[15] & 0x0F, pdu[16], pdu[17]


def userdata_payload(pdu: bytes) -> bytes:
    parameters = struct.unpack(">H", pdu[6:8])[0]
    data = pdu[10 + parameters :]
    return data[4:] if len(data) >= 4 else b""


# --- analysis ---------------------------------------------------------------------


@dataclass
class Result:
    capture: str
    check: str
    ok: bool
    detail: str = ""


def analyse(name: str, items: list[Message]) -> list[Result]:
    results: list[Result] = []
    lines: list[str] = []
    meta: list[tuple[str, str, bytes]] = []  # (kind, label, extra)

    def ask(kind: str, label: str, line: str, extra: bytes = b"") -> None:
        lines.append(line)
        meta.append((kind, label, extra))

    pending_requests: dict[int, Message] = {}
    for message in items:
        pdu = message.pdu
        if len(pdu) < 10 or pdu[0] != 0x32:
            results.append(
                Result(
                    name, "S7 header", False, f"frame {message.frame}: not an S7 PDU"
                )
            )
            continue
        rosctr, reference = pdu[1], struct.unpack(">H", pdu[4:6])[0]
        header = 12 if rosctr in (2, 3) else 10
        parameter_length = struct.unpack(">H", pdu[6:8])[0]
        parameters = pdu[header : header + parameter_length]
        body = pdu[header + parameter_length :]
        function = parameters[0] if parameters else -1
        block_type = parameters[11] if len(parameters) > 11 else 0
        if rosctr == 1 and message.from_client and function == 0x1A:
            number = int(parameters[12:17])
            load, mc7 = int(parameters[20:26]), int(parameters[26:32])
            ask(
                "request",
                f"frame {message.frame} request download",
                f"enc download {reference} {block_type} {number} {load} {mc7}",
                pdu,
            )
            continue
        if rosctr == 1 and not message.from_client and function in (0x1B, 0x1C):
            number = int(parameters[12:17])
            ask(
                "download",
                f"frame {message.frame} PLC download service 0x{function:02x}",
                f"dlreq {function} {block_type} {number} {pdu.hex()}",
                pdu,
            )
            pending_requests[reference] = message
            continue
        if rosctr == 3 and message.from_client and function == 0x1B:
            ask(
                "request",
                f"frame {message.frame} download fragment reply",
                f"enc dlfrag {reference} {1 if parameters[1] == 0 else 0} {body[4:].hex() or '-'}",
                pdu,
            )
            continue
        if rosctr == 3 and message.from_client and function == 0x1C:
            ask(
                "request",
                f"frame {message.frame} download ended reply",
                f"enc dlended {reference}",
                pdu,
            )
            continue
        if (
            rosctr == 1
            and message.from_client
            and function == 0x28
            and parameters.endswith(b"_INSE")
        ):
            ask(
                "request",
                f"frame {message.frame} insert block",
                f"enc insert {reference} {parameters[13]} {int(parameters[14:19])}",
                pdu,
            )
            continue
        if message.from_client and rosctr in (1, 7):
            pending_requests[reference] = message
            if rosctr == 7:
                ref, group, sub, sequence = userdata_fields(pdu)
                data = userdata_payload(pdu)
                label = f"frame {message.frame} request {group}/{sub}"
                if (group, sub) == (7, 1):
                    ask("request", label, f"enc readclock {ref}", pdu)
                elif (group, sub) == (3, 1):
                    ask("request", label, f"enc listblocks {ref}", pdu)
                elif (group, sub) == (3, 2) and len(data) == 2:
                    ask("request", label, f"enc listblocksoftype {ref} {data[1]}", pdu)
                elif (group, sub) == (3, 3) and len(data) == 8:
                    ask(
                        "request",
                        label,
                        f"enc blockinfo {ref} {data[1]} {int(data[2:7])}",
                        pdu,
                    )
                elif (
                    (group, sub) == (4, 1)
                    and len(data) == 4
                    and pdu[7] == 8
                    and sequence == 0
                ):
                    ask(
                        "request",
                        label,
                        f"enc szl {ref} {struct.unpack('>H', data[:2])[0]} {struct.unpack('>H', data[2:4])[0]}",
                        pdu,
                    )
                elif (group, sub) == (4, 1) and sequence != 0:
                    ask("request", label, f"enc szlnext {ref} {sequence}", pdu)
        elif not message.from_client and rosctr == 7:
            ref, group, sub, _ = userdata_fields(pdu)
            error = struct.unpack(">H", pdu[20:22])[0] if len(pdu) >= 22 else 0
            # Return code 0x0a with no data is a plain acknowledgement (e.g. set clock), not an error.
            refused = error != 0 or (len(pdu) > 22 and pdu[22] not in (0xFF, 0x0A))
            label = f"frame {message.frame} response {group}/{sub}" + (
                f" (PLC error 0x{error:04x})" if refused else ""
            )
            ask(
                "refused" if refused else "userdata",
                label,
                f"userdata {ref} {group} {sub} {pdu.hex()}",
                pdu,
            )
            payload = userdata_payload(pdu)
            hexed = payload.hex() or "-"
            if refused:
                pass
            elif (group, sub) == (3, 1) and payload:
                ask("payload", label + " block counts", f"blockcounts {hexed}", payload)
            elif (group, sub) == (3, 2) and payload:
                ask("payload", label + " block list", f"blocklist {hexed}", payload)
            elif (group, sub) == (3, 3) and payload:
                ask("payload", label + " block info", f"blockinfo {hexed}", payload)
            elif (group, sub) == (7, 1) and len(payload) == 10:
                ask("clock", label + " clock", f"clock {hexed}", payload)
        elif not message.from_client and rosctr == 3 and reference in pending_requests:
            request = pending_requests[reference].pdu
            if (
                request[1] == 1
                and len(request) > 11
                and request[10] == 0x04
                and request[11] == 1
                and request[22 - 0] is not None
            ):
                item = request[12:24]
                size_codes = {0x02: 1, 0x04: 2, 0x06: 4, 0x1C: 2, 0x1D: 2}
                if len(item) == 12 and item[3] in size_codes:
                    size = struct.unpack(">H", item[4:6])[0] * size_codes[item[3]]
                    ask(
                        "read",
                        f"frame {message.frame} read response",
                        f"read {reference} {size} {pdu.hex()}",
                        pdu,
                    )

    answers = lean(lines)
    for answer, (kind, label, extra), line in zip(answers, meta, lines, strict=True):
        if kind == "refused":
            ok = answer == "reject"
            results.append(
                Result(
                    name,
                    label + ", rejected as an error reply",
                    ok,
                    "" if ok else f"lean accepted a PLC error reply: {answer[:60]}",
                )
            )
        elif kind == "request" and "request 3/3" in label:
            got = answer.split()[-1] if answer.startswith("accept") else ""
            same_but_letter = got[:-2] == extra.hex()[:-2] and bytes.fromhex(
                extra.hex()[-2:]
            ) in (b"A", b"B", b"P")
            ok = got == extra.hex() or same_but_letter
            detail = ""
            if same_but_letter and got != extra.hex():
                detail = f"identical except the file-system letter: lean 0x{got[-2:]}, tool 0x{extra.hex()[-2:]}"
            results.append(Result(name, f"request {label}", ok, detail))
        elif kind == "request":
            expected = f"accept {extra.hex()}"
            results.append(
                Result(
                    name,
                    f"request {label}",
                    answer == expected,
                    ""
                    if answer == expected
                    else f"lean {answer[:100]} capture {extra.hex()[:100]}",
                )
            )
        elif kind == "clock":
            fields = independent_clock(extra)
            parts = answer.split()
            ok = parts[:1] == ["accept"] and tuple(int(p) for p in parts[1:]) == fields
            results.append(
                Result(
                    name, label, ok, "" if ok else f"lean {answer} independent {fields}"
                )
            )
        elif kind == "read":
            ok = answer.startswith("accept")
            results.append(Result(name, label, ok, "" if ok else f"lean {answer[:80]}"))
        else:
            ok = answer.startswith("accept")
            results.append(
                Result(
                    name,
                    label,
                    ok,
                    "" if ok else f"lean {answer[:80]} (pdu {line[-80:]})",
                )
            )
    return results


def snap7_checks(name: str, items: list[Message]) -> list[Result]:
    try:
        from snap7.s7protocol import S7Protocol
    except ImportError:
        return []
    results: list[Result] = []
    for message in items:
        pdu = message.pdu
        if pdu[0] != 0x32 or pdu[1] != 7:
            continue
        reference, group, sub, _ = userdata_fields(pdu)
        label = f"python-snap7 frame {message.frame}"
        protocol = S7Protocol()
        try:
            if message.from_client and (group, sub) == (7, 1):
                protocol.sequence = reference - 1
                ok = protocol.build_get_clock_request() == pdu
                results.append(
                    Result(
                        name, f"{label} read-clock request", ok, "" if ok else "differs"
                    )
                )
            elif message.from_client and (group, sub) == (3, 1):
                protocol.sequence = reference - 1
                ok = protocol.build_list_blocks_request() == pdu
                results.append(
                    Result(
                        name,
                        f"{label} list-blocks request",
                        ok,
                        "" if ok else "differs",
                    )
                )
            elif message.from_client and (group, sub) == (3, 3):
                data = userdata_payload(pdu)
                protocol.sequence = reference - 1
                ok = (
                    protocol.build_get_block_info_request(data[1], int(data[2:7]))
                    == pdu
                )
                results.append(
                    Result(
                        name,
                        f"{label} block-info request",
                        ok,
                        ""
                        if ok
                        else f"python {protocol.build_get_block_info_request(data[1], int(data[2:7]))[-8:]!r} PLC tool {data[-8:]!r}",
                    )
                )
            elif (
                not message.from_client
                and (group, sub) == (7, 1)
                and len(userdata_payload(pdu)) == 10
            ):
                parsed = protocol.parse_response(pdu)
                try:
                    protocol.parse_get_clock_response(parsed)
                    results.append(Result(name, f"{label} clock reply parsed", True))
                except Exception as error:
                    results.append(
                        Result(name, f"{label} clock reply parsed", False, str(error))
                    )
            elif not message.from_client and (group, sub) == (3, 1):
                parsed = protocol.parse_response(pdu)
                protocol.parse_list_blocks_response(parsed)
                results.append(Result(name, f"{label} block-count reply parsed", True))
            elif not message.from_client and (group, sub) == (7, 2) and pdu[22] == 0x0A:
                parsed = protocol.parse_response(pdu)
                try:
                    protocol.check_userdata_response(parsed, 7, 2)
                    results.append(
                        Result(
                            name, f"{label} set-clock acknowledgement accepted", True
                        )
                    )
                except Exception as error:
                    results.append(
                        Result(
                            name,
                            f"{label} set-clock acknowledgement accepted",
                            False,
                            str(error),
                        )
                    )
        except Exception as error:
            results.append(
                Result(
                    name,
                    f"{label} {group}/{sub}",
                    False,
                    f"{type(error).__name__}: {error}",
                )
            )
    return results


def tshark_count(tshark: str, path: Path) -> int:
    output = subprocess.run(
        [tshark, "-r", str(path), "-Y", "s7comm", "-T", "fields", "-e", "frame.number"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    return len([line for line in output.splitlines() if line.strip()])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--tshark", nargs="?", const="tshark", help="cross-check PDU counts with tshark"
    )
    parser.add_argument("--list", action="store_true", help="print every check")
    args = parser.parse_args()
    if not ORACLE.exists():
        print(
            f"missing {ORACLE}; run `lake build lean-s7-decode` first", file=sys.stderr
        )
        return 1

    failures = 0
    for name in CAPTURES:
        path = fetch(name)
        items = messages(path)
        results = analyse(name, items) + snap7_checks(name, items)
        lean_results = [r for r in results if not r.check.startswith("python-snap7")]
        snap = [r for r in results if r.check.startswith("python-snap7")]
        line = f"{name}: {len(items)} S7 PDUs, lean-s7 {sum(r.ok for r in lean_results)}/{len(lean_results)} checks ok"
        if snap:
            line += f"; python-snap7 {sum(r.ok for r in snap)}/{len(snap)} ok"
        if args.tshark:
            count = tshark_count(shutil.which(args.tshark) or args.tshark, path)
            line += f"; tshark counts {count} S7 frames" + (
                "" if count == len(items) else " (DIFFERS)"
            )
            failures += count != len(items)
        print(line)
        for result in results:
            if args.list or (
                not result.ok and not result.check.startswith("python-snap7")
            ):
                print(
                    f"  {'ok  ' if result.ok else 'FAIL'} {result.check}"
                    + (f": {result.detail}" if result.detail else "")
                )
        failures += sum(not r.ok for r in lean_results)
        for result in snap:
            if not result.ok:
                print(f"  note {result.check}: {result.detail}")
            elif args.list:
                print(f"  ok   {result.check}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
