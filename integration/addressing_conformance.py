"""Check generated address vectors with the installed Wireshark dissector.

Synthetic packets only: no network sockets or controller access.
"""

from __future__ import annotations

import argparse
import json
import struct
import subprocess
import tempfile
from pathlib import Path

DEFAULT_CORPUS = Path(__file__).resolve().parents[1] / "conformance/v1/s7.json"


def capture(packets: list[bytes]) -> bytes:
    result = bytearray(struct.pack("<IHHIIII", 0xA1B2C3D4, 2, 4, 0, 0, 65535, 1))
    for index, payload in enumerate(packets):
        # Ethernet/IPv4/TCP envelope. Checksums are unused for offline dissection.
        ethernet = bytes(12) + b"\x08\x00"
        ip = struct.pack(
            ">BBHHHBBH4s4s",
            0x45,
            0,
            40 + len(payload),
            index,
            0,
            64,
            6,
            0,
            b"\x7f\x00\x00\x01",
            b"\x7f\x00\x00\x02",
        )
        tcp = struct.pack(
            ">HHIIBBHHH", 40000 + index, 102, 1, 1, 0x50, 0x18, 65535, 0, 0
        )
        frame = ethernet + ip + tcp + payload
        result.extend(struct.pack("<IIII", index, 0, len(frame), len(frame)))
        result.extend(frame)
    return bytes(result)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", nargs="?", type=Path, default=DEFAULT_CORPUS)
    parser.add_argument("--tshark", default="tshark")
    args = parser.parse_args()
    corpus = json.loads(args.corpus.read_text())
    if corpus["schema_version"] != 1:
        raise ValueError("unsupported corpus schema")
    cases = corpus["address_cases"]
    if not cases:
        raise ValueError("empty address corpus")
    version = subprocess.run(
        [args.tshark, "--version"], check=True, capture_output=True, text=True
    ).stdout.splitlines()[0]
    print(version)
    with tempfile.TemporaryDirectory(prefix="lean-s7-addresses-") as directory:
        path = Path(directory) / "addresses.pcap"
        path.write_bytes(capture([bytes(case["packet"]) for case in cases]))
        output = subprocess.run(
            [
                args.tshark,
                "-r",
                str(path),
                "-T",
                "fields",
                "-e",
                "frame.number",
                "-e",
                "s7comm.param.item.area",
                "-e",
                "s7comm.param.item.address",
                "-e",
                "s7comm.param.item.address.number",
                "-e",
                "s7comm.param.item.address.byte",
            ],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.splitlines()
    if len(output) != len(cases):
        raise AssertionError("Wireshark did not return one row per packet")
    for index, (test, row) in enumerate(zip(cases, output, strict=True), start=1):
        frame, area, address, number, byte = row.split("\t")
        if int(frame) != index or int(area, 0) != test["area"]:
            raise AssertionError(f"{test['id']}: frame/area differs: {row}")
        if int(address, 0) != test["wire_address"]:
            raise AssertionError(f"{test['id']}: raw address differs: {row}")
        if test["area"] in (0x1C, 0x1D):
            if byte or int(number, 0) != test["wire_address"]:
                raise AssertionError(
                    f"{test['id']}: counter/timer interpretation differs: {row}"
                )
        elif number or int(byte, 0) != test["start_bytes"]:
            raise AssertionError(f"{test['id']}: byte interpretation differs: {row}")
        print(
            f"PASS {test['id']}: wire={address}, number={number or '-'}, byte={byte or '-'}"
        )
    print(f"{len(cases)} address vectors passed independent Wireshark dissection")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
