"""Run the versioned Lean TPKT corpus against python-snap7."""

from __future__ import annotations

import argparse
import json
import struct
from pathlib import Path
from typing import Any

from snap7.connection import ISOTCPConnection
from snap7.error import S7ConnectionError

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = ROOT / "conformance" / "v1" / "tpkt.json"


class BufferSocket:
    """The recv subset needed to present one finite packet to python-snap7."""

    def __init__(self, data: bytes) -> None:
        self.data = data
        self.offset = 0

    def recv(self, size: int) -> bytes:
        chunk = self.data[self.offset : self.offset + size]
        self.offset += len(chunk)
        return chunk


def materialize(spec: dict[str, Any]) -> bytes:
    result = bytearray()
    for chunk in spec["chunks"]:
        if "hex" in chunk:
            result.extend(bytes.fromhex(chunk["hex"]))
        else:
            repeated = chunk["repeat"]
            result.extend(bytes.fromhex(repeated["byte_hex"]) * repeated["count"])
    return bytes(result)


def describe_expected(expected: dict[str, Any]) -> str:
    if expected["status"] == "accept":
        return "accept"
    return f"reject ({expected['error']})"


def receive_tpkt(packet: bytes) -> bytes:
    connection = ISOTCPConnection("conformance.invalid")
    connection.connected = True
    connection.socket = BufferSocket(packet)  # type: ignore[assignment]
    # Isolate TPKT framing from the next protocol layer.
    connection._parse_cotp_data = lambda payload: payload  # type: ignore[method-assign]
    return connection.receive_data()


def run_encode_case(test: dict[str, Any]) -> str | None:
    expected = test["expected"]
    payload = materialize(test["payload"])
    connection = ISOTCPConnection("conformance.invalid")
    try:
        packet = connection._build_tpkt(payload)
    except S7ConnectionError as error:
        if expected["status"] == "reject":
            return None
        return f"expected accept, got protocol rejection: {error}"
    except (OverflowError, ValueError, struct.error) as error:
        return (
            f"expected {describe_expected(expected)}, got implementation error "
            f"{type(error).__name__}: {error}"
        )

    if expected["status"] == "reject":
        return f"expected {describe_expected(expected)}, got accept"
    expected_packet = materialize(expected["packet"])
    if packet != expected_packet:
        return f"expected {len(expected_packet)} wire bytes, got {len(packet)}"
    return None


def run_decode_case(test: dict[str, Any]) -> str | None:
    expected = test["expected"]
    packet = materialize(test["packet"])
    try:
        payload = receive_tpkt(packet)
    except S7ConnectionError as error:
        if expected["status"] == "reject":
            return None
        return f"expected accept, got protocol rejection: {error}"
    except (OverflowError, ValueError, struct.error) as error:
        return (
            f"expected {describe_expected(expected)}, got implementation error "
            f"{type(error).__name__}: {error}"
        )

    if expected["status"] == "reject":
        return f"expected {describe_expected(expected)}, got accept"
    expected_payload = materialize(expected["payload"])
    if payload != expected_payload:
        return f"expected {len(expected_payload)} payload bytes, got {len(payload)}"
    return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("corpus", nargs="?", type=Path, default=DEFAULT_CORPUS)
    args = parser.parse_args()
    corpus = json.loads(args.corpus.read_text(encoding="utf-8"))

    failures: list[str] = []
    for test in corpus["encode_cases"]:
        if failure := run_encode_case(test):
            failures.append(f"encode/{test['id']}: {failure}")
    for test in corpus["decode_cases"]:
        if failure := run_decode_case(test):
            failures.append(f"decode/{test['id']}: {failure}")

    if failures:
        print(f"python-snap7 has {len(failures)} TPKT conformance divergence(s):")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print("python-snap7 passes all TPKT conformance cases.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
