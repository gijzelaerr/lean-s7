"""Run the versioned Lean COTP data corpus against python-snap7."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from snap7.connection import ISOTCPConnection
from snap7.error import S7ConnectionError
from tpkt_conformance import materialize

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS = ROOT / "conformance" / "v1" / "cotp-data.json"


def describe_expected(expected: dict[str, Any]) -> str:
    if expected["status"] == "accept":
        return "accept"
    return f"reject ({expected['error']})"


def run_encode_case(test: dict[str, Any]) -> str | None:
    if not test["end_of_transmission"]:
        # python-snap7 exposes only complete DT construction through this helper.
        return None
    connection = ISOTCPConnection("conformance.invalid")
    payload = materialize(test["payload"])
    packet = connection._build_cotp_dt(payload)
    expected = materialize(test["expected"])
    if packet != expected:
        return f"expected {expected.hex()}, got {packet.hex()}"
    return None


def run_decode_case(test: dict[str, Any]) -> str | None:
    connection = ISOTCPConnection("conformance.invalid")
    packet = materialize(test["packet"])
    expected = test["expected"]
    try:
        payload = connection._parse_cotp_data(packet)
    except S7ConnectionError as error:
        if expected["status"] == "reject":
            return None
        return f"expected accept, got protocol rejection: {error}"

    if expected["status"] == "reject":
        return f"expected {describe_expected(expected)}, got accept"
    expected_payload = materialize(expected["payload"])
    if payload != expected_payload:
        return f"expected payload {expected_payload.hex()}, got {payload.hex()}"
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
        print(f"python-snap7 has {len(failures)} COTP conformance divergence(s):")
        for failure in failures:
            print(f"- {failure}")
        return 1

    print("python-snap7 passes all COTP data conformance cases.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
