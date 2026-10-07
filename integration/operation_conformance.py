"""Independent, standard-library-only oracle for portable operation regressions.

These pure guard/policy/diagnostic cases do not validate python-snap7 or network IO.
"""

from __future__ import annotations

import argparse
import json
import struct
from copy import deepcopy
from pathlib import Path

DEFAULT_CORPUS = Path(__file__).resolve().parents[1] / "conformance/v1/operations.json"


def reject(category: str) -> dict:
    return {"status": "reject", "category": category}


def decode_string(test: dict) -> dict:
    wide = test["encoding"] == "utf-16-be"
    if test["encoding"] not in ("utf-16-be", "latin-1"):
        raise ValueError("unsupported encoding")
    width = 2 if wide else 1
    header, body = bytes(test["initial_header"]), bytes(test["body"])
    if len(header) < width * 2:
        return reject("initial-header")
    maximum = int.from_bytes(header[:width], "big")
    current = int.from_bytes(header[width : width * 2], "big")
    if maximum > (16382 if wide else 254) or current > maximum:
        return reject("initial-header")
    if len(body) < width:
        return reject("body-header")
    if int.from_bytes(body[:width], "big") != maximum:
        return reject("capacity-changed")
    if len(body) < width * 2:
        return reject("value-codec")
    current = int.from_bytes(body[width : width * 2], "big")
    if current > maximum or len(body) < width * (maximum + 2):
        return reject("value-codec")
    try:
        value = body[width * 2 : width * (current + 2)].decode(test["encoding"])
    except UnicodeDecodeError:
        return reject("value-codec")
    return {"status": "accept", "value": value}


def decode_userdata(test: dict) -> dict:
    pdu = bytes(test["pdu"])
    if len(pdu) < 10 or pdu[:2] != b"\x32\x07":
        return reject("pdu-validation")
    reference, parameter_size, data_size = struct.unpack_from(">HHH", pdu, 4)
    if (
        reference != test["reference"]
        or parameter_size != 12
        or len(pdu) != 10 + parameter_size + data_size
    ):
        return reject("pdu-validation")
    parameters, data = pdu[10:22], pdu[22:]
    if (
        parameters[:5] != b"\0\x01\x12\x08\x12"
        or parameters[5] != 0x80 | test["group"]
        or parameters[6] != test["subfunction"]
        or parameters[9] not in (0, 1)
        or parameters[10:] != b"\0\0"
        or len(data) < 4
        or data[0] != 255
        or len(data) != 4 + int.from_bytes(data[2:4], "big")
    ):
        return reject("pdu-validation")
    if parameters[9]:
        return reject("incomplete-single-response")
    return {"status": "accept", "payload": list(data[4:])}


def decode_progress(test: dict) -> dict:
    attempts, pending = [], []
    for event in test["events"]:
        operation = event["operation"]
        if operation == "send":
            if pending or not event["locations"]:
                return reject("progress-transition")
            pending = deepcopy(event["locations"])
        elif operation == "acknowledge":
            results = event["results"]
            if len(results) != len(pending):
                return reject("progress-transition")
            for location, result in zip(pending, results, strict=True):
                outcome = (
                    "success"
                    if result["status"] == "success"
                    else f"failure:{result['code']}"
                )
                attempts.append({"location": location, "outcome": outcome})
            pending = []
        elif operation in ("replay", "global-reject"):
            outcome = "replayed-unknown" if operation == "replay" else "global-rejected"
            attempts.extend(
                {"location": location, "outcome": outcome} for location in pending
            )
            pending = []
        else:
            raise ValueError("unsupported progress event")
    attempts.extend(
        {"location": location, "outcome": "pending"} for location in pending
    )
    outcomes = [attempt["outcome"] for attempt in attempts]
    return {
        "status": "accept",
        "attempts": attempts,
        "acknowledged_count": sum(
            outcome == "success" or outcome.startswith("failure:")
            for outcome in outcomes
        ),
        "rejected_count": outcomes.count("global-rejected"),
        "replayed_uncertain_count": outcomes.count("replayed-unknown"),
        "uncertain_count": outcomes.count("pending"),
    }


def run(corpus_path: Path = DEFAULT_CORPUS) -> None:
    corpus = json.loads(corpus_path.read_text(encoding="utf-8"))
    if (
        corpus["schema_version"] != 1
        or corpus["protocol"] != "classic S7 operation guards and write diagnostics"
    ):
        raise ValueError("unsupported operation corpus")
    total = 0
    ids = set()
    for group, decode in (
        ("string_read_cases", decode_string),
        ("single_userdata_cases", decode_userdata),
        ("write_progress_cases", decode_progress),
    ):
        for test in corpus[group]:
            if test["id"] in ids:
                raise ValueError("duplicate case identity")
            ids.add(test["id"])
            actual = decode(test)
            if actual != test["expected"]:
                raise AssertionError(f"{test['id']}: {actual} != {test['expected']}")
            total += 1
    for test in corpus["retry_policy_cases"]:
        if test["safety"] not in ("read-only", "potentially-mutating"):
            raise ValueError("unsupported retry safety")
        actual = test["safety"] == "read-only" or test["allow_potentially_mutating"]
        if actual != test["expected_permitted"]:
            raise AssertionError(f"{test['id']}: retry policy differs")
        total += 1
    print(f"{total}/{total} independent operation corpus cases passed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", nargs="?", type=Path, default=DEFAULT_CORPUS)
    run(parser.parse_args().corpus)
