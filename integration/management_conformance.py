"""Independent stdlib oracle for management codec/fragment conversations.

Fragments contain opaque codec payloads, not typed SZL/block records. This does
not model socket IO, PLC side effects, or all USER_DATA groups.
"""

from __future__ import annotations

import argparse
import json
import struct
from copy import deepcopy
from pathlib import Path

from conversation_conformance import integer, octets, shape

DEFAULT_CORPUS = Path(__file__).resolve().parents[1] / "conformance/v1/management.json"
PROTOCOL = "classic S7 management codec conversations"


def decode(pdu: bytes, reference: int, group: int, subfunction: int) -> dict:
    def reject(category: str = "protocol") -> dict:
        return {"status": "reject", "category": category}

    if len(pdu) < 10:
        return reject()
    protocol, kind, _reserved, actual_ref, parameter_size, data_size = struct.unpack(
        ">BBHHHH", pdu[:10]
    )
    if (
        protocol != 0x32
        or kind != 7
        or actual_ref != reference
        or parameter_size != 12
        or len(pdu) != 10 + parameter_size + data_size
    ):
        return reject()
    parameters = pdu[10:22]
    if (
        parameters[:5] != b"\0\x01\x12\x08\x12"
        or parameters[5] >> 4 != 8
        or parameters[5] & 15 != group
        or parameters[6] != subfunction
        or parameters[9] not in (0, 1)
    ):
        return reject()
    if int.from_bytes(parameters[10:12], "big"):
        return reject("plc-rejected")
    data = pdu[22:]
    if len(data) < 4:
        return reject()
    code, transport, length = struct.unpack(">BBH", data[:4])
    null_ack = code == 10 and (group, subfunction) in ((7, 2), (5, 1), (5, 2))
    if code != 255 and not null_ack:
        return reject("plc-rejected")
    if null_ack:
        if transport or length or parameters[9]:
            return reject()
    elif transport != 9:
        return reject()
    if len(data) != 4 + length:
        return reject()
    return {
        "status": "accept",
        "payload": list(data[4:]),
        "sequence": parameters[7],
        "data_unit_reference": parameters[8],
        "has_more_data": bool(parameters[9]),
        "return_code": code,
        "transport_size": transport,
    }


def request(
    reference: int, group: int, subfunction: int, sequence: int | None
) -> bytes:
    if sequence is None:
        parameters = bytes([0, 1, 0x12, 4, 0x11, 0x40 | group, subfunction, 0])
        data = (
            b"\xff\x09\0\x04\x04\x24\0\0" if group == 4 else b"\xff\x09\0\x02\x30\x41"
        )
    else:
        parameters = bytes(
            [0, 1, 0x12, 8, 0x12, 0x40 | group, subfunction, sequence, 0, 0, 0, 0]
        )
        data = b"\x0a\0\0\0"
    return (
        struct.pack(">BBHHHH", 0x32, 7, 0, reference, len(parameters), len(data))
        + parameters
        + data
    )


def canonical(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def validate(corpus: dict) -> tuple[int, int]:
    shape(corpus, {"schema_version", "protocol", "decoder_cases", "continuation_cases"})
    if (
        type(corpus["schema_version"]) is not int
        or corpus["schema_version"] != 1
        or corpus["protocol"] != PROTOCOL
    ):
        raise ValueError("unsupported management corpus")
    identifiers: set[str] = set()

    def identity(test: dict) -> None:
        if (
            not isinstance(test["id"], str)
            or not test["id"]
            or test["id"] in identifiers
        ):
            raise ValueError("invalid/duplicate case identity")
        identifiers.add(test["id"])

    for field in ("decoder_cases", "continuation_cases"):
        if not isinstance(corpus[field], list) or not 1 <= len(corpus[field]) <= 10000:
            raise ValueError("invalid case array")
    for test in corpus["decoder_cases"]:
        shape(test, {"id", "reference", "group", "subfunction", "pdu", "expected"})
        identity(test)
        actual = decode(
            octets(test["pdu"]),
            integer(test["reference"], 65535),
            integer(test["group"], 15),
            integer(test["subfunction"], 255),
        )
        if canonical(actual) != canonical(test["expected"]):
            raise ValueError(f"management decoder mismatch: {test['id']}")
    for test in corpus["continuation_cases"]:
        shape(test, {"id", "group", "subfunction", "steps", "expected"})
        identity(test)
        group, subfunction = (
            integer(test["group"], 15),
            integer(test["subfunction"], 255),
        )
        if (
            (group, subfunction) not in ((4, 1), (3, 2))
            or not isinstance(test["steps"], list)
            or not 1 <= len(test["steps"]) <= 256
        ):
            raise ValueError("unsupported continuation profile")
        payload = bytearray()
        unit = sequence = None
        failure = None
        for index, step in enumerate(test["steps"]):
            shape(step, {"reference", "request_pdu", "response_pdu"})
            reference = integer(step["reference"], 65535)
            # Validate even unsent request fixtures after rejection. This is
            # fixture integrity, not evidence that a real client sent them.
            if octets(step["request_pdu"]) != request(
                reference, group, subfunction, sequence
            ):
                raise ValueError("continuation request does not echo previous token")
            decoded = decode(
                octets(step["response_pdu"]), reference, group, subfunction
            )
            if failure is not None:
                continue
            if decoded["status"] == "reject":
                failure = {
                    "status": "reject",
                    "category": decoded["category"],
                    "failed_step": index,
                }
                continue
            if unit is not None and unit != decoded["data_unit_reference"]:
                failure = {
                    "status": "reject",
                    "category": "protocol",
                    "failed_step": index,
                }
                continue
            unit, sequence = decoded["data_unit_reference"], decoded["sequence"]
            payload.extend(decoded["payload"])
            if len(payload) > 16 * 1024 * 1024 or decoded["has_more_data"] != (
                index + 1 < len(test["steps"])
            ):
                raise ValueError("invalid bounded conversation completion")
        actual = failure or {"status": "accept", "assembled_payload": list(payload)}
        if canonical(actual) != canonical(test["expected"]):
            raise ValueError(f"management conversation mismatch: {test['id']}")
    return len(corpus["decoder_cases"]), len(corpus["continuation_cases"])


def self_test(corpus: dict) -> None:
    def rejected(changed: dict) -> None:
        try:
            validate(changed)
        except (ValueError, TypeError, KeyError):
            return
        raise AssertionError("management oracle accepted mutation")

    for bad in (True, 1.0, "1", 2):
        changed = deepcopy(corpus)
        changed["schema_version"] = bad
        rejected(changed)
    for index, test in enumerate(corpus["decoder_cases"]):
        changed = deepcopy(corpus)
        changed["decoder_cases"][index]["expected"]["status"] = "changed"
        rejected(changed)
        if test["expected"]["status"] == "accept":
            for position in (0, 1, 4, 7, 10, 14, 15, 16, 23):
                changed = deepcopy(corpus)
                changed["decoder_cases"][index]["pdu"][position] ^= 1
                rejected(changed)
            for field in (
                "sequence",
                "data_unit_reference",
                "return_code",
                "transport_size",
            ):
                changed = deepcopy(corpus)
                changed["decoder_cases"][index]["expected"][field] ^= 1
                rejected(changed)
            changed = deepcopy(corpus)
            changed["decoder_cases"][index]["expected"]["has_more_data"] = 0
            rejected(changed)
            changed = deepcopy(corpus)
            changed["decoder_cases"][index]["pdu"].pop()
            rejected(changed)
    for field in ("reference", "group", "subfunction"):
        for bad in (True, 1.0, "1", -1):
            changed = deepcopy(corpus)
            changed["decoder_cases"][0][field] = bad
            rejected(changed)
    for bad in (True, 1.0, -1, 256):
        changed = deepcopy(corpus)
        changed["decoder_cases"][0]["pdu"][0] = bad
        rejected(changed)
    for index, test in enumerate(corpus["continuation_cases"]):
        changed = deepcopy(corpus)
        changed["continuation_cases"][index]["expected"]["status"] = "changed"
        rejected(changed)
        for step_index in range(len(test["steps"])):
            for position in (4, 14, 17):
                changed = deepcopy(corpus)
                changed["continuation_cases"][index]["steps"][step_index][
                    "request_pdu"
                ][position] ^= 1
                rejected(changed)
        if test["expected"]["status"] == "accept":
            for field in ("data_unit_reference", "sequence", "has_more_data"):
                changed = deepcopy(corpus)
                packet = changed["continuation_cases"][index]["steps"][1][
                    "response_pdu"
                ]
                packet[
                    {"data_unit_reference": 18, "sequence": 17, "has_more_data": 19}[
                        field
                    ]
                ] ^= 1
                rejected(changed)
    changed = deepcopy(corpus)
    changed["decoder_cases"].append(deepcopy(changed["decoder_cases"][0]))
    rejected(changed)
    changed = deepcopy(corpus)
    changed["decoder_cases"][0]["unknown"] = None
    rejected(changed)
    changed = deepcopy(corpus)
    changed["continuation_cases"][0]["steps"][0]["unknown"] = None
    rejected(changed)


def run(path: Path = DEFAULT_CORPUS) -> None:
    corpus = json.loads(path.read_text(encoding="utf-8"))
    counts = validate(corpus)
    self_test(corpus)
    print(
        f"management oracle passed: {counts[0]} decoder cases / {counts[1]} continuation histories"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", nargs="?", type=Path, default=DEFAULT_CORPUS)
    run(parser.parse_args().corpus)
