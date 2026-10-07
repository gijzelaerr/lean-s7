"""Independently decode mixed-item and bounded USERDATA corpus conversations.

This strict byte-level oracle uses only the standard library, not the Lean
implementation or python-snap7. It is not a claim about python-snap7 behavior.
"""

from __future__ import annotations

import argparse
import json
import struct
from pathlib import Path

DEFAULT_CORPUS = Path(__file__).resolve().parents[1] / "conformance/v1/s7.json"


def sections(packet: bytes, kind: int, reference: int) -> tuple[bytes, bytes]:
    header_size = 12 if kind == 3 else 10
    if len(packet) < header_size or packet[:4] != bytes((0x32, kind, 0, 0)):
        raise ValueError("invalid S7 header")
    actual_reference, parameter_size, data_size = struct.unpack_from(">HHH", packet, 4)
    if (
        actual_reference != reference
        or len(packet) != header_size + parameter_size + data_size
    ):
        raise ValueError("reference or section length mismatch")
    if kind == 3 and packet[10:12] != b"\0\0":
        raise ValueError("global PLC error")
    return packet[header_size : header_size + parameter_size], packet[
        header_size + parameter_size :
    ]


def check_request(test: dict) -> None:
    parameters, data = sections(bytes(test["request_pdu"]), 1, test["reference"])
    function = 5 if test["operation"] == "write" else 4
    ranges = test["ranges"]
    if parameters[:2] != bytes((function, len(ranges))) or len(
        parameters
    ) != 2 + 12 * len(ranges):
        raise ValueError("bad request item count/function")
    for index, item in enumerate(ranges):
        address = parameters[2 + index * 12 : 14 + index * 12]
        expected = (
            b"\x12\x0a\x10\x02"
            + struct.pack(">HHB", item["count"], item["db_number"], 0x84)
            + (item["start"] * 8).to_bytes(3, "big")
        )
        if address != expected:
            raise ValueError("request range/address differs")
    if function == 4 and data:
        raise ValueError("read request contains data")
    if function == 5:
        offset = 0
        for index, item in enumerate(ranges):
            size = item["count"]
            if data[offset : offset + 4] != b"\0\x04" + struct.pack(">H", size * 8):
                raise ValueError("write payload header differs")
            offset += 4 + size
            if index + 1 < len(ranges) and size % 2:
                offset += 1
        if offset != len(data):
            raise ValueError("write payload extent differs")


def decode_multi(test: dict) -> dict:
    parameters, data = sections(bytes(test["response_pdu"]), 3, test["reference"])
    function = 5 if test["operation"] == "write" else 4
    ranges = test["ranges"]
    if parameters != bytes((function, len(ranges))):
        raise ValueError("response item count/function differs")
    results = []
    offset = 0
    for index, item in enumerate(ranges):
        if function == 5:
            if offset >= len(data):
                raise ValueError("missing write status")
            code = data[offset]
            offset += 1
            payload = None
        else:
            if offset + 4 > len(data):
                raise ValueError("truncated read header")
            code, transport, length = struct.unpack_from(">BBH", data, offset)
            offset += 4
            if transport == 9:
                size = length
            elif length % 8:
                raise ValueError("unaligned bit length")
            else:
                size = length // 8
            if offset + size > len(data):
                raise ValueError("truncated read payload")
            payload = list(data[offset : offset + size])
            offset += size
            if index + 1 < len(ranges) and size % 2:
                if offset >= len(data):
                    raise ValueError("missing inter-item padding")
                offset += 1
            if code == 255 and (transport != 4 or size != item["count"]):
                raise ValueError("successful read transport/length differs")
        if code == 255:
            result = {"status": "success"}
            if payload is not None:
                result["payload"] = payload
        else:
            result = {"status": "failure", "code": code}
        results.append(result)
    if offset != len(data):
        raise ValueError("trailing response bytes")
    return {"status": "accept", "items": results}


def decode_conversation(test: dict) -> dict:
    accumulated = bytearray()
    complete = False
    for count, raw in enumerate(test["response_pdus"], 1):
        if complete or count > test["maximum_fragments"]:
            raise ValueError("fragment after completion or fragment overflow")
        parameters, data = sections(bytes(raw), 7, test["reference"])
        if (
            len(parameters) != 12
            or parameters[:5] != b"\0\x01\x12\x08\x12"
            or parameters[5] != 0x80 | test["expected_group"]
            or parameters[6] != test["expected_subfunction"]
            or parameters[9] not in (0, 1)
            or parameters[10:] != b"\0\0"
        ):
            raise ValueError("invalid USERDATA parameters")
        if (
            len(data) < 4
            or data[:2] != b"\xff\x09"
            or len(data) != 4 + int.from_bytes(data[2:4], "big")
        ):
            raise ValueError("invalid USERDATA payload extent")
        more = parameters[9] == 1
        if more and count == test["maximum_fragments"]:
            raise ValueError("continuation exhausts fragment bound")
        if len(accumulated) + len(data) - 4 > test["maximum_bytes"]:
            raise ValueError("accumulated byte overflow")
        accumulated.extend(data[4:])
        complete = not more
    if not complete:
        raise ValueError("incomplete conversation")
    return {"status": "accept", "payload": list(accumulated)}


def run(corpus_path: Path = DEFAULT_CORPUS) -> None:
    corpus = json.loads(corpus_path.read_text(encoding="utf-8"))
    if corpus["schema_version"] != 1 or corpus["protocol"] != "classic S7 semantics":
        raise ValueError("unsupported corpus")
    total = 0
    for group, decode in (
        ("multi_item_cases", decode_multi),
        ("userdata_conversation_cases", decode_conversation),
    ):
        for test in corpus[group]:
            if group == "multi_item_cases":
                check_request(test)
            try:
                actual = decode(test)
            except ValueError:
                actual = {"status": "reject"}
            if actual != test["expected"]:
                raise AssertionError(f"{test['id']}: {actual} != {test['expected']}")
            total += 1
    print(f"{total}/{total} independent conversation corpus cases passed")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", nargs="?", type=Path, default=DEFAULT_CORPUS)
    run(parser.parse_args().corpus)
