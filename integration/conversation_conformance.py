"""Independent stdlib oracle for portable primitive conversation histories.

This checks lifecycle/replay/progress primitives and classic S7 wire exchanges,
not socket scheduling, native cancellation, PLC memory, or exactly-once writes.
"""

from __future__ import annotations

import argparse
import json
import struct
from copy import deepcopy
from pathlib import Path

DEFAULT_CORPUS = (
    Path(__file__).resolve().parents[1] / "conformance/v1/conversations.json"
)
PROTOCOL = "classic S7 primitive conversation histories"


def shape(value: dict, keys: set[str]) -> None:
    if not isinstance(value, dict) or set(value) != keys:
        raise ValueError("unsupported object shape")


def integer(value: int, maximum: int = 0xFFFFFFFF) -> int:
    if type(value) is not int or not 0 <= value <= maximum:
        raise ValueError("invalid integer range")
    return value


def octets(value: list[int]) -> bytes:
    if not isinstance(value, list) or len(value) > 65535:
        raise ValueError("invalid octet array")
    return bytes(integer(byte, 255) for byte in value)


def memory_range(value: dict) -> dict:
    shape(value, {"db_number", "start", "count"})
    integer(value["db_number"], 65535)
    integer(value["start"], 0x1FFFFF)
    integer(value["count"], 65535)
    return value


def location(value: dict) -> dict:
    shape(value, {"range", "item_index", "chunk_byte_offset"})
    memory_range(value["range"])
    if value["item_index"] is not None:
        integer(value["item_index"])
    integer(value["chunk_byte_offset"])
    return value


def address(value: dict) -> bytes:
    return (
        b"\x12\x0a\x10\x02"
        + struct.pack(">HHB", value["count"], value["db_number"], 0x84)
        + (value["start"] * 8).to_bytes(3, "big")
    )


def packet(kind: int, reference: int, parameters: bytes, data: bytes) -> bytes:
    header = struct.pack(
        ">BBHHHH", 0x32, kind, 0, reference, len(parameters), len(data)
    )
    return header + (b"\0\0" if kind == 3 else b"") + parameters + data


def payload(value: dict) -> bytes:
    return bytes(
        (value["start"] * 7 + index * 29) % 256 for index in range(value["count"])
    )


def request(reference: int, ranges: list[dict], write: bool) -> bytes | None:
    if not ranges or len(ranges) > 20:
        return None
    if any(
        item["count"] == 0
        or item["start"] + item["count"] > 0x200000
        or (write and item["count"] * 8 > 65535)
        for item in ranges
    ):
        return None
    parameters = bytes([5 if write else 4, len(ranges)]) + b"".join(
        map(address, ranges)
    )
    data = bytearray()
    if write:
        for index, item in enumerate(ranges):
            content = payload(item)
            data.extend(b"\0\x04" + struct.pack(">H", len(content) * 8) + content)
            if index + 1 < len(ranges) and len(content) % 2:
                data.append(0)
    if len(data) > 65535:
        return None
    return packet(1, reference, parameters, bytes(data))


def wire(value: list[int] | None, expected: bytes | None) -> None:
    if expected is None:
        if value is not None:
            raise ValueError("invalid request unexpectedly has wire bytes")
    elif value is None or octets(value) != expected:
        raise ValueError("wire bytes differ from independent encoder")


def accepted(**values: object) -> dict:
    return {"status": "accept", **values}


def rejected(category: str) -> dict:
    return {"status": "reject", "category": category}


def trace(events: list[dict]) -> list[dict]:
    if not isinstance(events, list) or len(events) > 1024:
        raise ValueError("invalid event array")
    state = "connected"
    history: list[dict] = []
    pending: list[dict] = []
    pending_reference = None
    result = []
    for event in events:
        if not isinstance(event, dict):
            raise TypeError("invalid event")
        operation = event.get("operation")
        outcome = accepted()
        if operation == "lifecycle":
            shape(event, {"operation", "event"})
            name = event["event"]
            if name == "disconnect":
                state = "closed"
            elif name == "transport-closed":
                if state != "closed":
                    state = "disconnected"
            elif name == "reconnected":
                if state == "disconnected":
                    state = "connected"
                else:
                    outcome = rejected("lifecycle-transition")
            else:
                raise ValueError("unknown lifecycle event")
        elif operation == "retry":
            shape(
                event,
                {
                    "operation",
                    "safety",
                    "allow_potentially_mutating",
                    "error_kind",
                    "remaining",
                },
            )
            safety, allow, kind = (
                event["safety"],
                event["allow_potentially_mutating"],
                event["error_kind"],
            )
            if (
                safety not in ("read-only", "potentially-mutating")
                or type(allow) is not bool
            ):
                raise ValueError("invalid retry policy")
            if kind not in (
                "invalid-input",
                "protocol",
                "plc-rejected",
                "timeout",
                "disconnected",
                "lifecycle",
                "transport",
                "other",
            ):
                raise ValueError("unknown error kind")
            remaining = integer(event["remaining"])
            permitted = (
                state != "closed"
                and remaining > 0
                and kind in ("timeout", "disconnected", "transport")
                and (safety == "read-only" or allow)
            )
            outcome = accepted(permitted=permitted)
            if permitted and safety == "potentially-mutating":
                history.extend(
                    {"location": deepcopy(item), "outcome": "replayed-unknown"}
                    for item in pending
                )
                pending = []
                pending_reference = None
        elif operation == "send":
            shape(event, {"operation", "reference", "locations", "request_pdu"})
            reference = integer(event["reference"], 65535)
            if not isinstance(event["locations"], list) or len(event["locations"]) > 20:
                raise ValueError("invalid locations")
            locations = [location(value) for value in event["locations"]]
            encoded = request(reference, [value["range"] for value in locations], True)
            wire(event["request_pdu"], encoded)
            if state != "connected":
                outcome = rejected("not-connected")
            elif encoded is None:
                outcome = rejected("request-codec")
            elif pending:
                outcome = rejected("write-progress")
            else:
                pending = deepcopy(locations)
                pending_reference = reference
        elif operation == "acknowledge":
            shape(event, {"operation", "reference", "count", "codes", "response_pdu"})
            reference, count = (
                integer(event["reference"], 65535),
                integer(event["count"], 255),
            )
            codes = octets(event["codes"])
            wire(event["response_pdu"], packet(3, reference, bytes([5, count]), codes))
            if state != "connected":
                outcome = rejected("not-connected")
            elif (
                (pending_reference is not None and reference != pending_reference)
                or count != len(pending)
                or len(codes) != len(pending)
            ):
                outcome = rejected("response-codec")
            else:
                history.extend(
                    {
                        "location": deepcopy(item),
                        "outcome": "success" if code == 255 else f"failure:{code}",
                    }
                    for item, code in zip(pending, codes, strict=True)
                )
                pending = []
                pending_reference = None
        elif operation == "read":
            shape(
                event,
                {
                    "operation",
                    "reference",
                    "range",
                    "payload",
                    "request_pdu",
                    "response_pdu",
                },
            )
            reference = integer(event["reference"], 65535)
            item = memory_range(event["range"])
            content = octets(event["payload"])
            wire(event["request_pdu"], request(reference, [item], False))
            if len(content) * 8 > 65535:
                raise ValueError("oversized read response")
            wire(
                event["response_pdu"],
                packet(
                    3,
                    reference,
                    b"\x04\x01",
                    b"\xff\x04" + struct.pack(">H", len(content) * 8) + content,
                ),
            )
            if state != "connected":
                outcome = rejected("not-connected")
            elif pending:
                outcome = rejected("write-pending")
            elif item["count"] == 0:
                outcome = rejected("request-codec")
            elif len(content) != item["count"]:
                outcome = rejected("response-codec")
            else:
                outcome = accepted(payload=list(content))
        else:
            raise ValueError("unknown operation")
        attempts = history + [
            {"location": deepcopy(item), "outcome": "pending"} for item in pending
        ]
        result.append(
            {
                "result": outcome,
                "snapshot": {"lifecycle": state, "attempts": deepcopy(attempts)},
            }
        )
    return result


def expectation(steps: list[dict]) -> None:
    if not isinstance(steps, list) or len(steps) > 1024:
        raise ValueError("invalid expected trace")
    for step in steps:
        shape(step, {"result", "snapshot"})
        snapshot = step["snapshot"]
        shape(snapshot, {"lifecycle", "attempts"})
        if snapshot["lifecycle"] not in ("connected", "disconnected", "closed"):
            raise ValueError("invalid expected lifecycle")
        if (
            not isinstance(snapshot["attempts"], list)
            or len(snapshot["attempts"]) > 20480
        ):
            raise ValueError("invalid expected attempts")
        for attempt in snapshot["attempts"]:
            shape(attempt, {"location", "outcome"})
            location(attempt["location"])
            outcome = attempt["outcome"]
            if outcome not in (
                "pending",
                "replayed-unknown",
                "global-rejected",
                "success",
            ):
                if not isinstance(outcome, str) or not outcome.startswith("failure:"):
                    raise ValueError("invalid expected outcome")
                code = outcome.removeprefix("failure:")
                if (
                    not code.isascii()
                    or not code.isdigit()
                    or code != str(integer(int(code), 255))
                ):
                    raise ValueError("invalid expected failure code")
        result = step["result"]
        if not isinstance(result, dict):
            raise TypeError("invalid expected result")
        if result.get("status") == "reject":
            shape(result, {"status", "category"})
            if not isinstance(result["category"], str):
                raise TypeError("invalid expected category")
        elif result.get("status") == "accept":
            if "permitted" in result:
                shape(result, {"status", "permitted"})
                if type(result["permitted"]) is not bool:
                    raise TypeError("expected permission must be Boolean")
            elif "payload" in result:
                shape(result, {"status", "payload"})
                octets(result["payload"])
            else:
                shape(result, {"status"})
        else:
            raise ValueError("invalid expected status")


def validate(corpus: dict) -> int:
    shape(corpus, {"schema_version", "protocol", "cases"})
    if (
        type(corpus["schema_version"]) is not int
        or corpus["schema_version"] != 1
        or corpus["protocol"] != PROTOCOL
    ):
        raise ValueError("unsupported corpus version/protocol")
    if not isinstance(corpus["cases"], list) or not 1 <= len(corpus["cases"]) <= 4096:
        raise ValueError("invalid cases")
    identities = set()
    total = 0
    for test in corpus["cases"]:
        shape(test, {"id", "seed", "events", "expected_trace"})
        if (
            not isinstance(test["id"], str)
            or not test["id"]
            or test["id"] in identities
        ):
            raise ValueError("invalid/duplicate case identity")
        identities.add(test["id"])
        integer(test["seed"])
        expectation(test["expected_trace"])
        actual = trace(test["events"])
        if actual != test["expected_trace"]:
            raise AssertionError(
                f"{test['id']}: independent conversation trace differs"
            )
        total += len(actual)
    return total


def self_test(corpus: dict) -> None:
    def must_reject(changed: dict) -> None:
        try:
            validate(changed)
        except (ValueError, AssertionError, TypeError):
            return
        raise AssertionError("conversation oracle accepted invalid/mutated corpus")

    for version in (True, 1.0, "1", 2):
        changed = deepcopy(corpus)
        changed["schema_version"] = version
        must_reject(changed)
    changed = deepcopy(corpus)
    changed["cases"].append(deepcopy(changed["cases"][0]))
    must_reject(changed)
    for key in ("snapshot", "result"):
        changed = deepcopy(corpus)
        changed["cases"][0]["expected_trace"][0][key] = {}
        must_reject(changed)
    changed = deepcopy(corpus)
    target = next(
        step
        for test in changed["cases"]
        for step in test["expected_trace"]
        if "permitted" in step["result"]
    )
    target["result"]["permitted"] = int(target["result"]["permitted"])
    must_reject(changed)
    for field in ("request_pdu", "response_pdu"):
        changed = deepcopy(corpus)
        target = next(
            event
            for test in changed["cases"]
            for event in test["events"]
            if event.get(field)
        )
        target[field][-1] ^= 1
        must_reject(changed)
    for field, bad in (
        ("remaining", True),
        ("allow_potentially_mutating", 1),
        ("safety", "unknown"),
        ("error_kind", "unknown"),
    ):
        changed = deepcopy(corpus)
        target = next(
            event
            for event in changed["cases"][0]["events"]
            if event["operation"] == "retry"
        )
        target[field] = bad
        must_reject(changed)
    # Independent controls prevent exported expectations defining semantics.
    send = next(
        event
        for test in corpus["cases"]
        for event in test["events"]
        if event["operation"] == "send" and len(event["locations"]) == 2
    )
    failure = {
        "operation": "retry",
        "safety": "potentially-mutating",
        "allow_potentially_mutating": False,
        "error_kind": "timeout",
        "remaining": 1,
    }
    control = trace(
        [send, {"operation": "lifecycle", "event": "transport-closed"}, failure]
    )[-1]
    if control["result"] != accepted(permitted=False) or [
        item["outcome"] for item in control["snapshot"]["attempts"]
    ] != ["pending", "pending"]:
        raise AssertionError("conservative write uncertainty control differs")
    failure["allow_potentially_mutating"] = True
    control = trace([send, failure])[-1]
    if [item["outcome"] for item in control["snapshot"]["attempts"]] != [
        "replayed-unknown",
        "replayed-unknown",
    ]:
        raise AssertionError("opt-in replay erased uncertainty")
    control = trace(
        [
            {"operation": "lifecycle", "event": "disconnect"},
            {"operation": "lifecycle", "event": "reconnected"},
        ]
    )[-1]
    if (
        control["result"] != rejected("lifecycle-transition")
        or control["snapshot"]["lifecycle"] != "closed"
    ):
        raise AssertionError("closed state resurrected")


def run(path: Path = DEFAULT_CORPUS) -> None:
    corpus = json.loads(path.read_text(encoding="utf-8"))
    steps = validate(corpus)
    self_test(corpus)
    print(
        f"{len(corpus['cases'])}/{len(corpus['cases'])} independent conversation cases passed ({steps} steps)"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", nargs="?", type=Path, default=DEFAULT_CORPUS)
    run(parser.parse_args().corpus)
