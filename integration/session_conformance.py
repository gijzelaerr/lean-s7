"""Independent active-request/reconnect operational-contract oracle.

Not an equivalence proof of live IO, cancellation, scheduler behavior, or PLC
side effects. References and responses use actual classic S7 wire structures.
"""

from __future__ import annotations

import argparse
import json
import struct
from copy import deepcopy
from pathlib import Path

from conversation_conformance import (
    accepted,
    integer,
    location,
    octets,
    packet,
    payload,
    rejected,
    request,
    shape,
    wire,
)

DEFAULT_CORPUS = Path(__file__).resolve().parents[1] / "conformance/v1/sessions.json"
PROTOCOL = "classic S7 active request histories"
KINDS = {
    "invalid-input",
    "protocol",
    "plc-rejected",
    "timeout",
    "disconnected",
    "lifecycle",
    "transport",
    "other",
}


def configuration(value: dict) -> dict:
    shape(
        value,
        {
            "write",
            "safety",
            "allow_potentially_mutating",
            "budget",
            "reference",
            "locations",
            "request_pdu",
        },
    )
    if (
        type(value["write"]) is not bool
        or type(value["allow_potentially_mutating"]) is not bool
    ):
        raise ValueError("invalid boolean policy")
    if value["safety"] != ("potentially-mutating" if value["write"] else "read-only"):
        raise ValueError("safety contradicts operation")
    integer(value["budget"], 16)
    integer(value["reference"], 65535)
    if (
        not isinstance(value["locations"], list)
        or not 1 <= len(value["locations"]) <= 20
    ):
        raise ValueError("invalid locations")
    locations = [location(item) for item in value["locations"]]
    encoded = request(
        value["reference"], [item["range"] for item in locations], value["write"]
    )
    if encoded is None:
        raise ValueError("invalid configured wire request")
    wire(value["request_pdu"], encoded)
    return value


def response(config: dict, pdu: bytes) -> tuple[str | None, list[str]]:
    """Decode independently, preserving actual codec error ordering/acceptance."""
    if len(pdu) < 12:
        return "protocol", []
    (
        protocol,
        kind,
        _reserved,
        reference,
        parameter_size,
        data_size,
        error_class,
        error_code,
    ) = struct.unpack(">BBHHHHBB", pdu[:12])
    if (
        protocol != 0x32
        or kind not in (2, 3)
        or len(pdu) != 12 + parameter_size + data_size
    ):
        return "protocol", []
    if reference != config["reference"]:
        return "protocol", []
    if error_class or error_code:
        return "plc-rejected", []
    width = len(config["locations"])
    parameters = pdu[12 : 12 + parameter_size]
    if parameters != bytes([5 if config["write"] else 4, width]):
        return "protocol", []
    data = pdu[12 + parameter_size :]
    if config["write"]:
        if len(data) != width:
            return "protocol", []
        return None, ["success" if code == 255 else f"failure:{code}" for code in data]
    offset = 0
    for index, item in enumerate(config["locations"]):
        if offset + 4 > len(data):
            return "protocol", []
        code, transport, length = struct.unpack(">BBH", data[offset : offset + 4])
        offset += 4
        if transport == 9:
            size = length
        elif length % 8:
            return "protocol", []
        else:
            size = length // 8
        if offset + size > len(data):
            return "protocol", []
        offset += size
        if index + 1 < width and size % 2:
            if offset == len(data):
                return "protocol", []
            offset += 1
        if code == 255 and (transport != 4 or size != item["range"]["count"]):
            return "protocol", []
    return (None, []) if offset == len(data) else ("protocol", [])


def trace(config: dict, events: list[dict]) -> list[dict]:
    configuration(config)
    if not isinstance(events, list) or not 1 <= len(events) <= 1024:
        raise ValueError("invalid event array")
    lifecycle, phase = "connected", "idle"
    remaining, sends = 0, 0
    active = None
    history: list[dict] = []
    pending: list[dict] = []
    snapshots = []

    def finish(outcome: str | list[str]) -> None:
        nonlocal pending
        outcomes = [outcome] * len(pending) if isinstance(outcome, str) else outcome
        history.extend(
            {"location": deepcopy(item), "outcome": result}
            for item, result in zip(pending, outcomes, strict=True)
        )
        pending = []

    def fail(kind: str) -> dict:
        nonlocal lifecycle, remaining, active, phase
        permitted = (
            lifecycle != "closed"
            and remaining > 0
            and kind in ("timeout", "disconnected", "transport")
            and (not config["write"] or config["allow_potentially_mutating"])
        )
        if permitted:
            remaining -= 1
            if config["write"] and phase == "awaiting":
                finish("replayed-unknown")
            lifecycle, phase = "disconnected", "reconnect-cotp"
        else:
            if config["write"] and kind == "plc-rejected" and phase == "awaiting":
                finish("global-rejected")
            lifecycle, phase, active = "disconnected", "failed", None
        return accepted(retry=permitted)

    for event in events:
        if not isinstance(event, dict):
            raise TypeError("invalid event")
        operation = event.get("operation")
        if operation == "failure":
            shape(event, {"operation", "error_kind"})
            if event["error_kind"] not in KINDS:
                raise ValueError("unknown error kind")
        elif operation == "response":
            shape(event, {"operation", "response_pdu"})
            pdu = octets(event["response_pdu"])
        elif operation in (
            "begin",
            "send",
            "reconnect-setup",
            "reconnected",
            "disconnect",
        ):
            shape(event, {"operation"})
        else:
            raise ValueError("unknown event operation")
        outcome = accepted()
        if operation == "begin":
            if lifecycle != "connected":
                outcome = rejected("not-connected")
            elif active is not None:
                outcome = rejected("already-active")
            else:
                remaining, active, phase, sends = (
                    config["budget"],
                    config["reference"],
                    "ready",
                    0,
                )
                history, pending = [], []
        elif operation == "send":
            if lifecycle != "connected" or active is None or phase != "ready":
                outcome = rejected("send-phase")
            elif config["write"] and pending:
                outcome = rejected("write-progress")
            else:
                if config["write"]:
                    pending = deepcopy(config["locations"])
                sends += 1
                phase = "awaiting"
        elif operation == "failure":
            outcome = (
                fail(event["error_kind"])
                if active is not None
                and phase in ("awaiting", "reconnect-cotp", "reconnect-setup")
                else rejected("failure-phase")
            )
        elif operation == "reconnect-setup":
            if active is None or phase != "reconnect-cotp":
                outcome = rejected("reconnect-phase")
            else:
                phase = "reconnect-setup"
        elif operation == "reconnected":
            if (
                active is None
                or phase != "reconnect-setup"
                or lifecycle != "disconnected"
            ):
                outcome = rejected("reconnect-phase")
            else:
                lifecycle, phase = "connected", "ready"
        elif operation == "response":
            if lifecycle != "connected" or active is None or phase != "awaiting":
                outcome = rejected("response-phase")
            else:
                error, results = response(config, pdu)
                if error:
                    fail(error)
                    outcome = rejected("response-codec")
                else:
                    if config["write"]:
                        finish(results)
                    active, phase = None, "completed"
        elif operation == "disconnect":
            lifecycle, active, phase = "closed", None, "closed"
        attempts = deepcopy(history) + [
            {"location": deepcopy(item), "outcome": "pending"} for item in pending
        ]
        snapshots.append(
            {
                "result": outcome,
                "snapshot": {
                    "lifecycle": lifecycle,
                    "remaining": remaining,
                    "active_reference": active,
                    "phase": phase,
                    "sends": sends,
                    "attempts": attempts,
                },
            }
        )
    return snapshots


def validate(corpus: dict) -> int:
    shape(corpus, {"schema_version", "protocol", "cases"})
    if (
        type(corpus["schema_version"]) is not int
        or corpus["schema_version"] != 1
        or corpus["protocol"] != PROTOCOL
    ):
        raise ValueError("unsupported corpus header")
    if not isinstance(corpus["cases"], list) or not 1 <= len(corpus["cases"]) <= 4096:
        raise ValueError("invalid cases")
    identifiers: set[str] = set()
    total = 0
    for case in corpus["cases"]:
        shape(case, {"id", "seed", "config", "events", "expected_trace"})
        if (
            not isinstance(case["id"], str)
            or not 1 <= len(case["id"]) <= 256
            or case["id"] in identifiers
        ):
            raise ValueError("invalid/duplicate case ID")
        identifiers.add(case["id"])
        integer(case["seed"])
        expected = trace(case["config"], case["events"])
        # Serialization comparison distinguishes bool/int and int/float values;
        # ordinary Python equality would silently accept True==1 and 1.0==1.
        if json.dumps(expected, sort_keys=True, allow_nan=False) != json.dumps(
            case["expected_trace"], sort_keys=True, allow_nan=False
        ):
            raise ValueError(f"independent active-session trace differs: {case['id']}")
        total += len(expected)
    return total


def _response(
    config: dict, reference: int | None = None, count: int | None = None
) -> dict:
    ranges = [item["range"] for item in config["locations"]]
    data = bytearray()
    if config["write"]:
        data.extend(b"\xff" * len(ranges))
    else:
        for index, item in enumerate(ranges):
            content = payload(item)
            data.extend(b"\xff\x04" + struct.pack(">H", len(content) * 8) + content)
            if index + 1 < len(ranges) and len(content) % 2:
                data.append(0)
    pdu = packet(
        3,
        config["reference"] if reference is None else reference,
        bytes([5 if config["write"] else 4, len(ranges) if count is None else count]),
        bytes(data),
    )
    return {"operation": "response", "response_pdu": list(pdu)}


def self_test(corpus: dict) -> None:
    def must_reject(changed: dict) -> None:
        try:
            validate(changed)
        except (ValueError, TypeError, OverflowError):
            return
        raise AssertionError("active-session oracle accepted mutation")

    for case_index, case in enumerate(corpus["cases"]):
        changed = deepcopy(corpus)
        changed["cases"][case_index]["config"]["request_pdu"][-1] ^= 1
        must_reject(changed)
        for field in ("remaining", "sends", "active_reference", "phase", "lifecycle"):
            changed = deepcopy(corpus)
            snapshot = changed["cases"][case_index]["expected_trace"][0]["snapshot"]
            snapshot[field] = "mutated"
            must_reject(changed)
        changed = deepcopy(corpus)
        changed["cases"][case_index]["expected_trace"][0]["result"]["status"] = "reject"
        must_reject(changed)
        for step_index, step in enumerate(case["expected_trace"]):
            if step["snapshot"]["attempts"]:
                changed = deepcopy(corpus)
                changed["cases"][case_index]["expected_trace"][step_index]["snapshot"][
                    "attempts"
                ][0]["outcome"] = "success"
                must_reject(changed)
                changed = deepcopy(corpus)
                changed["cases"][case_index]["expected_trace"][step_index]["snapshot"][
                    "attempts"
                ][0]["location"]["range"]["start"] += 1
                must_reject(changed)
                break
        for event_index, event in enumerate(case["events"]):
            if (
                event["operation"] == "response"
                and case["expected_trace"][event_index]["result"]["status"] == "accept"
            ):
                changed = deepcopy(corpus)
                changed["cases"][case_index]["events"][event_index]["response_pdu"][
                    4
                ] ^= 1
                must_reject(changed)
                break
    for bad in (True, 1.0, "1", 2):
        changed = deepcopy(corpus)
        changed["schema_version"] = bad
        must_reject(changed)
    for field, bad in (
        ("budget", True),
        ("budget", 1.0),
        ("reference", True),
        ("write", 1),
        ("allow_potentially_mutating", 1),
        ("safety", "unknown"),
    ):
        changed = deepcopy(corpus)
        changed["cases"][0]["config"][field] = bad
        must_reject(changed)
    changed = deepcopy(corpus)
    changed["cases"].append(deepcopy(changed["cases"][0]))
    must_reject(changed)
    changed = deepcopy(corpus)
    changed["cases"][0]["events"][0]["extra"] = True
    must_reject(changed)
    changed = deepcopy(corpus)
    changed["cases"][0]["expected_trace"][0]["snapshot"]["sends"] = 0.0
    must_reject(changed)
    # Fixed expectations independent of every exported trace.
    config = deepcopy(
        next(case["config"] for case in corpus["cases"] if case["config"]["write"])
    )
    config["budget"] = 2
    config["allow_potentially_mutating"] = True
    begin, send = {"operation": "begin"}, {"operation": "send"}
    timeout = {"operation": "failure", "error_kind": "timeout"}
    setup, connected = {"operation": "reconnect-setup"}, {"operation": "reconnected"}
    width = len(config["locations"])
    exhausted = trace(
        config, [begin, send, timeout, timeout, setup, timeout, begin, send]
    )
    final = exhausted[-1]["snapshot"]
    if (
        (
            final["remaining"],
            final["sends"],
            final["active_reference"],
            final["phase"],
            final["lifecycle"],
        )
        != (0, 1, None, "failed", "disconnected")
        or len(final["attempts"]) != width
        or any(item["outcome"] != "replayed-unknown" for item in final["attempts"])
    ):
        raise AssertionError("failed reconnect manufactured operation attempts")
    recovered = trace(
        config, [begin, send, timeout, setup, connected, send, _response(config)]
    )[-1]["snapshot"]
    if (
        recovered["remaining"] != 1
        or recovered["sends"] != 2
        or recovered["active_reference"] is not None
        or recovered["phase"] != "completed"
        or [item["outcome"] for item in recovered["attempts"]]
        != ["replayed-unknown"] * width + ["success"] * width
    ):
        raise AssertionError("successful replay lost original uncertainty")
    config["allow_potentially_mutating"] = False
    conservative = trace(config, [begin, send, timeout])[-1]
    if (
        conservative["result"] != accepted(retry=False)
        or conservative["snapshot"]["remaining"] != 2
        or [item["outcome"] for item in conservative["snapshot"]["attempts"]]
        != ["pending"] * width
    ):
        raise AssertionError("conservative write policy differs")
    for bad_response in (
        _response(config, reference=(config["reference"] + 1) % 65536),
        _response(config, count=width + 1),
    ):
        control = trace(config, [begin, send, bad_response])[-1]
        if (
            control["result"] != rejected("response-codec")
            or control["snapshot"]["phase"] != "failed"
            or control["snapshot"]["sends"] != 1
        ):
            raise AssertionError("bad ACK correlation/count accepted")
    closed = trace(config, [{"operation": "disconnect"}, begin, connected])[-1]
    if closed["snapshot"]["lifecycle"] != "closed" or closed["result"] != rejected(
        "reconnect-phase"
    ):
        raise AssertionError("closed session resurrected")
    global_reject = _response(config)
    global_reject["response_pdu"][10:12] = [0x81, 4]
    control = trace(config, [begin, send, global_reject])[-1]
    if (
        control["result"] != rejected("response-codec")
        or [item["outcome"] for item in control["snapshot"]["attempts"]]
        != ["global-rejected"] * width
    ):
        raise AssertionError("PLC rejection lost write provenance")
    read_config = deepcopy(
        next(case["config"] for case in corpus["cases"] if not case["config"]["write"])
    )
    read_config["locations"] = read_config["locations"][:1]
    read_config["request_pdu"] = list(
        request(read_config["reference"], [read_config["locations"][0]["range"]], False)
    )
    valid_read = _response(read_config)
    control = trace(read_config, [begin, send, valid_read])[-1]["snapshot"]
    if (
        control["phase"] != "completed"
        or control["active_reference"] is not None
        or control["attempts"]
    ):
        raise AssertionError("read completion differs")
    wrong_size = deepcopy(valid_read)
    size = read_config["locations"][0]["range"]["count"] + 1
    wrong_size["response_pdu"][16:18] = list(struct.pack(">H", size * 8))
    control = trace(read_config, [begin, send, wrong_size])[-1]
    if (
        control["result"] != rejected("response-codec")
        or control["snapshot"]["phase"] != "failed"
    ):
        raise AssertionError("invalid read payload length accepted")


def run(path: Path = DEFAULT_CORPUS) -> None:
    corpus = json.loads(path.read_text(encoding="utf-8"))
    steps = validate(corpus)
    self_test(corpus)
    print(
        f"{len(corpus['cases'])}/{len(corpus['cases'])} independent active-session cases passed ({steps} steps)"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", nargs="?", type=Path, default=DEFAULT_CORPUS)
    run(parser.parse_args().corpus)
