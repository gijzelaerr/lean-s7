"""Seeded differential fuzzing of actual Lean session transitions and codecs.

Pure operational model, not live socket scheduling or PLC effects. Failure
artifacts retain config, seed and deletion-minimized events for exact replay.
"""

from __future__ import annotations

import argparse
import json
import random
import struct
import subprocess
from collections import Counter
from copy import deepcopy
from pathlib import Path

from conversation_conformance import integer, packet, payload, request, shape
from session_conformance import configuration, trace

SEEDS = (7, 2026, 65535, 23063)
ROOT = Path(__file__).resolve().parents[1]


def canonical(value: object) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def reply(config: dict, rng: random.Random, mutation: int = 0) -> dict:
    data = bytearray()
    locations = config["locations"]
    for index, item in enumerate(locations):
        code = rng.choice((255, 255, 5, 10, 0))
        if config["write"]:
            data.append(code)
        else:
            content = (
                payload(item["range"]) if code == 255 else rng.choice((b"", b"\xaa"))
            )
            transport = 4 if code == 255 else rng.choice((4, 9))
            length = len(content) * (1 if transport == 9 else 8)
            data.extend(bytes([code, transport]) + struct.pack(">H", length) + content)
            if index + 1 < len(locations) and len(content) % 2:
                data.append(0)
    pdu = bytearray(
        packet(
            3,
            config["reference"],
            bytes([5 if config["write"] else 4, len(locations)]),
            bytes(data),
        )
    )
    if mutation == 1:
        pdu[0] ^= 1
    elif mutation == 2:
        pdu[1] = 7
    elif mutation == 3:
        pdu[4] ^= 1
    elif mutation == 4:
        pdu[12] = 4 if config["write"] else 5
    elif mutation == 5:
        pdu[13] += 1
    elif mutation == 6:
        pdu = pdu[: rng.randrange(len(pdu))]
    elif mutation == 7:
        pdu.append(0)
    elif mutation == 8:
        pdu[7] ^= 1
    elif mutation == 9:
        pdu[9] ^= 1
    elif mutation == 10:
        pdu[10:12] = b"\x81\x04"
    elif mutation == 11:
        pdu[1] = 2  # The response decoder permits ACK and ACK_DATA alike.
    elif mutation == 12:
        pdu[2:4] = b"\xaa\xbb"  # Reserved header bytes remain opaque.
    elif mutation == 13 and not config["write"]:
        pdu[15] = 7
    elif mutation == 14 and not config["write"]:
        pdu[17] |= 1
    elif mutation == 15:
        pdu[14:] = b""
        pdu[8:10] = b"\0\0"
    return {"operation": "response", "response_pdu": list(pdu)}


def generate(seed: int, count: int) -> list[dict]:
    rng = random.Random(seed)
    cases = []
    for case_index in range(count):
        write = bool(rng.randrange(2))
        locations = []
        for index in range(rng.randint(1, 6)):
            memory = {
                "db_number": rng.choice((0, 1, 65535)),
                "start": rng.randrange(128),
                "count": rng.randint(1, 7),
            }
            if locations and rng.randrange(3) == 0:
                memory = deepcopy(rng.choice(locations)["range"])
            locations.append(
                {
                    "range": memory,
                    "item_index": index,
                    "chunk_byte_offset": rng.randrange(8),
                }
            )
        config = {
            "write": write,
            "safety": "potentially-mutating" if write else "read-only",
            "allow_potentially_mutating": bool(rng.randrange(2)),
            "budget": rng.randrange(5),
            "reference": rng.choice((0, 65535, rng.randrange(65536))),
            "locations": locations,
        }
        config["request_pdu"] = list(
            request(config["reference"], [item["range"] for item in locations], write)
        )
        events = [{"operation": "begin"}, {"operation": "send"}]
        if case_index % 4 in (0, 2):
            events.append({"operation": "failure", "error_kind": "disconnected"})
        else:
            events.append(
                reply(config, rng, (case_index // 4) % 16 if case_index % 4 == 1 else 0)
            )
        for _ in range(rng.randint(8, 24)):
            state = trace(config, events)[-1]["snapshot"]
            phase = state["phase"]
            if phase == "awaiting" and rng.randrange(5):
                event = (
                    reply(config, rng, rng.randrange(16))
                    if rng.randrange(2)
                    else {
                        "operation": "failure",
                        "error_kind": rng.choice(
                            (
                                "timeout",
                                "transport",
                                "disconnected",
                                "protocol",
                                "plc-rejected",
                            )
                        ),
                    }
                )
            elif phase in ("reconnect-cotp", "reconnect-setup") and rng.randrange(5):
                event = (
                    {
                        "operation": "reconnect-setup"
                        if phase == "reconnect-cotp"
                        else "reconnected"
                    }
                    if rng.randrange(2)
                    else {
                        "operation": "failure",
                        "error_kind": rng.choice(
                            ("timeout", "transport", "disconnected")
                        ),
                    }
                )
            elif phase == "ready" and rng.randrange(5):
                event = {"operation": "send"}
            elif phase in ("idle", "completed") and rng.randrange(5):
                event = {"operation": "begin"}
            else:
                operation = rng.choice(
                    (
                        "begin",
                        "send",
                        "failure",
                        "response",
                        "reconnect-setup",
                        "reconnected",
                        "disconnect",
                    )
                )
                event = (
                    reply(config, rng, rng.randrange(16))
                    if operation == "response"
                    else {
                        "operation": operation,
                        **({"error_kind": "timeout"} if operation == "failure" else {}),
                    }
                )
            events.append(event)
        events.extend(
            (
                {"operation": "disconnect"},
                {"operation": "begin"},
                {"operation": "send"},
                {"operation": "reconnected"},
            )
        )
        cases.append(
            {"seed": seed, "case_index": case_index, "config": config, "events": events}
        )
    return cases


def native(cases: list[dict]) -> list[list[dict]]:
    batch = [{"config": case["config"], "events": case["events"]} for case in cases]
    result = subprocess.run(
        [str(ROOT / ".lake/build/bin/lean-s7-fuzz")],
        input=canonical(batch) + "\n",
        capture_output=True,
        text=True,
        timeout=15,
        check=False,
    )
    if result.returncode:
        raise RuntimeError(f"native fuzz adapter failed: {result.stderr}")
    output = json.loads(result.stdout)
    if set(output) != {"traces"} or len(output["traces"]) != len(cases):
        raise RuntimeError(f"invalid native fuzz output: {output}")
    return output["traces"]


def minimize(events: list[dict], fails) -> list[dict]:
    """Deletion minimization; preserves the exact seed/config/remaining bytes."""
    result = deepcopy(events)
    width = max(1, len(result) // 2)
    while width:
        index = 0
        while index < len(result):
            candidate = result[:index] + result[index + width :]
            if candidate and fails(candidate):
                result = candidate
                index = 0  # Revisit earlier deletions after a later simplification.
            else:
                index += width
        width //= 2
    return result


def compare(case: dict, observed: list[dict]) -> bool:
    return canonical(observed) == canonical(trace(case["config"], case["events"]))


def self_test() -> None:
    if generate(7, 4) != generate(7, 4):
        raise AssertionError("generator is not reproducible")
    sample = [
        {"operation": "begin"},
        {"operation": "send"},
        {"operation": "disconnect"},
    ]
    reduced = minimize(
        sample, lambda events: any(event["operation"] == "send" for event in events)
    )
    if reduced != [{"operation": "send"}]:
        raise AssertionError("minimizer did not retain exact failing event")
    nonmonotonic = lambda events: (
        tuple(event["operation"] for event in events)
        in (("begin", "send", "disconnect"), ("begin", "disconnect"), ("disconnect",))
    )
    if minimize(sample, nonmonotonic) != [{"operation": "disconnect"}]:
        raise AssertionError("minimizer failed to revisit an earlier event")
    case = generate(7, 1)[0]
    observed = trace(case["config"], case["events"])
    changed = deepcopy(observed)
    changed[0]["snapshot"]["remaining"] += 1
    if compare(case, changed):
        raise AssertionError("differential checker failed to detect divergence")


def replay_case(path: Path) -> dict:
    with path.open("rb") as stream:
        content = stream.read(65537)
    if len(content) > 65536:
        raise ValueError("replay artifact exceeds 64 KiB bound")
    case = json.loads(content)
    shape(case, {"seed", "case_index", "config", "events"})
    integer(case["seed"])
    integer(case["case_index"], 4095)
    configuration(case["config"])
    if not isinstance(case["events"], list) or not 1 <= len(case["events"]) <= 128:
        raise ValueError("replay event count exceeds bound")
    trace(case["config"], case["events"])
    return case


def adapter_controls() -> None:
    case = generate(7, 1)[0]
    valid = {"config": case["config"], "events": case["events"]}
    invalid = [
        [],
        {},
        [dict(valid, events=[])],
        [dict(valid, events=[{"operation": "disconnect"}] * 129)],
    ]
    for field, value in (
        ("budget", 17),
        ("reference", 65536),
        ("write", 2),
        ("safety", "wrong"),
        ("locations", []),
    ):
        changed = deepcopy(valid)
        changed["config"][field] = value
        invalid.append([changed])
    changed = deepcopy(valid)
    changed["config"]["request_pdu"][-1] ^= 1
    invalid.append([changed])
    for event in (
        {"operation": "unknown"},
        {"operation": "send", "extra": 0},
        {"operation": "response", "response_pdu": [256]},
        {"operation": "failure", "error_kind": "unknown"},
    ):
        invalid.append([dict(valid, events=[event])])
    lines = "".join(canonical(value) + "\n" for value in invalid)
    result = subprocess.run(
        [str(ROOT / ".lake/build/bin/lean-s7-fuzz")],
        input=lines,
        capture_output=True,
        text=True,
        timeout=15,
        check=False,
    )
    results = [json.loads(line) for line in result.stdout.splitlines()]
    if (
        result.returncode
        or len(results) != len(invalid)
        or any(set(value) != {"error"} for value in results)
    ):
        raise AssertionError("native fuzz adapter accepted invalid fixture")


def run(
    per_seed: int = 64, replay: Path | None = None, failure_output: Path | None = None
) -> dict:
    if not 1 <= per_seed <= 4096:
        raise ValueError("fuzz case count exceeds bound")
    self_test()
    adapter_controls()
    cases = (
        [replay_case(replay)]
        if replay
        else [case for seed in SEEDS for case in generate(seed, per_seed)]
    )
    statistics: Counter = Counter()
    for offset in range(0, len(cases), 16):
        batch = cases[offset : offset + 16]
        for case, observed in zip(batch, native(batch), strict=True):
            if not compare(case, observed):

                def fails(events: list[dict], failing_case: dict = case) -> bool:
                    candidate = {**failing_case, "events": events}
                    return not compare(candidate, native([candidate])[0])

                failure = {**case, "events": minimize(case["events"], fails)}
                artifact = (
                    failure_output
                    or ROOT
                    / "reports"
                    / f"session-fuzz-failure-{case['seed']}-{case['case_index']}.json"
                )
                serialized = canonical(failure)
                artifact_note = str(artifact)
                try:
                    if len(serialized.encode()) + 1 > 65536:
                        raise ValueError("minimized artifact exceeds replay bound")
                    # Generated runtime artifact, never overwrite prior evidence.
                    with artifact.open("x") as stream:
                        stream.write(serialized + "\n")
                except (OSError, ValueError) as error:
                    artifact_note = f"not saved ({error}); prior evidence is untouched"
                raise RuntimeError(
                    f"differential divergence; artifact {artifact_note}; replay: "
                    + serialized
                )
            for event, step in zip(case["events"], observed, strict=True):
                statistics["events"] += 1
                statistics["event:" + event["operation"]] += 1
                statistics["phase:" + step["snapshot"]["phase"]] += 1
                statistics["result:" + step["result"]["status"]] += 1
                if "retry" in step["result"]:
                    statistics["retry:" + str(step["result"]["retry"]).lower()] += 1
    result = {
        "schema_version": 1,
        "scope": "actual pure session transitions and S7 response codecs; not Client IO equivalence",
        "seeds": list(SEEDS) if not replay else [cases[0]["seed"]],
        "cases": len(cases),
        "coverage": dict(sorted(statistics.items())),
    }
    print(canonical(result))
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--per-seed", type=int, default=64)
    parser.add_argument("--replay", type=Path)
    parser.add_argument("--failure-output", type=Path)
    options = parser.parse_args()
    run(options.per_seed, options.replay, options.failure_output)
