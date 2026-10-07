# ruff: noqa: BLE001  (any python-snap7 exception, whatever its type, counts as a rejection)
"""Differential fuzzing of the Lean decoders against python-snap7.

Corpus PDUs and payloads are mutated deterministically (fixed seed: bit flips,
byte replacement, truncation, insertion, deletion, trailing bytes). Each mutant is
decoded by the Lean oracle (``lean-s7-decode``) and by python-snap7; the verdicts
(accept/reject and the decoded payload) are compared and grouped:

* ``both-reject`` / ``both-accept-equal``  agreement;
* ``lean-rejects``    Lean refuses, python-snap7 accepts (python-snap7 is lenient);
* ``python-rejects``  python-snap7 refuses, Lean accepts;
* ``accept-different`` both accept but decode different values.

Disagreements are leads, not verdicts: python-snap7 is not the specification, and
Lean's stricter rules are deliberate. Run ``--examples N`` to print shortest
examples per group. Optional, local, not run in CI.

    lake build lean-s7-decode
    python integration/python_snap7_fuzz.py [--seed 1] [--per-seed 150] [--examples 3]
"""

from __future__ import annotations

import argparse
import json
import logging
import random
import struct
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from python_snap7_consumer import S7Protocol, userdata_response
from snap7.datatypes import S7WordLen

logging.disable(logging.CRITICAL)

ROOT = Path(__file__).resolve().parent.parent
CORPUS = ROOT / "conformance" / "v1"
ORACLE = (
    ROOT
    / ".lake"
    / "build"
    / "bin"
    / ("lean-s7-decode.exe" if sys.platform == "win32" else "lean-s7-decode")
)
INTERESTING = (
    0x00,
    0x01,
    0x02,
    0x03,
    0x04,
    0x09,
    0x0A,
    0x0F,
    0x10,
    0x7F,
    0x80,
    0xFB,
    0xFE,
    0xFF,
)


def mutate(data: bytes, rng: random.Random) -> bytes:
    out = bytearray(data)
    for _ in range(rng.choice((1, 1, 1, 2, 3))):
        kind = rng.randrange(7)
        if not out and kind not in (3, 6):
            kind = 3
        if kind == 0:
            out[rng.randrange(len(out))] ^= 1 << rng.randrange(8)
        elif kind == 1:
            out[rng.randrange(len(out))] = rng.choice(INTERESTING)
        elif kind == 2:
            del out[rng.randrange(len(out)) :]
        elif kind == 3:
            out.insert(rng.randrange(len(out) + 1), rng.choice(INTERESTING))
        elif kind == 4:
            del out[rng.randrange(len(out))]
        elif kind == 5:
            index = rng.randrange(len(out))
            out[index : index + 1] = bytes([out[index]]) * 2
        else:
            out.append(rng.choice(INTERESTING))
    return bytes(out)


# --- python-snap7 verdicts (the same calls the client makes) ---------------------


def py_userdata(reference: int, group: int, sub: int, pdu: bytes) -> str:
    try:
        protocol = S7Protocol()
        parsed = protocol.parse_response(pdu)
        protocol.sequence = reference
        protocol.validate_pdu_reference(parsed["sequence"])
        protocol.check_userdata_response(parsed, group, sub)
        parameters = parsed.get("parameters") or {}
        data = (parsed.get("data") or {}).get("data", b"")
        return f"accept {parameters.get('sequence_number')} {1 if parameters.get('last_data_unit') else 0} {bytes(data).hex()}"
    except Exception:
        return "reject"


def py_upload(reference: int, pdu: bytes) -> str:
    try:
        protocol = S7Protocol()
        parsed = protocol.parse_response(pdu)
        protocol.sequence = reference
        protocol.validate_pdu_reference(parsed["sequence"])
        payload, is_last = protocol.parse_upload_fragment(parsed)
        return f"accept {1 if is_last else 0} {payload.hex()}"
    except Exception:
        return "reject"


def py_read(reference: int, size: int, pdu: bytes) -> str:
    try:
        protocol = S7Protocol()
        parsed = protocol.parse_response(pdu)
        protocol.sequence = reference
        protocol.validate_pdu_reference(parsed["sequence"])
        data = protocol.extract_read_data(parsed, S7WordLen.BYTE, size)
        return f"accept {bytes(data).hex()}"
    except Exception:
        return "reject"


def py_block(kind: str, payload: bytes) -> str:
    group, sub = {"blockcounts": (3, 1), "blocklist": (3, 2), "blockinfo": (3, 3)}[kind]
    try:
        protocol = S7Protocol()
        parsed = protocol.parse_response(userdata_response(group, sub, payload))
        if kind == "blockcounts":
            c = protocol.parse_list_blocks_response(parsed)
            keys = (
                "OBCount",
                "FBCount",
                "FCCount",
                "SFBCount",
                "SFCCount",
                "DBCount",
                "SDBCount",
            )
            return "accept " + " ".join(str(c[k]) for k in keys)
        if kind == "blocklist":
            return " ".join(
                [
                    "accept",
                    *map(str, protocol.parse_list_blocks_of_type_response(parsed)),
                ]
            )
        i = protocol.parse_get_block_info_response(parsed)
        keys = (
            "block_number",
            "mc7_size",
            "load_size",
            "local_data",
            "sbb_length",
            "checksum",
            "version",
            "block_flags",
            "block_lang",
        )
        return "accept " + " ".join(str(i[k]) for k in keys)
    except Exception:
        return "reject"


# --- seeds ----------------------------------------------------------------------


def ack_data(parameters: bytes, data: bytes) -> bytes:
    return (
        struct.pack(">BBHHHHBB", 0x32, 3, 0, 1, len(parameters), len(data), 0, 0)
        + parameters
        + data
    )


def seeds() -> list[tuple[str, tuple[Any, ...], bytes]]:
    """(kind, fixed arguments, seed bytes) for every accepted corpus case."""
    s7 = json.loads((CORPUS / "s7.json").read_text(encoding="utf-8"))
    mg = json.loads((CORPUS / "management.json").read_text(encoding="utf-8"))
    out: list[tuple[str, tuple[Any, ...], bytes]] = []
    for case in s7["userdata_cases"]:
        if case["expected"]["status"] == "accept":
            out.append(
                (
                    "userdata",
                    (1, case["expected_group"], case["expected_subfunction"]),
                    bytes(case["pdu"]),
                )
            )
    for case in mg["decoder_cases"]:
        if case["expected"]["status"] == "accept":
            out.append(
                (
                    "userdata",
                    (case["reference"], case["group"], case["subfunction"]),
                    bytes(case["pdu"]),
                )
            )
    for case in s7["upload_cases"]:
        if case["expected"]["status"] == "accept":
            out.append(("upload", (1,), bytes(case["pdu"])))
    for case in s7["response_cases"]:
        if case["operation"] == "read" and case["expected"]["status"] == "accept":
            pdu = ack_data(bytes(case["parameters"]), bytes(case["data"]))
            out.append(("read", (1, case["requested_bytes"]), pdu))
    for kind, array in (
        ("blockcounts", "block_count_cases"),
        ("blocklist", "block_list_cases"),
        ("blockinfo", "block_info_cases"),
    ):
        for case in s7[array]:
            if case["expected"]["status"] == "accept":
                out.append((kind, (), bytes(case["payload"])))
    return out


def lean_args(kind: str, args: tuple[Any, ...], data: bytes) -> str:
    return " ".join([kind, *map(str, args), data.hex() or "-"])


def python_verdict(kind: str, args: tuple[Any, ...], data: bytes) -> str:
    if kind == "userdata":
        return py_userdata(*args, data)
    if kind == "upload":
        return py_upload(*args, data)
    if kind == "read":
        return py_read(*args, data)
    return py_block(kind, data)


def classify(lean: str, python: str) -> str:
    if lean == python:
        return "both-reject" if lean == "reject" else "both-accept-equal"
    if lean == "reject":
        return "lean-rejects"
    if python == "reject":
        return "python-rejects"
    return "accept-different"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--per-seed", type=int, default=150)
    parser.add_argument("--examples", type=int, default=0)
    args = parser.parse_args()
    if not ORACLE.exists():
        print(
            f"missing {ORACLE}; run `lake build lean-s7-decode` first", file=sys.stderr
        )
        return 1

    rng = random.Random(args.seed)
    mutants: list[tuple[str, tuple[Any, ...], bytes]] = []
    seed_of: dict[int, bytes] = {}
    for kind, fixed, seed in seeds():
        mutants.append((kind, fixed, seed))
        for _ in range(args.per_seed):
            mutant = mutate(seed, rng)
            seed_of[id(mutant)] = seed
            mutants.append((kind, fixed, mutant))
    lines = "\n".join(lean_args(*mutant) for mutant in mutants) + "\n"
    answers = subprocess.run(
        [str(ORACLE)], input=lines, capture_output=True, text=True, check=True
    ).stdout.splitlines()
    if len(answers) != len(mutants):
        print(
            f"oracle returned {len(answers)} answers for {len(mutants)} mutants",
            file=sys.stderr,
        )
        return 1

    offsets: Counter[tuple[str, str, int]] = Counter()
    base_ok: dict[bytes, bool] = {}
    for (kind, fixed, data), lean in zip(mutants, answers, strict=True):
        if data in {seed for _, _, seed in seeds()}:
            base_ok[data] = classify(lean, python_verdict(kind, fixed, data)) in (
                "both-accept-equal",
                "both-reject",
            )
    skipped = sorted({d.hex()[:24] for d, ok in base_ok.items() if not ok})
    counts: Counter[tuple[str, str]] = Counter()
    examples: dict[tuple[str, str], list[tuple[int, str, str, str]]] = defaultdict(list)
    for (kind, fixed, data), lean in zip(mutants, answers, strict=True):
        python = python_verdict(kind, fixed, data)
        group = classify(lean, python)
        origin = seed_of.get(id(data), data)
        if base_ok.get(origin) is False:
            group = "seed-disagrees"
            counts[(kind, group)] += 1
            continue
        counts[(kind, group)] += 1
        if group in ("lean-rejects", "python-rejects", "accept-different"):
            base = seed_of.get(id(data))
            if base is not None and len(base) == len(data):
                for index, (old, new) in enumerate(zip(base, data, strict=True)):
                    if old != new:
                        offsets[(kind, group, index)] += 1
        if group in ("lean-rejects", "python-rejects", "accept-different"):
            examples[(kind, group)].append(
                (len(data), data.hex(), lean[:90], python[:90])
            )
    print(
        f"seed {args.seed}: {len(mutants)} inputs from {len(seeds())} accepted corpus cases"
    )
    print(
        f"  {len(skipped)} seed(s) already disagree unmutated and are excluded from the groups below"
    )
    for kind in sorted({k for k, _ in counts}):
        row = ", ".join(
            f"{g} {counts[(kind, g)]}"
            for g in (
                "both-accept-equal",
                "both-reject",
                "lean-rejects",
                "python-rejects",
                "accept-different",
            )
        )
        print(f"  {kind:12} {row}")
    for (kind, group), found in sorted(examples.items()):
        top = sorted(
            ((n, o) for (k, g, o), n in offsets.items() if (k, g) == (kind, group)),
            reverse=True,
        )[:6]
        print(
            f"  [{kind} {group}] most-mutated byte offsets (same-length mutants): "
            + ", ".join(f"{o}x{n}" for n, o in top)
        )
        for length, hexdata, lean, python in sorted(found)[: args.examples]:
            print(
                f"  [{kind} {group}] {length}B {hexdata}\n      lean:   {lean}\n      python: {python}"
            )
    return 0


if __name__ == "__main__":
    sys.exit(main())
