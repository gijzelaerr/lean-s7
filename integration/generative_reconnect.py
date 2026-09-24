"""Seeded live reconnect configurations with independent replay expectations."""

from __future__ import annotations

import argparse
import json
import random
import socket
import subprocess
import threading
from dataclasses import asdict, dataclass
from pathlib import Path

from reconnect_faults import Case, _cases, _serve

SEED = 0x573743
COUNT = 32
MODES = ("read", "raw", "write", "multi")
TRANSIENT = ("cotp-eof", "setup-eof")
TERMINAL = ("cotp-invalid", "setup-invalid", "setup-reject", "setup-shrink")


@dataclass(frozen=True)
class Expected:
    recovered: bool
    connections: int
    sends: int
    write_attempts: int
    acknowledged: int
    pending_uncertain: int
    replayed_uncertain: int
    write_chronology: tuple[str, ...]


def expected(case: Case) -> Expected:
    """Derive gates without Case.succeeds/sessions or the native fixture model.

    Initial lost ACK is a wire attempt. A reconnect-stage failure consumes retry
    budget but never creates an operation attempt. Replay opt-in records the
    original write as replayed-unknown before trying the first reconnect.
    """
    transient = case.fault in TRANSIENT
    recovered = transient and case.budget > case.failures
    if case.budget == 0:
        reconnects = 0
    elif transient:
        reconnects = min(case.budget, case.failures + 1)
    else:
        reconnects = 1
    sends = 1 + int(recovered)
    width = 2 if case.mode == "multi" else int(case.mode == "write")
    replayed = case.budget > 0
    original = "replayed-unknown" if replayed else "pending"
    chronology = (original,) * width
    if recovered:
        chronology += ("acknowledged",) * width
    return Expected(
        recovered,
        1 + reconnects,
        sends,
        width * sends,
        width * int(recovered),
        width * int(not replayed),
        width * int(replayed),
        chronology,
    )


def generate(seed: int = SEED) -> tuple[Case, ...]:
    """Return 32 distinct configurations absent from the fixed 75-case suite.

    Existing native fixture bounds remain 0..4. Budgets above four are not
    silently passed to a fixture that cannot test them.
    """
    if not 0 <= seed <= 0xFFFFFFFF:
        raise ValueError("seed must be an unsigned 32-bit integer")
    rng = random.Random(seed)
    fixed = set(_cases())
    pool = [
        Case(mode, fault, budget, failures)
        for mode in MODES
        for fault in TRANSIENT
        for budget in range(5)
        for failures in range(5)
        if Case(mode, fault, budget, failures) not in fixed
    ] + [
        Case(mode, fault, budget, 1)
        for mode in MODES
        for fault in TERMINAL
        for budget in range(1, 4)
    ]
    # Stratification covers both stages for every public operation mode, the
    # zero-budget gate, every terminal reason, recovery, and exhaustion.
    selected = [
        Case(mode, fault, 3, rng.randrange(5)) for mode in MODES for fault in TRANSIENT
    ]
    selected.extend([Case("read", "cotp-eof", 0, 4), Case("write", "setup-eof", 4, 0)])
    selected.extend(
        Case(mode, fault, rng.randrange(1, 4), 1)
        for mode, fault in zip(MODES, TERMINAL, strict=True)
    )
    selected.append(Case("multi", "cotp-eof", 3, 4))
    selected = list(dict.fromkeys(selected))
    remaining = [case for case in pool if case not in selected]
    rng.shuffle(remaining)
    selected.extend(remaining[: COUNT - len(selected)])
    rng.shuffle(selected)
    return tuple(selected)


def _self_test() -> None:
    cases = generate()
    assert cases == generate() and cases != generate(SEED + 1)
    assert len(cases) == COUNT and len(set(cases)) == COUNT
    assert not set(cases).intersection(_cases())
    assert {(case.mode, case.fault) for case in cases if case.fault in TRANSIENT} == {
        (mode, fault) for mode in MODES for fault in TRANSIENT
    }
    assert {case.fault for case in cases if case.fault in TERMINAL} == set(TERMINAL)
    assert any(case.budget == 0 for case in cases)
    assert any(expected(case).recovered for case in cases)
    assert any(not expected(case).recovered for case in cases)
    for case in cases:
        oracle = expected(case)
        assert oracle.recovered == case.succeeds
        assert oracle.connections == case.sessions
        assert 1 <= oracle.connections <= case.budget + 1
        assert oracle.sends in (1, 2)
        assert len(oracle.write_chronology) == oracle.write_attempts
    assert expected(Case("write", "setup-eof", 0, 4)) == Expected(
        False, 1, 1, 1, 0, 1, 0, ("pending",)
    )
    assert expected(Case("multi", "cotp-eof", 3, 4)) == Expected(
        False, 4, 1, 2, 0, 0, 2, ("replayed-unknown", "replayed-unknown")
    )
    assert expected(Case("multi", "setup-eof", 4, 0)) == Expected(
        True,
        2,
        2,
        4,
        2,
        0,
        2,
        ("replayed-unknown", "replayed-unknown", "acknowledged", "acknowledged"),
    )
    for seed in range(100):
        generated = generate(seed)
        assert len(generated) == COUNT and len(set(generated)) == COUNT
        assert not set(generated).intersection(_cases())


def _run_case(root: Path, case: Case) -> str:
    oracle = expected(case)
    if oracle.connections != case.sessions or oracle.recovered != case.succeeds:
        raise RuntimeError("fixture disagrees with independent reconnect expectation")
    errors: list[Exception] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(8)
        listener.settimeout(4)
        worker = threading.Thread(target=_serve, args=(listener, case, errors))
        worker.start()
        try:
            outcome = subprocess.run(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "integration-reconnect-faults",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                    case.mode,
                    case.fault,
                    str(case.budget),
                    str(case.failures),
                ],
                cwd=root,
                capture_output=True,
                text=True,
                timeout=12,
                check=False,
            )
        finally:
            worker.join(timeout=5)
        if worker.is_alive():
            raise RuntimeError("generative reconnect peer did not terminate")
        if errors:
            raise errors[0]
        if outcome.returncode:
            raise RuntimeError(
                f"native reconnect failed: {outcome.stdout[-4096:]}{outcome.stderr[-4096:]}"
            )
        return outcome.stdout.strip()


def run(
    root: Path,
    seed: int = SEED,
    case_index: int | None = None,
    artifact_dir: Path | None = None,
) -> None:
    _self_test()
    cases = generate(seed)
    indices = range(len(cases)) if case_index is None else [case_index]
    for index in indices:
        if not 0 <= index < len(cases):
            raise ValueError("case index must be 0..31")
        case = cases[index]
        try:
            _run_case(root, case)
        except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
            artifact = {
                "schema_version": 1,
                "generator": "seeded-live-reconnect-v1",
                "seed": seed,
                "case_index": index,
                "configuration": asdict(case),
                "expected": asdict(expected(case)),
                "error": str(error)[-8192:],
                "replay": f"python integration/generative_reconnect.py --seed {seed} --case {index}",
            }
            print(json.dumps(artifact, sort_keys=True))
            if artifact_dir is not None:
                artifact_dir.mkdir(parents=True, exist_ok=True)
                target = artifact_dir / f"reconnect-{seed}-{index}.json"
                try:
                    with target.open("x", encoding="utf-8") as output:
                        output.write(json.dumps(artifact, indent=2) + "\n")
                except FileExistsError:
                    print(f"preserved existing replay artifact: {target}")
            raise RuntimeError(f"seed={seed} case={index} {case}: {error}") from error
    print(f"seeded live reconnect passed: {len(indices)} conversations, seed={seed}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=SEED)
    parser.add_argument("--case", type=int, default=None, dest="case_index")
    parser.add_argument("--artifact-dir", type=Path, default=None)
    arguments = parser.parse_args()
    run(Path(__file__).resolve().parents[1], **vars(arguments))
