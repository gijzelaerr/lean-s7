"""Seeded native conversations and bounded failure-preserving sequence reduction."""

from __future__ import annotations

import random
import socket
import struct
import subprocess
import threading
from collections.abc import Callable
from pathlib import Path

from concurrency import _handshake
from multi_batching import _ack, _receive, _request, _send


def minimize(plan: str, fails: Callable[[str], bool], budget: int = 24) -> str:
    """Delete contiguous chunks, retaining only candidates with the same failure.

    The bounded result preserves the predicate, not a claim of global minimality.
    The empty candidate is intentionally allowed for standalone lifecycle failures.
    """
    if not fails(plan):
        raise ValueError("initial plan does not reproduce the target failure")
    width = max(1, len(plan) // 2)
    attempts = 0
    while plan and attempts < budget:
        changed = False
        for offset in range(0, len(plan), width):
            candidate = plan[:offset] + plan[offset + width :]
            attempts += 1
            if fails(candidate):
                plan = candidate
                changed = True
                break
            if attempts >= budget:
                break
        if not changed:
            if width == 1:
                break
            width = max(1, width // 2)
        else:
            width = min(width, max(1, len(plan)))
    return plan


def _check_reducer() -> None:
    for original in ("rwmRnxcz", "rrrrRwwz", "z", ""):
        predicate = lambda plan: "R" in plan and "z" in plan
        if predicate(original):
            reduced = minimize(original, predicate)
            if reduced != "Rz":
                raise RuntimeError(f"sequence reducer lost required order: {reduced}")
    if minimize("abc", lambda _: True) != "":
        raise RuntimeError("sequence reducer did not test the empty candidate")
    try:
        minimize("abc", lambda _: False)
    except ValueError:
        pass
    else:
        raise RuntimeError("sequence reducer accepted a non-failing initial plan")
    calls: list[str] = []

    def unchanged(plan: str) -> bool:
        calls.append(plan)
        return plan == "abcdef"

    if minimize("abcdef", unchanged, budget=2) != "abcdef" or len(calls) != 3:
        raise RuntimeError("sequence reducer exceeded its predicate budget")


def _spec(start: int) -> bytes:
    return b"\x12\x0a\x10\x02\0\x01\0\x01\x84" + (start * 8).to_bytes(3, "big")


def _check(request: bytes, op: str, index: int) -> None:
    write = op in "wnxd"
    count = 2 if op in "mn" else 1
    start = 10 + index
    parameters = bytes([5 if write else 4, count]) + _spec(start)
    if count == 2:
        parameters += _spec(start + 1 if op == "m" else start)
    value = (index * 17 + 3) % 256
    data = b"\0\x04\0\x08" + bytes([value]) if write else b""
    if op == "n":
        data += b"\0\0\x04\0\x08" + bytes([(value + 1) % 256])
    expected = struct.pack(">BBHHHH", 0x32, 1, 0, 0, len(parameters), len(data))
    expected += parameters + data
    if request[:4] != expected[:4] or request[6:] != expected[6:]:
        raise RuntimeError(f"mixed wire oracle mismatch at operation {index} ({op})")


def _accept(listener: socket.socket) -> socket.socket:
    connection, _ = listener.accept()
    try:
        _handshake(connection)
    except (OSError, RuntimeError, ValueError, IndexError, struct.error):
        connection.close()
        raise
    return connection


def _serve(listener: socket.socket, plan: str, errors: list[str]) -> None:
    connection: socket.socket | None = None
    try:
        connection = _accept(listener)
        for index, op in enumerate(plan):
            if op == "c":
                disconnect = _receive(connection)
                if len(disconnect) != 7 or disconnect[1] != 0x80:
                    raise RuntimeError("mixed reconnect omitted disconnect")
                connection.close()
                connection = _accept(listener)
                continue
            request = _request(connection)
            _check(request, op, index)
            if op == "R":
                connection.close()
                connection = _accept(listener)
                request = _request(connection)
                _check(request, op, index)
            if op == "d":
                connection.shutdown(socket.SHUT_RDWR)
                connection.close()
                connection = None
                # A dropped mutating request must not reconnect or replay.
                listener.settimeout(0.15)
                try:
                    unexpected, _ = listener.accept()
                    unexpected.close()
                except TimeoutError:
                    pass
                else:
                    raise RuntimeError("mixed lost write acknowledgement was replayed")
                return
            reference = int.from_bytes(request[4:6], "big")
            value = (index * 17 + 3) % 256
            if op == "z":
                # Correlated ACK of wrong service is malformed, not stale.
                packet = _ack(reference, b"\x05\x01", b"\xff")
            elif op == "x":
                packet = bytearray(_ack(reference, b"\x05\x01"))
                packet[10:12] = b"\x81\x04"
            elif op in "wmnd":
                if op == "m":
                    data = b"\xff\x04\0\x08" + bytes([value]) + b"\0\x05\0\0\0"
                    packet = _ack(reference, b"\x04\x02", data)
                else:
                    packet = _ack(
                        reference,
                        bytes([5, 2 if op == "n" else 1]),
                        b"\xff\x05" if op == "n" else b"\xff",
                    )
            else:
                packet = _ack(
                    reference, b"\x04\x01", b"\xff\x04\0\x08" + bytes([value])
                )
            _send(connection, b"\x02\xf0\x80" + packet)
            if op == "z":
                try:
                    frame = _receive(connection)
                except ConnectionResetError:
                    # Shutdown of a poisoned session may legally reset TCP.
                    pass
                except RuntimeError as error:
                    if "closed an incomplete frame" not in str(error):
                        raise
                else:
                    # Cleanup may emit COTP DR, but never another S7 request.
                    if len(frame) != 7 or frame[1] != 0x80:
                        raise RuntimeError("mixed malformed reply allowed later IO")
                    try:
                        unexpected = connection.recv(1)
                    except ConnectionResetError:
                        unexpected = b""
                    if unexpected:
                        raise RuntimeError("mixed malformed reply allowed IO after DR")
                return
        disconnect = _receive(connection)
        if len(disconnect) != 7 or disconnect[1] != 0x80:
            raise RuntimeError("mixed plan did not terminate with disconnect")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(str(error))
    finally:
        if connection is not None:
            connection.close()


def _case(plan: str) -> str | None:
    executable = Path(__file__).resolve().parents[1] / ".lake/build/bin/lean-s7"
    errors: list[str] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(2)
        listener.settimeout(3)
        thread = threading.Thread(target=_serve, args=(listener, plan, errors))
        thread.start()
        try:
            outcome = subprocess.run(
                [
                    str(executable),
                    "integration-mixed-operations",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                    plan,
                ],
                check=False,
                capture_output=True,
                text=True,
                timeout=10,
            )
        except subprocess.TimeoutExpired:
            outcome = None
        thread.join(4)
        if outcome is None:
            return "native: process timeout"
        if outcome.returncode:
            return "native: " + (outcome.stderr.strip() or outcome.stdout.strip())
        if thread.is_alive():
            return "peer: unfinished conversation"
        if errors:
            return "peer: " + errors[0]
        print(outcome.stdout.strip())
        return None


def run_mixed_operations() -> None:
    _check_reducer()
    seeds = (7, 2026, 65535, 0x5A17)
    for index, seed in enumerate(seeds):
        generator = random.Random(seed)
        operations = list("rwmnxRc")
        generator.shuffle(operations)
        operations += generator.choices("rwmnx", k=8)
        plan = "".join(operations) + ("z" if index % 2 == 0 else "d")
        failure = _case(plan)
        if failure is not None:
            # Equality retains the original source and complete diagnostic, not
            # merely any unsuccessful subprocess or unrelated peer failure.
            reduced = minimize(
                plan,
                lambda candidate, target=failure: _case(candidate) == target,
                budget=12,
            )
            raise RuntimeError(
                f"mixed seed={seed} plan={plan!r} reduced={reduced!r}: {failure}; "
                "replay with mixed_operations._case(reduced)"
            )


if __name__ == "__main__":
    run_mixed_operations()
