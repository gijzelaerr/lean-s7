"""Repeated classic S7 failures must consume the configured replay allowance."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path

from boundary_operations import _closed, _handshake
from multi_batching import _ack, _request, _send


def expected_attempts(mode: str, budget: int, drops: int) -> tuple[int, bool]:
    replay = mode in ("read", "raw-opt-in", "write-opt-in")
    success = drops == 0 or (replay and drops <= budget)
    return (drops + 1 if success else budget + 1 if replay else 1), success


def _check(request: bytes, write: bool) -> int:
    parameters = bytes([5 if write else 4, 1])
    parameters += b"\x12\x0a\x10\x02\0\x01\0\x01\x84\0\0\0"
    data = b"\0\x04\0\x08\x2a" if write else b""
    expected = struct.pack(">BBHHHH", 0x32, 1, 0, 0, len(parameters), len(data))
    expected += parameters + data
    if request[:4] != expected[:4] or request[6:] != expected[6:]:
        raise RuntimeError("retry-budget request changed operation/address/payload")
    return int.from_bytes(request[4:6], "big")


def _serve(
    listener: socket.socket, mode: str, budget: int, drops: int, errors: list[Exception]
) -> None:
    stage = "initial accept"
    try:
        attempts, success = expected_attempts(mode, budget, drops)
        original = None
        for index in range(attempts):
            stage = f"attempt {index + 1}/{attempts} accept"
            connection, _ = listener.accept()
            with connection:
                _handshake(connection, 480)
                stage = f"attempt {index + 1}/{attempts} request"
                request = _request(connection)
                reference = _check(request, mode.startswith("write"))
                if original is None:
                    original = request
                elif request != original:
                    raise RuntimeError("repeated retry changed exact request/reference")
                if index < drops:
                    connection.shutdown(socket.SHUT_RDWR)
                    continue
                if not success or index + 1 != attempts:
                    raise RuntimeError("independent attempt accounting diverged")
                write = mode.startswith("write")
                response = _ack(
                    reference,
                    bytes([5 if write else 4, 1]),
                    b"\xff" if write else b"\xff\x04\0\x08\x2a",
                )
                _send(connection, b"\x02\xf0\x80" + response)
                stage = "successful terminal disconnect"
                _closed(connection)
        stage = "no excess retry or fresh-call resurrection"
        listener.settimeout(0.15)
        try:
            extra, _ = listener.accept()
        except TimeoutError:
            return
        extra.close()
        raise RuntimeError("retry allowance exceeded or exhausted client resurrected")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(
            RuntimeError(
                f"retry budget {mode} allowance={budget} drops={drops}, {stage}: {error}"
            )
        )


def _self_test() -> None:
    for budget in range(5):
        for drops in range(6):
            for mode in ("read", "raw", "raw-opt-in", "write", "write-opt-in"):
                attempts, success = expected_attempts(mode, budget, drops)
                if mode in ("raw", "write"):
                    assert attempts == 1 and success == (drops == 0)
                else:
                    assert attempts == min(drops, budget) + 1 and success == (
                        drops <= budget
                    )
    for write in (False, True):
        parameters = (
            bytes([5 if write else 4, 1]) + b"\x12\x0a\x10\x02\0\x01\0\x01\x84\0\0\0"
        )
        data = b"\0\x04\0\x08\x2a" if write else b""
        request = (
            struct.pack(">BBHHHH", 0x32, 1, 0, 65535, len(parameters), len(data))
            + parameters
            + data
        )
        assert _check(request, write) == 65535
        for position in (0, 1, 6, 8, 10, 11, 16, 23, len(request) - 1):
            damaged = bytearray(request)
            damaged[position] ^= 1
            try:
                _check(bytes(damaged), write)
            except RuntimeError:
                pass
            else:
                raise RuntimeError("retry budget oracle accepted wire mutation")


def run_retry_budgets(root: Path) -> None:
    _self_test()
    cases = 0
    for mode in ("read", "raw", "raw-opt-in", "write", "write-opt-in"):
        for budget in (0, 1, 2, 4):
            for drops in (budget, budget + 1):
                errors: list[Exception] = []
                with socket.socket() as listener:
                    listener.bind(("127.0.0.1", 0))
                    listener.listen(8)
                    listener.settimeout(4)
                    worker = threading.Thread(
                        target=_serve, args=(listener, mode, budget, drops, errors)
                    )
                    worker.start()
                    try:
                        outcome = subprocess.run(
                            [
                                str(root / ".lake/build/bin/lean-s7"),
                                "integration-retry-budgets",
                                "127.0.0.1",
                                str(listener.getsockname()[1]),
                                mode,
                                str(budget),
                                str(drops),
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
                        raise RuntimeError("retry-budget peer did not terminate")
                    if errors:
                        raise errors[0]
                    if outcome.returncode:
                        raise RuntimeError(
                            f"native retry budget failed: {outcome.stdout}{outcome.stderr}"
                        )
                    print(outcome.stdout.strip())
                    cases += 1
    print(f"retry-budget campaign passed: {cases} conversations")


if __name__ == "__main__":
    run_retry_budgets(Path(__file__).resolve().parents[1])
