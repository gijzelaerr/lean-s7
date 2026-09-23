"""Independent raw TCP peers for finite COTP work and pre-body framing limits."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path


def _frame(payload: bytes, final: bool, reserved: int = 0) -> bytes:
    body = bytes([2, 0xF0, 0x80 if final else 0]) + payload
    return struct.pack(">BBH", 3, reserved, len(body) + 4) + body


def _serve(listener: socket.socket, mode: str, errors: list[Exception]) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(3)
            if mode in ("exact", "reserved"):
                reserved = 255 if mode == "reserved" else 0
                connection.sendall(
                    b"".join(
                        _frame(bytes([index + 1]), index == 2, reserved)
                        for index in range(3)
                    )
                )
            elif mode in ("empty", "tiny"):
                # No fourth header or EOF: rejection must occur at the bound.
                connection.sendall(
                    b"".join(
                        _frame(b"" if mode == "empty" else b"x", False)
                        for _ in range(3)
                    )
                )
            elif mode == "version":
                connection.sendall(struct.pack(">BBH", 4, 0, 65535))
            elif mode == "short":
                connection.sendall(struct.pack(">BBH", 3, 0, 6))
            elif mode == "oversized":
                connection.sendall(struct.pack(">BBH", 3, 0, 65535))
            elif mode == "remaining":
                connection.sendall(_frame(b"xy", False))
                # Remaining payload budget is one; body claims two plus DT header.
                connection.sendall(struct.pack(">BBH", 3, 0, 9))
            elif mode != "zero":
                raise RuntimeError(f"unknown transport resource mode: {mode}")
            # For header-only and zero-budget cases, the peer withholds all body
            # bytes. Successful shutdown proves rejection did not await them.
            if connection.recv(1):
                raise RuntimeError("raw transport test sent unexpected data")
    except (OSError, RuntimeError) as error:
        errors.append(error)


def run_transport_resources() -> None:
    executable = Path(__file__).resolve().parents[1] / ".lake/build/bin/lean-s7"
    for mode in (
        "exact",
        "reserved",
        "empty",
        "tiny",
        "zero",
        "version",
        "short",
        "oversized",
        "remaining",
    ):
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            listener.settimeout(4)
            thread = threading.Thread(target=_serve, args=(listener, mode, errors))
            thread.start()
            outcome = subprocess.run(
                [
                    str(executable),
                    "integration-transport-resources",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                    mode,
                ],
                check=False,
                capture_output=True,
                text=True,
                timeout=6,
            )
            thread.join(5)
            if thread.is_alive():
                raise RuntimeError(f"transport resource peer hung: {mode}")
            if errors:
                raise RuntimeError(
                    f"transport resource peer failed: {mode}"
                ) from errors[0]
            if outcome.returncode:
                raise RuntimeError(outcome.stdout + outcome.stderr)
            print(outcome.stdout.strip())


if __name__ == "__main__":
    run_transport_resources()
