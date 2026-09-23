"""Read-only full-stack clock peers for every packed decimal millisecond digit."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path

from concurrency import _handshake
from multi_batching import _receive, _request, _send


def _serve(listener: socket.socket, digit: int, errors: list[Exception]) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            _handshake(connection)
            connection.settimeout(3)
            request = _request(connection)
            if (
                len(request) != 22
                or request[:4] != b"\x32\x07\0\0"
                or request[6:10] != b"\0\x08\0\x04"
                or request[10:] != b"\0\x01\x12\x04\x11\x47\x01\0\x0a\0\0\0"
            ):
                raise RuntimeError(
                    f"clock peer expected read-only clock query: {request.hex()}"
                )
            # All calendar, time, complete-BCD, and weekday fields remain valid.
            # A–F used to decode into plausible 130–135 milliseconds instead.
            weekday = digit % 7 + 1
            payload = bytes(
                [
                    0,
                    0x19,
                    0x24,
                    0x02,
                    0x29,
                    0x23,
                    0x59,
                    0x58,
                    0x12,
                    digit * 16 + weekday,
                ]
            )
            parameters = b"\0\x01\x12\x08\x12\x87\x01\x01\x01\0\0\0"
            data = b"\xff\x09" + struct.pack(">H", len(payload)) + payload
            reference = int.from_bytes(request[4:6], "big")
            header = struct.pack(
                ">BBHHHH", 0x32, 7, 0, reference, len(parameters), len(data)
            )
            _send(connection, b"\x02\xf0\x80" + header + parameters + data)
            frame = _receive(connection)
            if len(frame) < 2 or frame[1] != 0x80:
                raise RuntimeError(
                    "clock peer saw a later read after malformed typed reply"
                )
            try:
                extra = connection.recv(1)
            except ConnectionResetError:
                extra = b""
            if extra:
                raise RuntimeError("closed clock client sent another frame")
        listener.settimeout(0.15)
        try:
            unexpected, _ = listener.accept()
        except TimeoutError:
            return
        unexpected.close()
        raise RuntimeError(
            "clock protocol rejection reconnected despite terminal failure"
        )
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(error)


def run_clock_assurance(root: Path) -> None:
    for digit in range(16):
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(2)
            listener.settimeout(4)
            worker = threading.Thread(target=_serve, args=(listener, digit, errors))
            worker.start()
            try:
                outcome = subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-clock-assurance",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        str(digit),
                    ],
                    cwd=root,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=8,
                )
            finally:
                worker.join(timeout=6)
            if worker.is_alive():
                raise RuntimeError(f"clock assurance peer hung: packed digit {digit}")
            if errors:
                raise RuntimeError(
                    f"clock assurance peer failed: packed digit {digit}"
                ) from errors[0]
            if outcome.returncode:
                raise RuntimeError(
                    f"clock assurance client failed: {outcome.stdout}{outcome.stderr}"
                )
    print(
        "clock full-stack peers passed: 10 decimal controls and 6 nondecimal rejections"
    )
