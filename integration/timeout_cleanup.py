"""Repeated early timer cancellation and failed COTP connection cleanup."""

from __future__ import annotations

import socket
import subprocess
import threading
from pathlib import Path

from multi_batching import _ack, _receive, _request, _send


def _closed(connection: socket.socket) -> None:
    try:
        data = connection.recv(1)
    except ConnectionResetError:
        # Early framing rejection can leave unread bytes, producing TCP RST.
        return
    if data:
        raise RuntimeError("failed connection continued its handshake")


def _serve(listener: socket.socket, mode: str, errors: list[Exception]) -> None:
    try:
        count = 4 if mode == "stalled" else 24
        for index in range(count):
            connection, _ = listener.accept()
            with connection:
                connection.settimeout(3)
                cr = _receive(connection)
                if len(cr) < 7 or cr[1] != 0xE0:
                    raise RuntimeError("cleanup peer expected COTP connection request")
                if mode == "stalled":
                    _closed(connection)
                    continue
                if index % 3 == 1:
                    _send(connection, b"\x01\xd0")
                    _closed(connection)
                    continue
                _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
                setup = _request(connection)
                _send(
                    connection,
                    b"\x02\xf0\x80"
                    + _ack(
                        int.from_bytes(setup[4:6], "big"), b"\xf0\0\0\x01\0\x01\0\xf0"
                    ),
                )
                frame = _receive(connection)
                if len(frame) < 2 or frame[1] != 0x80:
                    raise RuntimeError("successful connection did not disconnect")
    except (OSError, RuntimeError, ValueError, IndexError) as error:
        errors.append(error)


def run_timeout_cleanup(root: Path) -> None:
    for mode in ("repeated", "stalled"):
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(4)
            listener.settimeout(5)
            worker = threading.Thread(target=_serve, args=(listener, mode, errors))
            worker.start()
            try:
                # Max-budget timers must not keep sleeping native workers alive.
                subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-timeout-cleanup",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        mode,
                    ],
                    cwd=root,
                    check=True,
                    timeout=12,
                )
            except subprocess.TimeoutExpired as error:
                raise RuntimeError(
                    f"cleanup process timed out; peer errors: {errors}"
                ) from error
            finally:
                worker.join(timeout=6)
            if worker.is_alive():
                raise RuntimeError("cleanup peer did not finish")
            if errors:
                raise errors[0]
    print("timeout cleanup peers passed: 28 connection attempts")
