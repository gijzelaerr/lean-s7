"""Barrier-synchronized peers for serialized operations and lifecycle races."""

from __future__ import annotations

import select
import socket
import struct
import subprocess
import threading
from pathlib import Path

from multi_batching import _ack, _receive, _request, _send


def _handshake(connection: socket.socket) -> None:
    connection.settimeout(5)
    cr = _receive(connection)
    _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
    setup = _request(connection)
    reference = int.from_bytes(setup[4:6], "big")
    _send(connection, b"\x02\xf0\x80" + _ack(reference, b"\xf0\0\0\x01\0\x01\0\xf0"))


def _serve(
    listener: socket.socket,
    mode: str,
    pending: threading.Event,
    release: threading.Event,
    errors: list[Exception],
) -> None:
    stage = "accept"
    try:
        connection, _ = listener.accept()
        completed: set[int] = set()
        active: int | None = None
        next_offset = 0
        first = True
        references: set[int] = set()
        try:
            stage = "handshake"
            _handshake(connection)
            while True:
                stage = "next request"
                frame = _receive(connection)
                if len(frame) >= 2 and frame[1] == 0x80:
                    if active is not None:
                        raise RuntimeError("disconnect interleaved an active transfer")
                    break
                if frame[:3] != b"\x02\xf0\x80":
                    raise RuntimeError("unexpected concurrency frame")
                request = frame[3:]
                if len(request) != 24 or request[10:16] != b"\x04\x01\x12\x0a\x10\x02":
                    raise RuntimeError("unexpected concurrent read codec")
                reference = int.from_bytes(request[4:6], "big")
                count = int.from_bytes(request[16:18], "big")
                address = int.from_bytes(request[21:24], "big")
                if address % 8:
                    raise RuntimeError("unaligned concurrent byte read")
                index, offset = divmod(address // 8, 1000)
                if first:
                    if index != 0 or offset != 0:
                        raise RuntimeError(
                            "first operation was not the synchronized read"
                        )
                    pending.set()
                    if not release.wait(5):
                        raise RuntimeError(
                            "concurrency process barrier did not release"
                        )
                    first = False
                    if mode == "failure":
                        _send(
                            connection, b"\x02\xf0\x80" + _ack(reference, b"\x05\x01")
                        )
                        # A malformed reply closes the session. Queued operations
                        # must not send any additional read or reconnect.
                        try:
                            leftover = _receive(connection)
                        except RuntimeError as error:
                            if "closed an incomplete frame" not in str(error):
                                raise
                            leftover = b""
                        if leftover and (len(leftover) < 2 or leftover[1] != 0x80):
                            raise RuntimeError(
                                f"queued read sent after protocol failure: {leftover.hex()}"
                            )
                        break
                    if mode == "reconnect":
                        connection.close()
                        connection, _ = listener.accept()
                        _handshake(connection)
                        retried = _request(connection)
                        if retried != request:
                            raise RuntimeError("reconnect changed the original read")
                if reference in references:
                    raise RuntimeError("concurrent requests reused a reference")
                references.add(reference)
                if active is None:
                    if offset or index in completed or not 0 <= index < 16:
                        raise RuntimeError("duplicate/out-of-order logical read")
                    active = index
                    next_offset = 0
                if active != index or offset != next_offset:
                    raise RuntimeError("concurrent chunked transfers interleaved")
                if count != min(222, 700 - offset):
                    raise RuntimeError("concurrent read chunk length mismatch")
                payload = bytes(
                    (index * 19 + value * 37) % 256
                    for value in range(offset, offset + count)
                )
                data = struct.pack(">BBH", 0xFF, 4, count * 8) + payload
                _send(connection, b"\x02\xf0\x80" + _ack(reference, b"\x04\x01", data))
                next_offset += count
                if next_offset == 700:
                    completed.add(index)
                    active = None
            if mode in ("success", "reconnect") and completed != set(range(16)):
                raise RuntimeError("concurrency peer lost an operation")
            if mode == "disconnect" and 0 not in completed:
                raise RuntimeError(
                    "disconnect interrupted its earlier active operation"
                )
        finally:
            connection.close()
        # Listen remains open: any resurrection/reconnect after close is a
        # client failure and also makes the subprocess fail its late-read check.
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(RuntimeError(f"concurrency {mode} at {stage}: {error}"))
        pending.set()


def run_concurrency(
    root: Path,
    modes: tuple[str, ...] = ("success", "failure", "disconnect", "reconnect"),
) -> None:
    for mode in modes:
        errors: list[Exception] = []
        pending, release = threading.Event(), threading.Event()
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(4)
            listener.settimeout(5)
            thread = threading.Thread(
                target=_serve, args=(listener, mode, pending, release, errors)
            )
            thread.start()
            process = subprocess.Popen(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "integration-concurrency",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                    mode,
                ],
                cwd=root,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            try:
                if not pending.wait(5) or errors:
                    if process.poll() is not None:
                        stdout, stderr = process.communicate()
                        raise RuntimeError(
                            f"concurrency {mode} exited before barrier: {stdout}{stderr}"
                        )
                    raise RuntimeError(
                        f"concurrency {mode} did not reach its first request: {errors}"
                    )
                assert process.stdin is not None and process.stdout is not None
                process.stdin.write("launch\n")
                process.stdin.flush()
                # This line is emitted only after the competing tasks and
                # disconnect task have been created, while reply one is held.
                if not select.select([process.stdout], [], [], 5)[0]:
                    raise RuntimeError(
                        "concurrency process did not launch its queued calls"
                    )
                launched = process.stdout.readline()
                if launched.strip() != "concurrency calls launched":
                    raise RuntimeError(f"unexpected concurrency barrier: {launched!r}")
                release.set()
                stdout, stderr = process.communicate(timeout=15)
                if process.returncode:
                    raise RuntimeError(f"concurrency {mode} failed: {stdout}{stderr}")
                print(stdout.strip())
            finally:
                release.set()
                if process.poll() is None:
                    process.kill()
                    process.communicate()
                thread.join(timeout=6)
            if thread.is_alive():
                raise RuntimeError("concurrency peer did not terminate")
            if errors:
                raise errors[0]
