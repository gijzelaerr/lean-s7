"""Admission-barrier peers for FIFO lifecycle, gate release, and no resurrection."""

from __future__ import annotations

import os
import select
import socket
import struct
import subprocess
import threading
from pathlib import Path

from concurrency import _handshake
from multi_batching import _ack, _receive, _request, _send


def _check_read(request: bytes, index: int, offset: int) -> tuple[int, int]:
    count = min(222, 700 - offset)
    expected_parameters = (
        b"\x04\x01\x12\x0a\x10\x02"
        + struct.pack(">HHB", count, 1, 0x84)
        + ((index * 1000 + offset) * 8).to_bytes(3, "big")
    )
    if (
        len(request) != 24
        or request[:4] != b"\x32\x01\0\0"
        or request[6:10] != b"\0\x0e\0\0"
        or request[10:] != expected_parameters
    ):
        raise RuntimeError(
            f"queued read reordered/interleaved at {index}:{offset}: {request.hex()}"
        )
    return int.from_bytes(request[4:6], "big"), count


def _serve(
    listener: socket.socket,
    mode: str,
    pending: threading.Event,
    release: threading.Event,
    errors: list[Exception],
) -> None:
    stage = "accept"
    connection: socket.socket | None = None
    try:
        connection, _ = listener.accept()
        stage = "initial handshake"
        _handshake(connection)
        first = _request(connection)
        if mode == "write-drop":
            expected = b"\x05\x01\x12\x0a\x10\x02\0\x01\0\x01\x84\0\0\0\0\x04\0\x08\x2a"
            if first[10:] != expected or first[6:10] != b"\0\x0e\0\x05":
                raise RuntimeError(f"unexpected queued mutation: {first.hex()}")
        else:
            _check_read(first, 0, 0)
        pending.set()
        stage = "gate admission barrier"
        if not release.wait(5):
            raise RuntimeError("six operations did not enter the client gate")
        if mode == "write-drop":
            connection.close()
            connection = None
        elif mode == "protocol":
            reference = int.from_bytes(first[4:6], "big")
            _send(connection, b"\x02\xf0\x80" + _ack(reference, b"\x05\x01"))
            # Decode failure closes before the queued reads can acquire the gate.
            stage = "terminal protocol closure"
            close = _receive(connection)
            if len(close) < 2 or close[1] != 0x80:
                raise RuntimeError(
                    f"queued call sent after protocol failure: {close.hex()}"
                )
        else:
            if mode == "reconnect":
                connection.close()
                connection, _ = listener.accept()
                stage = "retry handshake"
                _handshake(connection)
                if _request(connection) != first:
                    raise RuntimeError(
                        "retry changed the active read or overtook its queue"
                    )
            indices = [0, 2] if mode == "invalid" else [0, 1, 2]
            references: set[int] = set()
            for index in indices:
                offset = 0
                while offset < 700:
                    stage = f"read {index}:{offset}"
                    request = (
                        first if index == 0 and offset == 0 else _request(connection)
                    )
                    reference, count = _check_read(request, index, offset)
                    if reference in references:
                        raise RuntimeError("queued requests reused a reference")
                    references.add(reference)
                    if mode == "plc" and index == 0:
                        packet = bytearray(_ack(reference, b"\x04\x01"))
                        packet[10:12] = b"\x81\x04"
                        _send(connection, b"\x02\xf0\x80" + packet)
                        break
                    payload = bytes(
                        (index * 23 + value * 31) % 256
                        for value in range(offset, offset + count)
                    )
                    data = struct.pack(">BBH", 0xFF, 4, count * 8) + payload
                    _send(
                        connection, b"\x02\xf0\x80" + _ack(reference, b"\x04\x01", data)
                    )
                    offset += count
            stage = "FIFO explicit closure"
            close = _receive(connection)
            if len(close) < 2 or close[1] != 0x80:
                raise RuntimeError(
                    f"explicit close overtaken by a queued call: {close.hex()}"
                )
        if connection is not None:
            # The second admitted disconnect must not send another frame.
            stage = "closed socket drain"
            if connection.recv(1):
                raise RuntimeError("closed client sent an additional frame")
            connection.close()
            connection = None
        # A listening independent peer detects retries/resurrection that never
        # reach a handshake; subprocess lifecycle checks independently fail them.
        stage = "no resurrection"
        listener.settimeout(0.3)
        try:
            unexpected, _ = listener.accept()
        except TimeoutError:
            return
        unexpected.close()
        raise RuntimeError("queued call reconnected after terminal failure/closure")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(RuntimeError(f"queued lifecycle {mode} at {stage}: {error}"))
        pending.set()
    finally:
        if connection is not None:
            connection.close()


def run_queued_lifecycle(root: Path) -> None:
    modes = ("disconnect", "reconnect", "protocol", "plc", "invalid", "write-drop")
    # This sets the native pool's initial configuration, not a hard thread cap.
    for worker_count in (None, "2"):
        for mode in modes:
            errors: list[Exception] = []
            pending, release = threading.Event(), threading.Event()
            with socket.socket() as listener:
                listener.bind(("127.0.0.1", 0))
                listener.listen(4)
                listener.settimeout(5)
                worker = threading.Thread(
                    target=_serve, args=(listener, mode, pending, release, errors)
                )
                worker.start()
                environment = os.environ.copy()
                if worker_count is not None:
                    environment["LEAN_NUM_THREADS"] = worker_count
                process = subprocess.Popen(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-queued-lifecycle",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        mode,
                    ],
                    cwd=root,
                    env=environment,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                )
                try:
                    if not pending.wait(5) or errors:
                        raise RuntimeError(
                            f"queued lifecycle first request missing: {errors}"
                        )
                    assert process.stdin is not None and process.stdout is not None
                    process.stdin.write("admit\n")
                    process.stdin.flush()
                    if not select.select([process.stdout], [], [], 5)[0]:
                        raise RuntimeError(
                            "queued lifecycle gate admission output missing"
                        )
                    admitted = process.stdout.readline()
                    if admitted.strip() != "queued lifecycle admitted 6":
                        raise RuntimeError(
                            f"unexpected lifecycle barrier: {admitted!r}"
                        )
                    release.set()
                    stdout, stderr = process.communicate(timeout=15)
                    if process.returncode:
                        raise RuntimeError(
                            f"queued lifecycle {mode} failed: {stdout}{stderr}"
                        )
                    print(
                        f"{stdout.strip()} (initial workers {worker_count or 'default'})"
                    )
                finally:
                    release.set()
                    if process.poll() is None:
                        process.kill()
                        process.communicate()
                    worker.join(timeout=6)
                if worker.is_alive():
                    raise RuntimeError("queued lifecycle peer did not terminate")
                if errors:
                    raise errors[0]
