"""Slow independent peers for shared chunk, batch, download, and retry budgets."""

from __future__ import annotations

import select
import socket
import struct
import subprocess
import threading
from pathlib import Path

from transfer_deadlines import _ack, _delay, _disconnected, _receive, _request, _send


def _handshake(listener: socket.socket) -> socket.socket:
    connection, _ = listener.accept()
    connection.settimeout(3)
    cr = _receive(connection)
    _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
    setup = _request(connection)
    reference = int.from_bytes(setup[4:6], "big")
    _send(
        connection,
        b"\x02\xf0\x80" + _ack(reference, bytes([0xF0, 0, 0, 1, 0, 1, 0, 240])),
    )
    return connection


def _job(reference: int, function: int) -> bytes:
    parameters = bytes([function]) + bytes(7) + b"\x09_0A00001P"
    return (
        struct.pack(">BBHHHH", 0x32, 1, 0, reference, len(parameters), 0) + parameters
    )


def _next_request(connection: socket.socket) -> bytes | None:
    frame = _receive(connection)
    if len(frame) >= 2 and frame[1] == 0x80:
        # Expiration between a reply and the next request is also legitimate;
        # the Lean command independently checks the expected outcome.
        _disconnected(frame)
        return None
    if frame[:3] != b"\x02\xf0\x80":
        raise RuntimeError("expected extended deadline S7 request")
    return frame[3:]


def _download(connection: socket.socket, interval: float) -> None:
    start = _request(connection)
    if start[10] != 0x1A:
        raise RuntimeError("expected deadline REQUEST_DOWNLOAD")
    _send(
        connection, b"\x02\xf0\x80" + _ack(int.from_bytes(start[4:6], "big"), b"\x1a")
    )
    block = bytearray(b"\xaa" * 1000)
    block[34:36] = (964).to_bytes(2, "big")
    received = bytearray()
    reference = 0x7000
    while len(received) < len(block):
        if not _delay(connection, interval):
            return
        _send(connection, b"\x02\xf0\x80" + _job(reference, 0x1B))
        response = _next_request(connection)
        if response is None:
            return
        if response[1] != 3 or int.from_bytes(response[4:6], "big") != reference:
            raise RuntimeError("invalid deadline download fragment reference")
        parameter_size = int.from_bytes(response[6:8], "big")
        data = response[12 + parameter_size :]
        if data[2:4] != b"\x00\xfb" or int.from_bytes(data[:2], "big") != len(data) - 4:
            raise RuntimeError("invalid deadline download fragment data")
        received.extend(data[4:])
        reference += 1
    if received != block:
        raise RuntimeError("deadline download changed block data")
    if not _delay(connection, interval):
        return
    _send(connection, b"\x02\xf0\x80" + _job(reference, 0x1C))
    ended = _request(connection)
    if ended[12:] != b"\x1c":
        raise RuntimeError("invalid deadline DOWNLOAD_ENDED acknowledgment")
    insert = _request(connection)
    if b"_INSE" not in insert:
        raise RuntimeError("deadline download did not insert block")
    if not _delay(connection, interval):
        return
    _send(
        connection, b"\x02\xf0\x80" + _ack(int.from_bytes(insert[4:6], "big"), b"\x28")
    )
    _disconnected(_receive(connection))


def _memory(connection: socket.socket, operation: str, interval: float) -> None:
    total = 800 if "multi" in operation else 1000
    completed = 0
    while completed < total:
        request = _next_request(connection)
        if request is None:
            return
        function, count = request[10:12]
        expected_function = 5 if operation.startswith("write") else 4
        if function != expected_function or len(request) > 240:
            raise RuntimeError("invalid memory deadline request")
        reference = int.from_bytes(request[4:6], "big")
        parameters_size = int.from_bytes(request[6:8], "big")
        response_data = bytearray()
        data_offset = 10 + parameters_size
        for index in range(count):
            spec = request[12 + index * 12 : 24 + index * 12]
            size = int.from_bytes(spec[4:6], "big")
            if size == 0:
                raise RuntimeError("zero-sized deadline memory item")
            completed += size
            if function == 4:
                response_data += struct.pack(">BBH", 0xFF, 4, size * 8) + b"\xaa" * size
                if index + 1 < count and size % 2:
                    response_data.append(0)
            else:
                data = request[data_offset : data_offset + 4 + size]
                if data != struct.pack(">BBH", 0, 4, size * 8) + b"\xaa" * size:
                    raise RuntimeError("deadline write payload changed")
                data_offset += 4 + size + (size % 2 if index + 1 < count else 0)
                response_data.append(0xFF)
        delay = (
            0.01
            if operation.endswith("-continuation-retry") and completed == size
            else interval
        )
        if not _delay(connection, delay):
            return
        if operation in ("read-retry", "write-retry") and interval >= 0.2:
            raise RuntimeError("reconnect refreshed the already-spent transfer budget")
        _send(
            connection,
            b"\x02\xf0\x80" + _ack(reference, bytes([function, count]), response_data),
        )
    if completed != total:
        raise RuntimeError("memory deadline transfer coverage mismatch")
    _disconnected(_receive(connection))


def _serve(
    listener: socket.socket,
    operation: str,
    interval: float,
    zero: bool,
    errors: list[Exception],
) -> None:
    try:
        connection = _handshake(listener)
        if operation.endswith("-retry") and not operation.endswith(
            "-continuation-retry"
        ):
            # Spend most of the whole budget before the initial retry. A fresh
            # budget after reconnect would allow the complete transfer to finish.
            with connection:
                _request(connection)
                if not _delay(connection, 0.23):
                    return
            connection = _handshake(listener)
        with connection:
            if zero:
                _disconnected(_receive(connection))
            elif operation == "download":
                _download(connection, interval)
            else:
                _memory(connection, operation, interval)
        # Retrying a continuation is forbidden: another connection is a failure.
        if select.select([listener], [], [], 0.05)[0]:
            extra, _ = listener.accept()
            extra.close()
            raise RuntimeError("deadline transfer retried after a continuation")
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_extended_deadlines(root: Path) -> None:
    for operation in (
        "read",
        "write",
        "readmulti",
        "writemulti",
        "download",
        "read-retry",
        "write-retry",
        "read-continuation-retry",
        "write-continuation-retry",
        "read-invalid-range",
        "write-invalid-range",
    ):
        cases = [(250, "420", 0.15, "timeout"), (250, "600", 0.01, "accept")]
        if operation.endswith("-invalid-range"):
            cases = [(250, "600", 0, "invalid-input")]
        elif operation.endswith("-continuation-retry"):
            cases = [(120, "600", 0.25, "timeout")]
        elif operation.endswith("-retry"):
            # The peer closes the first connection after 230 ms. A 250 ms
            # exchange limit leaves only 20 ms to observe EOF: a slow runner
            # can time out and disconnect the peer before it reaches its
            # reconnect handshake. Keep the short shared-transfer rejection
            # budget, but give the exchange/positive controls genuine slack.
            cases = [(1000, "420", 0.23, "timeout"), (1000, "2000", 0.01, "accept")]
        else:
            cases += [
                (250, "0", 0, "timeout"),
                (120, "none", 0.25, "timeout"),
                (250, "none", 0.15, "accept"),
            ]
        if operation == "download":
            # Five fragments plus DOWNLOAD_ENDED complete in 600ms. The
            # insertion acknowledgment still belongs to the initial budget.
            cases.append((250, "680", 0.1, "timeout"))
        for operation_ms, transfer_ms, interval, expected in cases:
            errors: list[Exception] = []
            with socket.socket() as listener:
                listener.bind(("127.0.0.1", 0))
                listener.listen(2)
                listener.settimeout(3)
                thread = threading.Thread(
                    target=_serve,
                    args=(
                        listener,
                        operation,
                        interval,
                        transfer_ms == "0" or operation.endswith("-invalid-range"),
                        errors,
                    ),
                )
                thread.start()
                subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-transfer-deadline",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        operation,
                        str(operation_ms),
                        transfer_ms,
                        expected,
                    ],
                    cwd=root,
                    check=True,
                    timeout=10,
                )
                thread.join(timeout=3)
            if thread.is_alive():
                raise RuntimeError(
                    f"extended deadline peer did not finish: {operation}"
                )
            if errors:
                raise errors[0]
