"""Independent slow peers: exchange deadlines must not refresh transfer budgets."""

from __future__ import annotations

import select
import socket
import struct
import subprocess
import threading
from pathlib import Path


def _exact(connection: socket.socket, size: int) -> bytes:
    result = bytearray()
    while len(result) < size:
        chunk = connection.recv(size - len(result))
        if not chunk:
            raise RuntimeError("deadline client closed an incomplete frame")
        result.extend(chunk)
    return bytes(result)


def _receive(connection: socket.socket) -> bytes:
    version, reserved, size = struct.unpack(">BBH", _exact(connection, 4))
    if version != 3 or reserved != 0 or size < 4:
        raise RuntimeError("invalid deadline-test TPKT")
    return _exact(connection, size - 4)


def _send(connection: socket.socket, payload: bytes) -> None:
    connection.sendall(struct.pack(">BBH", 3, 0, len(payload) + 4) + payload)


def _request(connection: socket.socket) -> bytes:
    frame = _receive(connection)
    if frame[:3] != bytes([2, 0xF0, 0x80]):
        raise RuntimeError("expected deadline-test S7 request")
    return frame[3:]


def _ack(reference: int, parameters: bytes, data: bytes = b"") -> bytes:
    return (
        struct.pack(
            ">BBHHHHBB", 0x32, 3, 0, reference, len(parameters), len(data), 0, 0
        )
        + parameters
        + data
    )


def _userdata(reference: int, operation: str, index: int, chunk: bytes) -> bytes:
    group, subfunction = (4, 1) if operation == "szl" else (3, 2)
    parameters = bytes([0, 1, 0x12, 8, 0x12, 0x80 | group, subfunction, 7, 0])
    parameters += bytes([int(index < 3), 0, 0])
    if operation == "szl" and index == 0:
        chunk = bytes([4, 0x24, 0, 0]) + chunk
    data = bytes([0xFF, 9]) + len(chunk).to_bytes(2, "big") + chunk
    return (
        struct.pack(">BBHHHH", 0x32, 7, 0, reference, len(parameters), len(data))
        + parameters
        + data
    )


def _disconnected(frame: bytes) -> None:
    if len(frame) != 7 or frame[:2] != b"\x06\x80":
        raise RuntimeError(
            "deadline client sent another request instead of disconnecting"
        )


def _decode_next_request(frame: bytes) -> bytes | None:
    # Expiry can occur after a reply, before the next continuation is sent.
    # Only a complete DR is an allowed alternative; malformed frames still fail.
    if len(frame) >= 2 and frame[1] == 0x80:
        _disconnected(frame)
        return None
    if len(frame) < 13 or frame[:3] != b"\x02\xf0\x80":
        raise RuntimeError("expected deadline-test S7 request or disconnect")
    return frame[3:]


def _next_request(connection: socket.socket) -> bytes | None:
    return _decode_next_request(_receive(connection))


def _self_test() -> None:
    request = b"\x32\x01" + bytes(8)
    if _decode_next_request(b"\x02\xf0\x80" + request) != request:
        raise AssertionError("deadline peer changed an ordinary request")
    dr = b"\x06\x80\0\x01\0\x02\0"
    if _decode_next_request(dr) is not None:
        raise AssertionError("deadline peer rejected between-exchange disconnect")
    for frame in (
        b"",
        b"\x06\x80",
        dr[:-1],
        dr + b"\0",
        b"\x05" + dr[1:],
        b"\x02\xf0\x80",
    ):
        try:
            _decode_next_request(frame)
        except RuntimeError:
            continue
        raise AssertionError("deadline peer accepted a malformed frame")


def _delay(connection: socket.socket, interval: float) -> bool:
    # Do not send after timeout, and do not close the socket to cause the timeout.
    # A refreshed cleanup exchange would be a test failure, not silently ignored.
    readable, _, _ = select.select([connection], [], [], interval)
    if readable:
        _disconnected(_receive(connection))
        return False
    return True


def _serve(
    listener: socket.socket,
    operation: str,
    interval: float,
    no_request: bool,
    errors: list[Exception],
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(3)
            cr = _receive(connection)
            _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
            setup = _request(connection)
            reference = int.from_bytes(setup[4:6], "big")
            _send(
                connection,
                bytes([2, 0xF0, 0x80])
                + _ack(reference, bytes([0xF0, 0, 0, 1, 0, 1, 1, 0xE0])),
            )
            if no_request:
                _disconnected(_receive(connection))
                return
            if operation == "upload":
                start = _next_request(connection)
                if start is None:
                    return
                if start[10] != 0x1D:
                    raise RuntimeError("expected START_UPLOAD")
                reference = int.from_bytes(start[4:6], "big")
                parameters = bytes([0x1D, 0, 0, 0, 0, 0, 0, 1, 7, 0, 5]) + b"00004"
                _send(connection, bytes([2, 0xF0, 0x80]) + _ack(reference, parameters))
            payload = (
                bytes([0, 1, 0, 4, 0xAA, 0xBB, 0xCC, 0xDD])
                if operation == "szl"
                else bytes([0, 1, 0x10, 2])
            )
            for index in range(4):
                request = _next_request(connection)
                if request is None:
                    return
                reference = int.from_bytes(request[4:6], "big")
                if operation == "upload":
                    if request[10] != 0x1E or request[17] != 1:
                        raise RuntimeError("invalid UPLOAD request")
                    response = _ack(
                        reference,
                        bytes([0x1E, int(index < 3)]),
                        bytes([0, 1, 0, 0xFB, 0xAA + 0x11 * index]),
                    )
                else:
                    group, subfunction = (4, 1) if operation == "szl" else (3, 2)
                    if request[15:17] != bytes([0x40 | group, subfunction]):
                        raise RuntimeError("invalid segmented USER_DATA request")
                    if index > 0 and request[17] != 7:
                        raise RuntimeError("invalid continuation sequence")
                    chunk_size = 2 if operation == "szl" else 1
                    response = _userdata(
                        reference,
                        operation,
                        index,
                        payload[chunk_size * index : chunk_size * (index + 1)],
                    )
                if not _delay(connection, interval):
                    return
                _send(connection, bytes([2, 0xF0, 0x80]) + response)
            if operation == "upload":
                end = _next_request(connection)
                if end is None:
                    return
                if end[10] != 0x1F or end[17] != 1:
                    raise RuntimeError("invalid END_UPLOAD request")
                if not _delay(connection, interval):
                    return
                reference = int.from_bytes(end[4:6], "big")
                _send(connection, bytes([2, 0xF0, 0x80]) + _ack(reference, b"\x1f"))
            _disconnected(_receive(connection))
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_transfer_deadlines(root: Path) -> None:
    _self_test()
    for operation in ("upload", "szl", "userdata"):
        cases = [
            (250, "0", 0, "timeout"),
            (250, "420", 0.15, "timeout"),
            (120, "600", 0.25, "timeout"),
            (120, "none", 0.25, "timeout"),
            # Success is a protocol control, not a scheduler-latency assertion.
            # Preserve the short timeout controls above; allow hosted runners
            # slack when the configured peer delay must complete successfully.
            (1000, "2000", 0.015, "accept"),
            (1000, "none", 0.15, "accept"),
        ]
        if operation == "upload":
            # Four fragments finish at 600ms; END_UPLOAD must use the same
            # absolute budget instead of buying another 250ms for its ACK.
            cases.append((250, "700", 0.15, "timeout"))
        for operation_ms, transfer_ms, interval, expected in cases:
            errors: list[Exception] = []
            with socket.socket() as listener:
                listener.bind(("127.0.0.1", 0))
                listener.listen(1)
                thread = threading.Thread(
                    target=_serve,
                    args=(listener, operation, interval, transfer_ms == "0", errors),
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
                    f"transfer deadline peer did not finish: {operation}"
                )
            if errors:
                raise errors[0]
