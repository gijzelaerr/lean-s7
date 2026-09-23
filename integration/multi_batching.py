"""Independent multi-item peers checking ordered batching and per-item failures."""

from __future__ import annotations

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
            raise RuntimeError("multi-batching client closed an incomplete frame")
        result.extend(chunk)
    return bytes(result)


def _receive(connection: socket.socket) -> bytes:
    version, reserved, size = struct.unpack(">BBH", _exact(connection, 4))
    if version != 3 or reserved != 0 or size < 4:
        raise RuntimeError("invalid multi-batching TPKT")
    return _exact(connection, size - 4)


def _send(connection: socket.socket, payload: bytes) -> None:
    connection.sendall(struct.pack(">BBH", 3, 0, len(payload) + 4) + payload)


def _request(connection: socket.socket) -> bytes:
    frame = _receive(connection)
    if frame[:3] != bytes([2, 0xF0, 0x80]):
        raise RuntimeError("expected multi-batching S7 request")
    return frame[3:]


def _ack(reference: int, parameters: bytes, data: bytes = b"") -> bytes:
    return (
        struct.pack(
            ">BBHHHHBB", 0x32, 3, 0, reference, len(parameters), len(data), 0, 0
        )
        + parameters
        + data
    )


def _serve(
    listener: socket.socket,
    pdu_length: int,
    item_count: int,
    item_size: int,
    errors: list[Exception],
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(4)
            cr = _receive(connection)
            _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
            setup = _request(connection)
            if setup[10] != 0xF0:
                raise RuntimeError("expected multi-batching SETUP")
            reference = int.from_bytes(setup[4:6], "big")
            _send(
                connection,
                bytes([2, 0xF0, 0x80])
                + _ack(
                    reference,
                    bytes([0xF0, 0, 0, 1, 0, 1]) + struct.pack(">H", pdu_length),
                ),
            )
            for function in (5, 4):
                completed = 0
                batches = 0
                while completed < item_count:
                    request = _request(connection)
                    if len(request) > pdu_length or request[:2] != bytes([0x32, 1]):
                        raise RuntimeError(
                            "multi-batching request exceeded negotiated PDU"
                        )
                    reference, parameters_size, data_size = struct.unpack(
                        ">HHH", request[4:10]
                    )
                    if len(request) != 10 + parameters_size + data_size:
                        raise RuntimeError("multi-batching request length mismatch")
                    if request[10] != function:
                        raise RuntimeError(
                            "multi-batching request function/order mismatch"
                        )
                    if function == 4 and data_size != 0:
                        raise RuntimeError(
                            "multi-batching read request had unexpected data"
                        )
                    count = request[11]
                    expected = min(20, item_count - completed)
                    if function == 5:
                        expected = min(
                            expected,
                            (pdu_length - 12) // (16 + item_size + item_size % 2),
                        )
                    else:
                        expected = min(
                            expected,
                            (pdu_length - 12) // 12,
                            (pdu_length - 14) // (4 + item_size + item_size % 2),
                        )
                    if count != expected or parameters_size != 2 + 12 * count:
                        raise RuntimeError(
                            "multi-batching count did not match independent budget"
                        )
                    data_offset = 10 + parameters_size
                    response_data = bytearray()
                    for position in range(count):
                        index = completed + position
                        spec = request[12 + position * 12 : 24 + position * 12]
                        address = index * 256 * 8
                        expected_spec = bytes([0x12, 0x0A, 0x10, 2]) + struct.pack(
                            ">HH", item_size, 1
                        )
                        expected_spec += bytes([0x84]) + address.to_bytes(3, "big")
                        if spec != expected_spec:
                            raise RuntimeError(
                                "multi-batching item lost, repeated, or reordered"
                            )
                        failure = index % 7 == 3
                        if function == 5:
                            size = 4 + item_size
                            expected_data = (
                                struct.pack(">BBH", 0, 4, item_size * 8)
                                + bytes([index]) * item_size
                            )
                            if (
                                request[data_offset : data_offset + size]
                                != expected_data
                            ):
                                raise RuntimeError(
                                    "multi-batching write payload changed order"
                                )
                            data_offset += size
                            if position + 1 < count and item_size % 2:
                                if request[data_offset : data_offset + 1] != b"\0":
                                    raise RuntimeError(
                                        "multi-batching write padding mismatch"
                                    )
                                data_offset += 1
                            response_data.append(5 if failure else 0xFF)
                        elif failure:
                            response_data.extend(struct.pack(">BBH", 5, 0, 0))
                        else:
                            response_data.extend(
                                struct.pack(">BBH", 0xFF, 4, item_size * 8)
                            )
                            response_data.extend(bytes([index]) * item_size)
                            if position + 1 < count and item_size % 2:
                                response_data.append(0)
                    if function == 5 and data_offset != len(request):
                        raise RuntimeError(
                            "multi-batching write request had trailing bytes"
                        )
                    response = _ack(
                        reference, bytes([function, count]), bytes(response_data)
                    )
                    if len(response) > pdu_length:
                        raise RuntimeError(
                            "multi-batching peer response exceeded negotiated PDU"
                        )
                    _send(connection, bytes([2, 0xF0, 0x80]) + response)
                    completed += count
                    batches += 1
                if batches < 3:
                    raise RuntimeError(
                        "multi-batching fixture did not exercise multiple boundaries"
                    )
            disconnected = _receive(connection)
            if len(disconnected) < 2 or disconnected[1] != 0x80:
                raise RuntimeError("multi-batching client did not disconnect")
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_multi_batching(root: Path) -> None:
    for pdu_length in (240, 480):
        for item_size in (1, 37):
            errors: list[Exception] = []
            with socket.socket() as listener:
                listener.bind(("127.0.0.1", 0))
                listener.listen(1)
                thread = threading.Thread(
                    target=_serve, args=(listener, pdu_length, 41, item_size, errors)
                )
                thread.start()
                subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-multi-batching",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        str(pdu_length),
                        "41",
                        str(item_size),
                    ],
                    cwd=root,
                    check=True,
                    timeout=10,
                )
                thread.join(timeout=4)
            if thread.is_alive():
                raise RuntimeError("multi-batching peer did not finish")
            if errors:
                raise errors[0]
