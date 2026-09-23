"""Duplicate caller identities across batching, chunking, and partial failure."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path

from multi_batching import _ack, _receive, _request, _send


def _check(request: bytes, pdu: int, expected: list[tuple[int, bytes]]) -> None:
    count = len(expected)
    addresses = bytearray([5, count])
    data = bytearray()
    for index, (start, payload) in enumerate(expected):
        addresses += b"\x12\x0a\x10\x02" + struct.pack(">HHB", len(payload), 1, 0x84)
        addresses += (start * 8).to_bytes(3, "big")
        data += b"\0\x04" + struct.pack(">H", len(payload) * 8) + payload
        if index + 1 < count and len(payload) % 2:
            data += b"\0"
    if (
        len(request) > pdu
        or request[6:10] != struct.pack(">HH", len(addresses), len(data))
        or request[10:] != addresses + data
    ):
        raise RuntimeError("provenance peer saw changed request/order/padding/PDU")


def _reply(connection: socket.socket, request: bytes, statuses: bytes) -> None:
    _send(
        connection,
        b"\x02\xf0\x80"
        + _ack(
            int.from_bytes(request[4:6], "big"), bytes([5, len(statuses)]), statuses
        ),
    )


def _serve(
    listener: socket.socket, mode: str, pdu: int, errors: list[Exception]
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(4)
            cr = _receive(connection)
            _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
            setup = _request(connection)
            _send(
                connection,
                b"\x02\xf0\x80"
                + _ack(
                    int.from_bytes(setup[4:6], "big"),
                    b"\xf0\0\0\x01\0\x01" + struct.pack(">H", pdu),
                ),
            )
            if mode == "duplicates":
                done = 0
                while done < 41:
                    count = min(20, (pdu - 12) // 18, 41 - done)
                    request = _request(connection)
                    _check(
                        request,
                        pdu,
                        [(10, bytes([index])) for index in range(done, done + count)],
                    )
                    _reply(
                        connection,
                        request,
                        bytes(
                            5 if index % 7 == 3 else 255
                            for index in range(done, done + count)
                        ),
                    )
                    done += count
            else:
                if mode != "scalar":
                    first = _request(connection)
                    _check(first, pdu, [(2000, b"\x63")])
                    _reply(connection, first, b"\xff")
                for offset in range(0, 700, pdu - 28):
                    request = _request(connection)
                    _check(
                        request, pdu, [(offset, b"\x2a" * min(pdu - 28, 700 - offset))]
                    )
                    if mode == "drop" and offset == pdu - 28:
                        connection.shutdown(socket.SHUT_RDWR)
                        return
                    failure = mode == "reject" and offset == pdu - 28
                    _reply(connection, request, bytes([5 if failure else 255]))
                    if failure:
                        break
                if mode != "scalar":
                    last = _request(connection)
                    _check(last, pdu, [(2000, b"\x63")])
                    _reply(connection, last, b"\xff")
            frame = _receive(connection)
            if len(frame) < 2 or frame[1] != 0x80:
                raise RuntimeError("provenance peer received unexpected extra write")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(error)


def run_write_provenance(root: Path) -> None:
    scenarios = [
        ("duplicates", 240),
        ("duplicates", 480),
        ("success", 240),
        ("reject", 240),
        ("drop", 240),
        ("scalar", 240),
    ]
    for mode, pdu in scenarios:
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            listener.settimeout(5)
            worker = threading.Thread(target=_serve, args=(listener, mode, pdu, errors))
            worker.start()
            try:
                subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-write-provenance",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        mode,
                    ],
                    cwd=root,
                    check=True,
                    timeout=12,
                )
            finally:
                worker.join(timeout=6)
            if worker.is_alive():
                raise RuntimeError("write provenance peer did not finish")
            if errors:
                raise errors[0]
    print(f"write provenance peers passed: {len(scenarios)} scenarios")
