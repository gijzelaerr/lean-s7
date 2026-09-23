"""Peers for oversized per-item failures and write prevalidation side effects."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path

from multi_batching import _ack, _receive, _request, _send


def _serve(
    listener: socket.socket, pdu: int, mode: str, errors: list[Exception]
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(4)
            cr = _receive(connection)
            _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
            setup = _request(connection)
            reference = int.from_bytes(setup[4:6], "big")
            _send(
                connection,
                b"\x02\xf0\x80"
                + _ack(reference, b"\xf0\0\0\x01\0\x01" + struct.pack(">H", pdu)),
            )
            if not mode.startswith("invalid-"):
                function = 4 if mode.startswith("read-") else 5
                maximum = pdu - (18 if function == 4 else 28)
                successful = mode.endswith("success")
                if successful:
                    stages = [
                        (offset, min(maximum, 700 - offset), False)
                        for offset in range(0, 700, maximum)
                    ]
                else:
                    stages = [(0, maximum, mode.endswith("first"))]
                if mode.endswith("mid"):
                    stages.append((maximum, min(maximum, 700 - maximum), True))
                # The failed logical item must stop immediately, preserving the
                # next item's request and its original result position.
                stages.append((1000, 1, False))
                for start, count, failure in stages:
                    request = _request(connection)
                    if len(request) > pdu:
                        raise RuntimeError("oversized multi request exceeds PDU")
                    reference, parameters_size, data_size = struct.unpack(
                        ">HHH", request[4:10]
                    )
                    expected = bytes([function, 1, 0x12, 0x0A, 0x10, 2])
                    expected += struct.pack(">HH", count, 1) + b"\x84"
                    expected += (start * 8).to_bytes(3, "big")
                    if parameters_size != 14 or request[10:24] != expected:
                        raise RuntimeError("oversized multi chunk/order mismatch")
                    if len(request) != 10 + parameters_size + data_size:
                        raise RuntimeError("oversized multi request lengths mismatch")
                    payload = (
                        bytes(
                            (index * 37 + 7) % 256
                            for index in range(start, start + count)
                        )
                        if successful and start != 1000
                        else bytes([99 if start == 1000 else 42]) * count
                    )
                    if function == 5:
                        expected_data = struct.pack(">BBH", 0, 4, count * 8)
                        expected_data += payload
                        if request[24:] != expected_data:
                            raise RuntimeError("oversized multi write slice mismatch")
                        data = bytes([5 if failure else 0xFF])
                    elif failure:
                        data = struct.pack(">BBH", 5, 0, 0)
                    else:
                        if data_size:
                            raise RuntimeError("oversized multi read sent data")
                        data = struct.pack(">BBH", 0xFF, 4, count * 8)
                        data += payload
                    _send(
                        connection,
                        b"\x02\xf0\x80" + _ack(reference, bytes([function, 1]), data),
                    )
            disconnected = _receive(connection)
            if len(disconnected) < 2 or disconnected[1] != 0x80:
                raise RuntimeError("unexpected operation after validation/failure")
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_multi_semantics(root: Path) -> None:
    modes = (
        "read-first",
        "read-mid",
        "write-first",
        "write-mid",
        "read-success",
        "write-success",
        "invalid-payload",
        "invalid-range",
        "invalid-endpoint",
    )
    for pdu in (240, 480):
        for mode in modes:
            errors: list[Exception] = []
            with socket.socket() as listener:
                listener.bind(("127.0.0.1", 0))
                listener.listen(1)
                listener.settimeout(5)
                thread = threading.Thread(
                    target=_serve, args=(listener, pdu, mode, errors)
                )
                thread.start()
                try:
                    subprocess.run(
                        [
                            str(root / ".lake/build/bin/lean-s7"),
                            "integration-multi-semantics",
                            "127.0.0.1",
                            str(listener.getsockname()[1]),
                            mode,
                        ],
                        check=True,
                        cwd=root,
                        timeout=10,
                    )
                finally:
                    thread.join(timeout=6)
                if thread.is_alive():
                    raise RuntimeError("multi-semantics peer did not terminate")
                if errors:
                    raise errors[0]
