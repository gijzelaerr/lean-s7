"""Exact-wire block-info numeric correlation and non-sending preflight controls."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path

from concurrency import _handshake
from multi_batching import _request, _send
from userdata_assurance import _closed, _reply


def _serve(listener: socket.socket, scenario: str, errors: list[Exception]) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            _handshake(connection)
            connection.settimeout(3)
            request = _request(connection)
            number = 0 if scenario == "zero" else 65535 if scenario == "max" else 1
            parameters = bytes.fromhex("0001120411430300")
            data = bytes.fromhex("ff0900083041") + f"{number:05d}".encode() + b"A"
            expected = (
                struct.pack(">BBHHHH", 0x32, 7, 0, 0xFFFF, 8, 12) + parameters + data
            )
            # The first valid request must use the initial operation reference:
            # high-number calls neither send nor allocate one during preflight.
            if request != expected:
                raise RuntimeError(
                    f"block-info request/preflight reference differs: {request.hex()}"
                )
            payload = bytearray(78)
            payload[12:14] = struct.pack(">H", 2 if scenario == "mismatch" else number)
            if scenario == "max":
                payload[1], payload[11] = 255, 255
            elif scenario == "opaque":
                payload[1], payload[11] = 1, 165
            _send(
                connection,
                b"\x02\xf0\x80" + _reply(0xFFFF, 3, 3, 0, 0, 0, bytes(payload)),
            )
            _closed(connection)
        listener.settimeout(0.2)
        try:
            unexpected, _ = listener.accept()
        except TimeoutError:
            return
        unexpected.close()
        raise RuntimeError("block-info reply triggered an unexpected reconnect")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(error)


def run_block_info_identity(root: Path) -> None:
    for scenario in ("zero", "max", "opaque", "mismatch", "preflight"):
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(2)
            listener.settimeout(5)
            worker = threading.Thread(
                target=_serve, args=(listener, scenario, errors), daemon=True
            )
            worker.start()
            try:
                subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-block-info-identity",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        scenario,
                    ],
                    cwd=root,
                    check=True,
                    timeout=12,
                )
            finally:
                worker.join(timeout=6)
            if worker.is_alive():
                raise RuntimeError("block-info identity peer did not finish")
            if errors:
                raise errors[0]
    print("Block-info identity peers passed: 5 scenarios")
