"""Single-response services must not silently accept continuation replies."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path

from extended_deadlines import _handshake
from multi_batching import _receive, _request, _send


def _serve(
    listener: socket.socket, service: str, mode: str, errors: list[Exception]
) -> None:
    try:
        with _handshake(listener) as connection:
            request = _request(connection)
            expected = {
                "read-clock": (7, 1),
                "set-clock": (7, 2),
                "blocks": (3, 1),
                "set-password": (5, 1),
                "clear-password": (5, 2),
            }
            group, subfunction = expected[service]
            if request[1] != 7 or request[15:17] != bytes([0x40 | group, subfunction]):
                raise RuntimeError("completion peer saw wrong USER_DATA service")
            if service == "read-clock":
                payload = bytes.fromhex("00 20 26 09 23 12 00 00 00 04")
            elif service == "blocks":
                payload = b"".join(
                    bytes([0x30, code]) + struct.pack(">H", int(code == 0x41))
                    for code in (0x38, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46)
                )
            else:
                payload = b""
            parameters = bytes(
                [
                    0,
                    1,
                    0x12,
                    8,
                    0x12,
                    0x80 | group,
                    subfunction,
                    1,
                    1,
                    int(mode == "incomplete"),
                    0,
                    0,
                ]
            )
            data = b"\xff\x09" + struct.pack(">H", len(payload)) + payload
            reference = int.from_bytes(request[4:6], "big")
            packet = struct.pack(">BBHHHH", 0x32, 7, 0, reference, 12, len(data))
            _send(connection, b"\x02\xf0\x80" + packet + parameters + data)
            frame = _receive(connection)
            if len(frame) < 2 or frame[1] != 0x80:
                raise RuntimeError(
                    "completion peer saw unexpected continuation or write"
                )
        listener.settimeout(0.3)
        try:
            unexpected, _ = listener.accept()
        except TimeoutError:
            return
        unexpected.close()
        raise RuntimeError("incomplete service was retried despite protocol failure")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(error)


def run_userdata_completion(root: Path) -> None:
    for service in (
        "read-clock",
        "blocks",
        "set-clock",
        "set-password",
        "clear-password",
    ):
        for mode in ("complete", "incomplete"):
            errors: list[Exception] = []
            with socket.socket() as listener:
                listener.bind(("127.0.0.1", 0))
                listener.listen(2)
                listener.settimeout(5)
                worker = threading.Thread(
                    target=_serve, args=(listener, service, mode, errors)
                )
                worker.start()
                try:
                    subprocess.run(
                        [
                            str(root / ".lake/build/bin/lean-s7"),
                            "integration-userdata-completion",
                            "127.0.0.1",
                            str(listener.getsockname()[1]),
                            service,
                            mode,
                        ],
                        cwd=root,
                        check=True,
                        timeout=12,
                    )
                finally:
                    worker.join(timeout=6)
                if worker.is_alive():
                    raise RuntimeError("completion peer did not finish")
                if errors:
                    raise errors[0]
    print("USER_DATA completion peers passed: 10 scenarios")
