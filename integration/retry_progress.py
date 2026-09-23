"""Lost-acknowledgement peers for conservative replay and structured progress."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path

from extended_deadlines import _handshake
from transfer_deadlines import _ack, _receive, _request, _send


def _reply(connection: socket.socket, request: bytes, result: int = 0xFF) -> None:
    function, count = request[10:12]
    reference = int.from_bytes(request[4:6], "big")
    data = bytes([result]) * count
    if function == 4:
        data = struct.pack(">BBH", 0xFF, 4, 8) + b"\x2a"
    packet = _ack(reference, bytes([function, count]), data)
    _send(connection, b"\x02\xf0\x80" + packet)


def _serve(listener: socket.socket, mode: str, errors: list[Exception]) -> None:
    try:
        with _handshake(listener) as connection:
            first = _request(connection)
            if mode in ("read-retry", "write-opt-in") or mode.startswith("replay-"):
                connection.close()
                if mode == "replay-reconnect-reject":
                    replacement, _ = listener.accept()
                    with replacement:
                        replacement.settimeout(3)
                        cr = _receive(replacement)
                        _send(
                            replacement,
                            bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:],
                        )
                        setup = _request(replacement)
                        reference = int.from_bytes(setup[4:6], "big")
                        packet = bytearray(
                            _ack(reference, b"\xf0\x00\x00\x01\x00\x01\x00\xf0")
                        )
                        packet[10:12] = b"\x81\x04"
                        _send(replacement, b"\x02\xf0\x80" + packet)
                        _receive(replacement)
                    return
                with _handshake(listener) as replacement:
                    replay = _request(replacement)
                    if replay != first:
                        raise RuntimeError("retry changed request")
                    if mode == "replay-scalar-reject":
                        reference = int.from_bytes(replay[4:6], "big")
                        packet = bytearray(_ack(reference, b"\x05\x01", b"\xff"))
                        packet[10:12] = b"\x81\x04"
                        _send(replacement, b"\x02\xf0\x80" + packet)
                    else:
                        _reply(
                            replacement,
                            replay,
                            5 if mode == "replay-multi-reject" else 0xFF,
                        )
                    _receive(replacement)
                return
            if mode.endswith("no-retry"):
                connection.close()
            else:
                if first[10] != 5 or first[11] != 1:
                    raise RuntimeError("expected first singleton write chunk")
                _reply(connection, first)
                second = _request(connection)
                address = int.from_bytes(second[21:24], "big") // 8
                if address != 212:
                    raise RuntimeError("expected second chunk at acknowledged boundary")
                if mode == "multi-reject":
                    _reply(connection, second, 5)
                    _receive(connection)
                elif mode == "scalar-reject":
                    reference = int.from_bytes(second[4:6], "big")
                    packet = bytearray(_ack(reference, b"\x05\x01", b"\xff"))
                    packet[10:12] = b"\x81\x04"
                    _send(connection, b"\x02\xf0\x80" + packet)
                    _receive(connection)
                else:
                    connection.close()
        # Mutations must never be replayed by default, even with retries=1.
        listener.settimeout(0.6)
        try:
            unexpected, _ = listener.accept()
        except TimeoutError:
            return
        unexpected.close()
        raise RuntimeError("potentially mutating operation unexpectedly retried")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(error)


def run_retry_progress(root: Path) -> None:
    modes = (
        "read-retry",
        "write-opt-in",
        "write-no-retry",
        "control-no-retry",
        "raw-no-retry",
        "clock-no-retry",
        "security-no-retry",
        "upload-no-retry",
        "scalar-drop",
        "scalar-reject",
        "multi-drop",
        "multi-reject",
        "replay-scalar-reject",
        "replay-multi-reject",
        "replay-reconnect-reject",
    )
    for mode in modes:
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(2)
            listener.settimeout(5)
            worker = threading.Thread(target=_serve, args=(listener, mode, errors))
            worker.start()
            try:
                subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-retry-progress",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        mode,
                    ],
                    cwd=root,
                    check=True,
                    timeout=10,
                )
            finally:
                worker.join(timeout=6)
            if worker.is_alive():
                raise RuntimeError("retry/progress peer did not terminate")
            if errors:
                raise errors[0]
