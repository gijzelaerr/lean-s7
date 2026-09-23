"""Inject disconnects and wrong services at every segmented receive phase."""

from __future__ import annotations

import socket
import subprocess
import threading
from pathlib import Path

from extended_deadlines import _handshake
from transfer_deadlines import _ack, _receive, _request, _send, _userdata


def _serve(
    listener: socket.socket,
    operation: str,
    phase: int,
    mutation: str,
    errors: list[Exception],
) -> None:
    try:
        with _handshake(listener) as connection:
            connection.settimeout(3)
            steps = 6 if operation.startswith("upload") else 4
            for index in range(steps):
                request = _request(connection)
                reference = int.from_bytes(request[4:6], "big")
                if index == phase and mutation == "disconnect":
                    # EOF at a known boundary, not a timeout caused by test teardown.
                    connection.shutdown(socket.SHUT_RDWR)
                    return
                if operation.startswith("upload"):
                    function = 0x1D if index == 0 else 0x1F if index == 5 else 0x1E
                    if request[10] != function:
                        raise RuntimeError("upload sequence requested wrong phase")
                    if index == 0:
                        parameters = bytes([0x1D, 0, 0, 0, 0, 0, 0, 1, 7, 0, 5])
                        parameters += b"00004"
                        data = b""
                    elif index == 5:
                        parameters, data = b"\x1f", b""
                    else:
                        parameters = bytes([0x1E, int(index < 4)])
                        data = bytes([0, 1, 0, 0xFB, index])
                    if index == phase and mutation == "wrong-service":
                        parameters = bytes([0x04]) + parameters[1:]
                    response = _ack(reference, parameters, data)
                else:
                    payload = bytes([0, 1, 0, 4, 0xAA, 0xBB, 0xCC, 0xDD])
                    response = _userdata(
                        reference, "szl", index, payload[index * 2 : index * 2 + 2]
                    )
                    if index == phase:
                        # A validly framed response from a different USER_DATA service.
                        response = response[:16] + b"\x02" + response[17:]
                _send(connection, b"\x02\xf0\x80" + response)
                if index == phase:
                    frame = _receive(connection)
                    if (
                        frame[:3] == b"\x02\xf0\x80"
                        and operation.startswith("upload")
                        and 0 < index < 5
                    ):
                        # A validated upload ID permits exactly one cleanup request.
                        cleanup = frame[3:]
                        if cleanup[10] != 0x1F:
                            raise RuntimeError("faulted upload continued transferring")
                        _send(
                            connection,
                            b"\x02\xf0\x80"
                            + _ack(int.from_bytes(cleanup[4:6], "big"), b"\x1f"),
                        )
                        frame = _receive(connection)
                    if len(frame) < 2 or frame[1] != 0x80:
                        raise RuntimeError("faulted conversation did not disconnect")
                    return
    except (OSError, RuntimeError, ValueError, IndexError) as error:
        errors.append(error)


def run_stateful_faults(root: Path) -> None:
    scenarios = [
        (operation, phase, mutation)
        for operation, steps in (("upload", 6), ("szl", 4))
        for phase in range(steps)
        for mutation in ("disconnect", "wrong-service")
    ]
    # A successful raw transfer is not necessarily a valid compact block.
    scenarios.append(("upload-compact", 5, "compact-header"))
    for operation, phase, mutation in scenarios:
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            listener.settimeout(5)
            thread = threading.Thread(
                target=_serve, args=(listener, operation, phase, mutation, errors)
            )
            thread.start()
            try:
                subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-stateful-fault",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        operation,
                        "disconnect" if mutation == "disconnect" else "protocol",
                    ],
                    cwd=root,
                    check=True,
                    timeout=10,
                )
            finally:
                thread.join(timeout=4)
        if thread.is_alive():
            raise RuntimeError("stateful fault peer did not finish")
        if errors:
            raise errors[0]
    print(f"stateful fault peers passed: {len(scenarios)} phase injections")
