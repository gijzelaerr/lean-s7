"""Independent USER_DATA peers: opaque echo tokens, identity, and native ACKs."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
from pathlib import Path

from concurrency import _handshake
from multi_batching import _request, _send


def _reply(
    reference: int,
    group: int,
    subfunction: int,
    sequence: int,
    unit: int,
    flag: int,
    payload: bytes,
    transport: int = 9,
    code: int = 0xFF,
) -> bytes:
    parameters = bytes(
        [0, 1, 0x12, 8, 0x12, 0x80 | group, subfunction, sequence, unit, flag, 0, 0]
    )
    data = bytes([code, transport]) + struct.pack(">H", len(payload)) + payload
    return (
        struct.pack(">BBHHHH", 0x32, 7, 0, reference, 12, len(data)) + parameters + data
    )


def _closed(connection: socket.socket) -> None:
    """Permit clean EOF/reset or one exact classic disconnect request."""
    incoming = bytearray()
    while True:
        try:
            chunk = connection.recv(32)
        except ConnectionResetError:
            chunk = b""
        if not chunk:
            break
        incoming.extend(chunk)
        if len(incoming) > 11:
            raise RuntimeError(
                "USER_DATA client sent extra traffic after completion/rejection"
            )
    if incoming and incoming != bytes.fromhex("0300000b06800001000100"):
        raise RuntimeError(
            f"USER_DATA client sent invalid closing traffic: {incoming.hex()}"
        )


def _check_request(
    request: bytes, group: int, subfunction: int, sequence: int | None, operation: str
) -> int:
    parameter_length = 8 if sequence is None else 12
    if (
        request[:4] != b"\x32\x07\0\0"
        or int.from_bytes(request[6:8], "big") != parameter_length
        or int.from_bytes(request[8:10], "big") != len(request) - 10 - parameter_length
    ):
        raise RuntimeError(f"USER_DATA request header mismatch: {request.hex()}")
    parameters = request[10 : 10 + parameter_length]
    method = 0x12 if sequence is not None and operation == "szl" else 0x11
    expected = bytes(
        [
            0,
            1,
            0x12,
            parameter_length - 4,
            method,
            0x40 | group,
            subfunction,
            sequence or 0,
        ]
    )
    if sequence is not None:
        expected += bytes(4)
    if parameters != expected:
        raise RuntimeError(
            f"USER_DATA continuation did not echo opaque token: {parameters.hex()} != {expected.hex()}"
        )
    data = request[10 + parameter_length :]
    if sequence is not None:
        expected_data = b"\x0a\0\0\0"
    elif operation == "szl":
        expected_data = b"\xff\x09\0\x04\x04\x24\0\0"
    elif operation == "blocks":
        expected_data = b"\xff\x09\0\x02\x30\x41"
    elif operation == "clear-password":
        expected_data = b"\x0a\0\0\0"
    elif operation == "set-clock":
        expected_data = bytes.fromhex("ff09000a00192402292359581231")
    else:
        # Independent native Snap7 password transform for ASCII 12345678.
        encoded = bytearray()
        for index, byte in enumerate(b"12345678"):
            encoded.append(byte ^ 0x55 ^ (encoded[index - 2] if index >= 2 else 0))
        expected_data = b"\xff\x09\0\x08" + encoded
    if data != expected_data:
        raise RuntimeError(f"USER_DATA request data mismatch: {data.hex()}")
    return int.from_bytes(request[4:6], "big")


def _serve(
    listener: socket.socket, operation: str, scenario: str, errors: list[Exception]
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            _handshake(connection)
            connection.settimeout(3)
            group, subfunction = {
                "szl": (4, 1),
                "blocks": (3, 2),
                "set-clock": (7, 2),
                "set-password": (5, 1),
                "clear-password": (5, 2),
            }[operation]
            request = _request(connection)
            reference = _check_request(request, group, subfunction, None, operation)
            if operation not in ("szl", "blocks"):
                payload, transport, code, flag = b"", 0, 0x0A, 0
                if scenario == "octet-ack":
                    transport, code = 9, 0xFF
                elif scenario == "nonempty-null":
                    payload = b"\xaa"
                elif scenario == "wrong-null-transport":
                    transport = 9
                elif scenario == "continuing-null":
                    flag = 1
                _send(
                    connection,
                    b"\x02\xf0\x80"
                    + _reply(
                        reference,
                        group,
                        subfunction,
                        0,
                        0,
                        flag,
                        payload,
                        transport,
                        code,
                    ),
                )
            else:
                unit = 0 if scenario == "zero-unit" else 0x51
                # Repeat, wrap-looking, and nonmonotonic values are all opaque.
                sequences = [0xFF, 1, 1, 0x80]
                chunks = (
                    [
                        b"\x04\x24\0\0\0\x02",
                        b"\0\x04\x01",
                        b"\x02\x03\x04",
                        b"\x05\x06\x07\x08",
                    ]
                    if operation == "szl"
                    else [b"\0", b"\x01\x11", b"\x22\x02", b"\x01\x33\x44"]
                )
                for index, (sequence, payload) in enumerate(
                    zip(sequences, chunks, strict=True)
                ):
                    more = int(index != len(chunks) - 1)
                    actual_reference, actual_group, actual_subfunction = (
                        reference,
                        group,
                        subfunction,
                    )
                    actual_unit, transport, flag = unit, 9, more
                    if index == 1:
                        if scenario == "stale-reference":
                            actual_reference = (reference - 1) % 65536
                        elif scenario == "wrong-group":
                            actual_group = 3 if group == 4 else 4
                        elif scenario == "wrong-subfunction":
                            actual_subfunction = subfunction + 1
                        elif scenario == "changed-unit":
                            actual_unit = (unit + 1) % 256
                        elif scenario == "invalid-flag":
                            flag = 2
                        elif scenario == "wrong-transport":
                            transport = 4
                    _send(
                        connection,
                        b"\x02\xf0\x80"
                        + _reply(
                            actual_reference,
                            actual_group,
                            actual_subfunction,
                            sequence,
                            actual_unit,
                            flag,
                            payload,
                            transport,
                        ),
                    )
                    if index == 1 and scenario not in ("valid", "zero-unit"):
                        break
                    if more:
                        request = _request(connection)
                        reference = _check_request(
                            request, group, subfunction, sequence, operation
                        )
            _closed(connection)
        listener.settimeout(0.1)
        try:
            unexpected, _ = listener.accept()
        except TimeoutError:
            return
        unexpected.close()
        raise RuntimeError("USER_DATA terminal failure triggered a reconnect")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(error)


def run_userdata_assurance(root: Path) -> None:
    cases = [
        (operation, scenario)
        for operation in ("szl", "blocks")
        for scenario in (
            "valid",
            "zero-unit",
            "stale-reference",
            "wrong-group",
            "wrong-subfunction",
            "changed-unit",
            "invalid-flag",
            "wrong-transport",
        )
    ]
    cases += [
        (operation, scenario)
        for operation in ("set-clock", "set-password", "clear-password")
        for scenario in (
            "valid",
            "octet-ack",
            "nonempty-null",
            "wrong-null-transport",
            "continuing-null",
        )
    ]
    for operation, scenario in cases:
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(2)
            listener.settimeout(4)
            worker = threading.Thread(
                target=_serve, args=(listener, operation, scenario, errors)
            )
            worker.start()
            try:
                outcome = subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-userdata-assurance",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        operation,
                        scenario,
                    ],
                    capture_output=True,
                    text=True,
                    timeout=8,
                    check=False,
                )
            finally:
                worker.join(timeout=4)
            if worker.is_alive() or errors:
                raise RuntimeError(
                    f"USER_DATA peer failed {operation}/{scenario}: {errors}"
                )
            if outcome.returncode:
                raise RuntimeError(
                    f"USER_DATA client failed {operation}/{scenario}: {outcome.stdout}{outcome.stderr}"
                )
    print(
        f"USER_DATA independent full-stack assurance: {len(cases)} conversations passed"
    )
