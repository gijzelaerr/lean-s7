"""Independent reconnect-stage faults distinguish sessions from wire attempts."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
import time
from dataclasses import dataclass
from pathlib import Path

from boundary_operations import _closed, _handshake
from multi_batching import _ack, _receive, _request, _send


@dataclass(frozen=True)
class Case:
    mode: str
    fault: str
    budget: int
    failures: int

    @property
    def succeeds(self) -> bool:
        return self.fault.endswith("eof") and self.failures < self.budget

    @property
    def sessions(self) -> int:
        if self.budget == 0:
            return 1
        if not self.fault.endswith("eof"):
            return 2
        return 1 + (self.failures + 1 if self.succeeds else self.budget)


def _cases() -> tuple[Case, ...]:
    result = []
    for mode in ("read", "raw", "write", "multi"):
        for fault in ("cotp-eof", "setup-eof"):
            for budget in (0, 1, 2, 4):
                for failures in sorted({max(0, budget - 1), budget}):
                    result.append(Case(mode, fault, budget, failures))
        for fault in (
            "cotp-invalid",
            "setup-invalid",
            "setup-reject",
            "setup-shrink",
        ):
            result.append(Case(mode, fault, 4, 1))
        # Raw exchange intentionally has no compound receive deadline.
        if mode != "raw":
            result.append(Case(mode, "deadline", 4, 1))
    return tuple(result)


def _operation(request: bytes, mode: str) -> int:
    write = mode in ("write", "multi")
    width = 2 if mode == "multi" else 1
    parameters = bytes([5 if write else 4, width])
    data = bytearray()
    for index in range(width):
        parameters += b"\x12\x0a\x10\x02" + struct.pack(">HH", 1, 1)
        parameters += b"\x84" + (index * 32).to_bytes(3, "big")
        if write:
            data.extend(b"\0\x04\0\x08" + bytes([42 + index]))
            # S7's inter-item padding excludes the final item.
            if index + 1 < width:
                data.append(0)
    expected = struct.pack(">BBHHHH", 0x32, 1, 0, 0, len(parameters), len(data))
    expected += parameters + data
    if request[:4] != expected[:4] or request[6:] != expected[6:]:
        raise RuntimeError("reconnect operation changed address/order/payload")
    return int.from_bytes(request[4:6], "big")


def _reconnect(connection: socket.socket, fault: str | None) -> bool:
    """Return whether setup succeeded; failed stages must not send operations."""
    connection.settimeout(4)
    cr = _receive(connection)
    if len(cr) != 18 or cr[:2] != b"\x11\xe0":
        raise RuntimeError("reconnect COTP request malformed")
    if fault == "cotp-eof":
        connection.shutdown(socket.SHUT_RDWR)
        return False
    cc = bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:]
    if fault == "cotp-invalid":
        cc = cc[:2] + b"\xff\xff" + cc[4:]
        _send(connection, cc)
        _closed(connection)
        return False
    _send(connection, cc)
    setup = _request(connection)
    expected = b"\x32\x01\0\0\0\x01\0\x08\0\0\xf0\0\0\x01\0\x01\x01\xe0"
    if setup != expected:
        raise RuntimeError("reconnect setup request changed")
    if fault == "setup-eof":
        connection.shutdown(socket.SHUT_RDWR)
        return False
    if fault == "deadline":
        time.sleep(0.5)
    response = _ack(
        2 if fault == "setup-invalid" else 1,
        setup[10:16] + struct.pack(">H", 240 if fault == "setup-shrink" else 480),
    )
    if fault == "setup-reject":
        response = response[:10] + b"\x81\x04" + response[12:]
    _send(connection, b"\x02\xf0\x80" + response)
    if fault is not None:
        _closed(connection)
        return False
    return True


def _serve(listener: socket.socket, case: Case, errors: list[Exception]) -> None:
    stage = "initial handshake"
    try:
        connection, _ = listener.accept()
        with connection:
            _handshake(connection, 480)
            original = _request(connection)
            reference = _operation(original, case.mode)
            # Lost operation response creates the only initial wire attempt.
            connection.shutdown(socket.SHUT_RDWR)
        sends = 1
        for index in range(1, case.sessions):
            stage = f"reconnect session {index}/{case.sessions - 1}"
            connection, _ = listener.accept()
            with connection:
                recovery = case.succeeds and index == case.sessions - 1
                ready = _reconnect(connection, None if recovery else case.fault)
                if ready != recovery:
                    raise RuntimeError("reconnect stage unexpectedly ready")
                if not ready:
                    continue
                stage = "recovered operation resend"
                request = _request(connection)
                _operation(request, case.mode)
                if request != original:
                    raise RuntimeError(
                        "reconnect changed exact original request/reference"
                    )
                sends += 1
                write = case.mode in ("write", "multi")
                width = 2 if case.mode == "multi" else 1
                data = b"\xff" * width if write else b"\xff\x04\0\x08\x2a"
                _send(
                    connection,
                    b"\x02\xf0\x80"
                    + _ack(reference, bytes([5 if write else 4, width]), data),
                )
                _closed(connection)
        if sends != (2 if case.succeeds else 1):
            raise RuntimeError("operation sends differ from independent count")
        stage = "no excess reconnect or fresh call resurrection"
        listener.settimeout(0.15)
        try:
            extra, _ = listener.accept()
        except TimeoutError:
            return
        extra.close()
        raise RuntimeError("reconnect allowance exceeded")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(RuntimeError(f"{case}, {stage}: {error}"))


def _self_test() -> None:
    cases = _cases()
    assert len(cases) == 75 and len(set(cases)) == 75
    for case in cases:
        assert 1 <= case.sessions <= case.budget + 1
        if case.fault.endswith("eof"):
            assert case.succeeds == (case.failures < case.budget)
    for mode in ("read", "raw", "write", "multi"):
        width = 2 if mode == "multi" else 1
        write = mode in ("write", "multi")
        parameters = bytes([5 if write else 4, width])
        data = b""
        for index in range(width):
            parameters += b"\x12\x0a\x10\x02\0\x01\0\x01\x84" + (index * 32).to_bytes(
                3, "big"
            )
            if write:
                data += b"\0\x04\0\x08" + bytes([42 + index])
                if index + 1 < width:
                    data += b"\0"
        request = (
            struct.pack(">BBHHHH", 0x32, 1, 0, 65535, len(parameters), len(data))
            + parameters
            + data
        )
        assert _operation(request, mode) == 65535
        for index in range(len(request)):
            if index in (4, 5):
                continue
            damaged = bytearray(request)
            damaged[index] ^= 1
            try:
                _operation(bytes(damaged), mode)
            except RuntimeError:
                pass
            else:
                raise RuntimeError("reconnect wire oracle accepted mutation")


def run_reconnect_faults(root: Path) -> None:
    _self_test()
    for case in _cases():
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(8)
            listener.settimeout(4)
            worker = threading.Thread(target=_serve, args=(listener, case, errors))
            worker.start()
            try:
                outcome = subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-reconnect-faults",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        case.mode,
                        case.fault,
                        str(case.budget),
                        str(case.failures),
                    ],
                    cwd=root,
                    capture_output=True,
                    text=True,
                    timeout=12,
                    check=False,
                )
            finally:
                worker.join(timeout=5)
            if worker.is_alive():
                raise RuntimeError("reconnect fault peer did not terminate")
            if errors:
                raise errors[0]
            if outcome.returncode:
                raise RuntimeError(
                    f"native reconnect fault failed: {outcome.stdout}{outcome.stderr}"
                )
            print(outcome.stdout.strip())
    print(f"reconnect stage campaign passed: {len(_cases())} conversations")


if __name__ == "__main__":
    run_reconnect_faults(Path(__file__).resolve().parents[1])
