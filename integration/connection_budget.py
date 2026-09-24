"""Independent peers for one connection budget and distinct-address fallback."""

from __future__ import annotations

import socket
import subprocess
import threading
import time
from pathlib import Path

from multi_batching import _ack, _receive, _request, _send


def _closed(connection: socket.socket) -> None:
    # A fresh per-stage timeout would still be running at this point. The
    # short read window distinguishes it from expiry of the total budget.
    connection.settimeout(0.2)
    try:
        data = connection.recv(1)
    except ConnectionResetError:
        return
    if data:
        raise RuntimeError("failed negotiation sent more data")


def _confirm(connection: socket.socket, cr: bytes) -> None:
    if len(cr) != 18 or cr[1] != 0xE0:
        raise RuntimeError("budget peer expected COTP connection request")
    _send(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])


def _disconnect(connection: socket.socket) -> None:
    frame = _receive(connection)
    if len(frame) < 2 or frame[1] != 0x80:
        raise RuntimeError("successful negotiation did not disconnect")


def _serve(
    listener: socket.socket,
    mode: str,
    position: int,
    errors: list[Exception],
) -> None:
    try:
        if mode == "candidate-protocol" and position == 1:
            # Malformed COTP is terminal even though another endpoint is live.
            try:
                unexpected, _ = listener.accept()
            except TimeoutError:
                return
            unexpected.close()
            raise RuntimeError("protocol failure fell back to another address")
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(3)
            cr = _receive(connection)
            if mode == "candidate-protocol":
                _send(connection, b"\x01\xd0")
                _closed(connection)
                return
            if mode in ("candidate-disconnected", "candidate-budget") and position == 0:
                if mode == "candidate-budget":
                    time.sleep(1.0)
                # A distinct endpoint may be tried after transport EOF.
                return
            if mode == "candidate-budget":
                # The first endpoint consumed most of the shared budget. This
                # A 2.5 s second stage fits a fresh 3 s allowance, but exceeds
                # the 2 s left after the first stage's 1 s delay.
                time.sleep(2.5)
                _closed(connection)
                return
            if mode == "combined":
                time.sleep(1.0)
            elif mode in ("cotp-only", "disabled"):
                time.sleep(0.18)
            _confirm(connection, cr)
            if mode.startswith("candidate-"):
                _disconnect(connection)
                return
            setup = _request(connection)
            if mode in ("combined", "operation"):
                # Withhold the reply entirely after waiting less than a fresh
                # timeout; early EOF proves the earlier budget remained active.
                time.sleep(1.5 if mode == "operation" else 2.5)
                _closed(connection)
                return
            if mode in ("setup-only", "disabled"):
                time.sleep(0.18)
            _send(
                connection,
                b"\x02\xf0\x80"
                + _ack(int.from_bytes(setup[4:6], "big"), b"\xf0\0\0\x01\0\x01\0\xf0"),
            )
            _disconnect(connection)
    except (OSError, RuntimeError, ValueError, IndexError) as error:
        errors.append(error)


def run_connection_budget(root: Path) -> None:
    modes = (
        "cotp-only",
        "setup-only",
        "combined",
        "disabled",
        "operation",
        "candidate-refused",
        "candidate-disconnected",
        "candidate-protocol",
        "candidate-budget",
    )
    for mode in modes:
        errors: list[Exception] = []
        workers: list[threading.Thread] = []
        with socket.socket() as first, socket.socket() as second:
            for listener in (first, second):
                listener.bind(("127.0.0.1", 0))
                listener.settimeout(1 if mode == "candidate-protocol" else 4)
            # A bound non-listening TCP socket can silently drop SYN on macOS.
            # Close the locally selected endpoint to exercise actual refusal.
            # This fixture assumes no unrelated process claims that ephemeral
            # port during its short controlled localhost run.
            first_port = first.getsockname()[1]
            second_port = second.getsockname()[1]
            if mode == "candidate-refused":
                first.close()
            if mode != "candidate-refused":
                first.listen(2)
                workers.append(
                    threading.Thread(target=_serve, args=(first, mode, 0, errors))
                )
            if mode.startswith("candidate-"):
                second.listen(2)
                workers.append(
                    threading.Thread(target=_serve, args=(second, mode, 1, errors))
                )
            for worker in workers:
                worker.start()
            try:
                outcome = subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-connection-budget",
                        "localhost",
                        str(first_port),
                        str(second_port),
                        mode,
                    ],
                    cwd=root,
                    check=False,
                    capture_output=True,
                    text=True,
                    timeout=7,
                )
            finally:
                for worker in workers:
                    worker.join(5)
            if any(worker.is_alive() for worker in workers):
                raise RuntimeError(f"connection budget peer hung: {mode}")
            if errors:
                raise RuntimeError(
                    f"connection budget peer failed: {mode}"
                ) from errors[0]
            if outcome.returncode:
                raise RuntimeError(outcome.stdout + outcome.stderr)
            print(outcome.stdout.strip())
    _run_pending_tcp_budget(root)


def _run_pending_tcp_budget(root: Path) -> None:
    """Some platforms drop SYN to a bound, non-listening localhost socket.

    Where available, this independently checks that a pending native connect
    does not leave a blocked worker preventing process exit after its deadline.
    Platforms that refuse immediately still run the nine portable peers above.
    """
    with socket.socket() as passive:
        passive.bind(("127.0.0.1", 0))
        try:
            unexpected = socket.create_connection(passive.getsockname(), timeout=0.1)
        except ConnectionRefusedError:
            print("pending TCP budget probe not applicable: immediate refusal")
            return
        except TimeoutError:
            pass
        else:
            unexpected.close()
            raise RuntimeError("non-listening TCP probe unexpectedly accepted")
        port = str(passive.getsockname()[1])
        outcome = subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-connection-budget",
                "127.0.0.1",
                port,
                port,
                "pending-tcp",
            ],
            cwd=root,
            check=True,
            capture_output=True,
            text=True,
            timeout=2,
        )
        print("pending TCP process exit passed:", outcome.stdout.strip())
