"""Seeded mixed IO with bounded stale filtering, rejection reuse and closure."""

from __future__ import annotations

import argparse
import random
import socket
import struct
import subprocess
import threading
from dataclasses import dataclass
from pathlib import Path

from boundary_operations import _closed, _handshake
from multi_batching import _ack, _request, _send

SEEDS = (7, 2026, 65535, 0x573743)


@dataclass(frozen=True)
class Operation:
    kind: str
    status: str
    stale: int
    value: int

    def token(self) -> str:
        return f"{self.kind}:{self.status}:{self.stale}:{self.value}"


def generate(seed: int, terminal: str) -> tuple[Operation, ...]:
    if not 0 <= seed <= 0xFFFFFFFF or terminal not in ("overflow", "protocol"):
        raise ValueError("invalid bounded live-correlation configuration")
    rng = random.Random(seed)
    # Each successful or rejected operation reaches the decoder only after its
    # stale replies. Fixed categories, shuffled order and independently varied
    # payloads make the bounded history deterministic and reproducible.
    specs = [
        (kind, status) for kind in ("r", "w") for status in ("ok", "global", "item")
    ]
    rng.shuffle(specs)
    operations = [
        Operation(kind, status, index % 3, rng.randrange(256))
        for index, (kind, status) in enumerate(specs)
    ]
    # Both final healthy operations prove reuse and write-history reset after
    # any preceding error; one crosses the accepted stale-count upper boundary.
    operations += [
        Operation("w", "ok", 2, rng.randrange(256)),
        Operation("r", "ok", 2, rng.randrange(256)),
        Operation(
            "w" if seed % 2 else "r",
            terminal,
            3 if terminal == "overflow" else 2,
            rng.randrange(256),
        ),
    ]
    return tuple(operations)


def request_bytes(index: int, operation: Operation) -> bytes:
    reference = (0xFFFF + index) & 0xFFFF
    write = operation.kind == "w"
    parameters = bytes([5 if write else 4, 1]) + b"\x12\x0a\x10\x02"
    parameters += struct.pack(">HHB", 1, 1, 0x84) + (index * 128).to_bytes(3, "big")
    data = b"\0\x04\0\x08" + bytes([operation.value]) if write else b""
    return (
        struct.pack(">BBHHHH", 0x32, 1, 0, reference, len(parameters), len(data))
        + parameters
        + data
    )


def validate_request(packet: bytes, index: int, operation: Operation) -> None:
    if packet != request_bytes(index, operation):
        raise RuntimeError(
            f"request/reference/order/payload mismatch at {index}: {packet.hex()}"
        )


def _response(reference: int, operation: Operation) -> bytes:
    write = operation.kind == "w"
    parameters = bytes([5 if write else 4, 1])
    if operation.status == "global":
        packet = _ack(reference, parameters)
        return packet[:10] + b"\x81\x04" + packet[12:]
    if operation.status == "item":
        data = b"\x05" if write else b"\x05\0\0\0"
    else:
        data = b"\xff" if write else b"\xff\x04\0\x08" + bytes([operation.value])
    if operation.status == "protocol":
        # Correlated ACK with the wrong service is not a stale reply.
        parameters = bytes([4 if write else 5, 1])
    return _ack(reference, parameters, data)


def _serve(
    listener: socket.socket,
    pdu: int,
    operations: tuple[Operation, ...],
    errors: list[Exception],
) -> None:
    stage = "handshake"
    try:
        connection, _ = listener.accept()
        with connection:
            _handshake(connection, pdu)
            for index, operation in enumerate(operations):
                stage = f"operation {index}: {operation}"
                validate_request(_request(connection), index, operation)
                reference = (0xFFFF + index) & 0xFFFF
                for stale_index in range(operation.stale):
                    # Structurally valid stale replies vary across PLC rejection,
                    # wrong-service ACK and arbitrary payload. Their content may
                    # not determine the current operation's payload/progress.
                    stale_ref = (reference - stale_index - 1) & 0xFFFF
                    stale = _ack(stale_ref, b"\x05\x01", b"\xff")
                    if stale_index % 2:
                        stale = stale[:10] + b"\x81\x04" + stale[12:]
                    _send(connection, b"\x02\xf0\x80" + stale)
                if operation.status == "overflow":
                    # No current response: the third stale frame is sufficient
                    # to trigger the configured terminal gate, not a timeout.
                    break
                _send(connection, b"\x02\xf0\x80" + _response(reference, operation))
                if operation.status == "protocol":
                    break
            stage = "terminal disconnect and no later requests"
            _closed(connection)
            if connection.recv(1):
                raise RuntimeError("terminal client sent an extra frame")
        stage = "no excess reconnect"
        listener.settimeout(0.15)
        try:
            extra, _ = listener.accept()
        except TimeoutError:
            return
        extra.close()
        raise RuntimeError("terminal protocol failure retried or resurrected client")
    except (OSError, RuntimeError, ValueError, IndexError, struct.error) as error:
        errors.append(RuntimeError(f"live correlation at {stage}: {error}"))


def _self_test() -> None:
    for seed in SEEDS:
        for terminal in ("overflow", "protocol"):
            operations = generate(seed, terminal)
            assert operations == generate(seed, terminal) and len(operations) == 9
            assert {(op.kind, op.status) for op in operations[:6]} == {
                (kind, status)
                for kind in ("r", "w")
                for status in ("ok", "global", "item")
            }
            assert {op.stale for op in operations[:6]} == {0, 1, 2}
            assert operations[-1].status == terminal
            for index, operation in enumerate(operations):
                packet = request_bytes(index, operation)
                validate_request(packet, index, operation)
                # Independently demonstrate that reference, address, length,
                # discriminator and write-payload changes fail the wire oracle.
                positions = [1, 4, 6, 10, 23] + ([28] if operation.kind == "w" else [])
                for position in positions:
                    changed = bytearray(packet)
                    changed[position] ^= 1
                    try:
                        validate_request(bytes(changed), index, operation)
                    except RuntimeError:
                        continue
                    raise AssertionError("wire oracle accepted mutated request")
    assert (
        int.from_bytes(request_bytes(0, generate(7, "overflow")[0])[4:6], "big")
        == 65535
    )
    assert int.from_bytes(request_bytes(1, generate(7, "overflow")[1])[4:6], "big") == 0


def run(
    root: Path,
    seed: int | None = None,
    pdu: int | None = None,
    terminal: str | None = None,
) -> None:
    _self_test()
    count = 0
    for chosen_seed in SEEDS if seed is None else (seed,):
        for chosen_pdu in (240, 480) if pdu is None else (pdu,):
            if chosen_pdu not in (240, 480):
                raise ValueError("PDU must be 240 or 480")
            for chosen_terminal in (
                ("overflow", "protocol") if terminal is None else (terminal,)
            ):
                operations = generate(chosen_seed, chosen_terminal)
                errors: list[Exception] = []
                with socket.socket() as listener:
                    listener.bind(("127.0.0.1", 0))
                    listener.listen(4)
                    listener.settimeout(4)
                    worker = threading.Thread(
                        target=_serve, args=(listener, chosen_pdu, operations, errors)
                    )
                    worker.start()
                    replay = f"python integration/live_correlation.py --seed {chosen_seed} --pdu {chosen_pdu} --terminal {chosen_terminal}"
                    try:
                        outcome = subprocess.run(
                            [
                                str(root / ".lake/build/bin/lean-s7"),
                                "integration-live-correlation",
                                "127.0.0.1",
                                str(listener.getsockname()[1]),
                                "|".join(op.token() for op in operations),
                            ],
                            cwd=root,
                            capture_output=True,
                            text=True,
                            timeout=15,
                            check=False,
                        )
                    except (OSError, subprocess.TimeoutExpired) as error:
                        raise RuntimeError(
                            f"native live correlation failed; replay: {replay}; {error}"
                        ) from error
                    finally:
                        worker.join(timeout=5)
                    if worker.is_alive() or errors or outcome.returncode:
                        detail = (
                            errors
                            or f"{outcome.stdout[-4096:]}{outcome.stderr[-4096:]}"
                        )
                        raise RuntimeError(
                            f"live correlation failed; replay: {replay}; {detail}"
                        )
                    if (
                        outcome.stdout.strip()
                        != "live correlation passed: 9 operations"
                    ):
                        raise RuntimeError(
                            f"unexpected native outcome; replay: {replay}; {outcome.stdout}"
                        )
                count += 1
    print(
        f"live mixed correlation passed: {count} seeded conversations, 9 operations each"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int)
    parser.add_argument("--pdu", type=int, choices=(240, 480))
    parser.add_argument("--terminal", choices=("overflow", "protocol"))
    run(Path(__file__).resolve().parents[1], **vars(parser.parse_args()))
