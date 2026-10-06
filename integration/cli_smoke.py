"""Exercise the lean-s7-cli binary against an in-process python-snap7 emulator.

Localhost only. Checks the documented contract: reads work, typed values decode,
every mutating command is refused without --allow-write (before any connection),
writes are acknowledged and readable, and bad input fails with a nonzero status.
"""

from __future__ import annotations

import socket
import subprocess
import sys
from pathlib import Path

from snap7.server import Server
from snap7.type import SrvArea

ROOT = Path(__file__).resolve().parent.parent
CLI = (
    ROOT
    / ".lake"
    / "build"
    / "bin"
    / ("lean-s7-cli.exe" if sys.platform == "win32" else "lean-s7-cli")
)


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return int(probe.getsockname()[1])


def run(port: int, *args: str, timeout: float = 30) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            str(CLI),
            "--host",
            "127.0.0.1",
            "--port",
            str(port),
            "--timeout-ms",
            "3000",
            *args,
        ],
        capture_output=True,
        text=True,
        timeout=timeout,
        check=False,
    )


def expect(
    condition: bool, label: str, result: subprocess.CompletedProcess[str] | None = None
) -> None:
    if not condition:
        detail = (
            f"\nstdout={result.stdout!r}\nstderr={result.stderr!r}" if result else ""
        )
        raise AssertionError(f"cli: {label}{detail}")


def main() -> int:
    if not CLI.exists():
        print(f"missing {CLI}; run `lake build lean-s7-cli` first", file=sys.stderr)
        return 1
    database = bytearray(64)
    database[0:8] = bytes([0x12, 0x34, 0xFF, 0xFE, 0x40, 0x49, 0x0F, 0xDB])
    server = Server()
    server.register_area(SrvArea.DB, 1, database)
    server.register_area(SrvArea.MK, 0, bytearray(16))
    port = free_port()
    server.start(tcp_port=port)
    try:
        result = run(port, "read", "db", "1", "0", "8")
        expect(
            result.returncode == 0 and result.stdout.strip() == "1234fffe40490fdb",
            "raw read",
            result,
        )
        for spec, want in (("u16", "4660"), ("bit:4", "true")):
            result = run(port, "read", "db", "1", "0", "--as", spec)
            expect(
                result.returncode == 0 and result.stdout.strip() == want,
                f"typed read {spec}",
                result,
            )
        result = run(port, "read", "db", "1", "2", "--as", "i16")
        expect(result.stdout.strip() == "-2", "signed typed read", result)
        result = run(port, "read", "db", "1", "4", "--as", "real")
        expect(result.stdout.strip().startswith("3.14159"), "real typed read", result)

        # Every mutating command is refused locally, before any controller access.
        for command in (
            ("write", "db", "1", "10", "deadbeef"),
            ("cpu", "stop"),
            ("cpu", "hot-start"),
            ("cpu", "cold-start"),
            ("blocks", "delete", "db", "1"),
        ):
            result = run(
                0, *command
            )  # port 0 would fail to connect if it were attempted
            expect(
                result.returncode != 0 and "--allow-write" in result.stderr,
                f"gate {command}",
                result,
            )
            expect(
                "connection" not in result.stderr,
                f"gate before connect {command}",
                result,
            )
        expect(database[10:14] == bytes(4), "refused write left memory unchanged")

        result = run(port, "--allow-write", "write", "db", "1", "10", "deadbeef")
        expect(
            result.returncode == 0
            and bytes(database[10:14]) == bytes.fromhex("deadbeef"),
            "write",
            result,
        )
        result = run(port, "read", "db", "1", "10", "4")
        expect(result.stdout.strip() == "deadbeef", "read back", result)
        result = run(
            port, "--allow-write", "write", "db", "1", "20", "--as", "i16", "-2"
        )
        expect(bytes(database[20:22]) == b"\xff\xfe", "typed write", result)

        # Invalid input fails cleanly.
        for bad in (
            ("--allow-write", "write", "db", "1", "20", "--as", "u8", "300"),
            ("read", "db", "1", "0", "--as", "nonsense"),
            ("read", "zz", "0", "1"),
            ("read", "db", "1", "x", "1"),
            ("blocks", "info", "xx", "1"),
        ):
            result = run(port, *bad)
            expect(
                result.returncode != 0
                and result.stderr.strip().splitlines()[-1].startswith("error:"),
                f"bad {bad}",
                result,
            )
        result = subprocess.run(
            [str(CLI), "state"], capture_output=True, text=True, check=False
        )
        expect(
            result.returncode != 0 and "--host is required" in result.stderr,
            "host required",
            result,
        )
        result = subprocess.run(
            [str(CLI), "--help"], capture_output=True, text=True, check=False
        )
        expect(
            result.returncode == 0 and "not been validated" in result.stdout,
            "help warns",
            result,
        )
    finally:
        server.stop()
    print("cli smoke tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
