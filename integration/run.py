"""Run the Lean client against an in-process python-snap7 emulator."""

from __future__ import annotations

import socket
import subprocess
from pathlib import Path

from snap7.server import Server
from snap7.type import SrvArea


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return int(probe.getsockname()[1])


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    port = free_port()
    data = bytearray(256)
    data[:4] = b"\xaa\xbb\xcc\xdd"
    server = Server()
    server.register_area(SrvArea.DB, 1, data)
    server.start_to("127.0.0.1", port)
    try:
        subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration",
                "127.0.0.1",
                str(port),
            ],
            cwd=root,
            check=True,
        )
    finally:
        server.stop()
        server.destroy()


if __name__ == "__main__":
    main()
