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
    areas = {
        (SrvArea.DB, 1): bytearray(4096),
        (SrvArea.PE, 0): bytearray(256),
        (SrvArea.PA, 0): bytearray(256),
        (SrvArea.MK, 0): bytearray(256),
        (SrvArea.CT, 0): bytearray(256),
        (SrvArea.TM, 0): bytearray(256),
    }
    areas[(SrvArea.DB, 1)][:4] = b"\xaa\xbb\xcc\xdd"
    areas[(SrvArea.PE, 0)][:4] = b"\x11\x12\x13\x14"
    server = Server()
    for (area, index), data in areas.items():
        server.register_area(area, index, data)
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
