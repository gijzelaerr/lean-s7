"""Run the Lean client against an in-process python-snap7 emulator."""

from __future__ import annotations

import socket
import struct
import subprocess
from pathlib import Path

from snap7.s7protocol import S7Function, S7PDUType, S7WordLen
from snap7.server import Server
from snap7.type import SrvArea


class MultiItemServer(Server):
    """Add multi-item handling missing from the python-snap7 3.0 emulator."""

    def _parse_request(self, pdu: bytes) -> dict:
        request = super()._parse_request(pdu)
        _, _, _, _, parameter_length, data_length = struct.unpack(">BBHHHH", pdu[:10])
        data_start = 10 + parameter_length
        request["raw_data"] = pdu[data_start : data_start + data_length]
        return request

    @staticmethod
    def _word_size(word_length: int) -> int:
        if word_length in (S7WordLen.TIMER, S7WordLen.COUNTER, S7WordLen.WORD):
            return 2
        if word_length in (S7WordLen.DWORD, S7WordLen.REAL):
            return 4
        return 1

    def _multi_specs(self, request: dict) -> list[dict]:
        parameters = request["raw_parameters"]
        count = parameters[1]
        return [
            self._parse_address_specification(
                parameters[2 + index * 12 : 14 + index * 12]
            )
            for index in range(count)
        ]

    @staticmethod
    def _response_header(
        request: dict, function: int, count: int, data: bytes
    ) -> bytes:
        return (
            struct.pack(
                ">BBHHHHBB",
                0x32,
                S7PDUType.ACK_DATA,
                0,
                request["sequence"],
                2,
                len(data),
                0,
                0,
            )
            + struct.pack(">BB", function, count)
            + data
        )

    def _handle_read_area(
        self, request: dict, client_address: tuple[str, int]
    ) -> bytes:
        count = request["raw_parameters"][1]
        if count == 1:
            return super()._handle_read_area(request, client_address)
        data = bytearray()
        specs = self._multi_specs(request)
        for index, spec in enumerate(specs):
            size = spec["count"] * self._word_size(spec["word_len"])
            payload = self._read_from_memory_area(
                spec["area"], spec["db_number"], spec["start"], size
            )
            if payload is None:
                data.extend(struct.pack(">BBH", 0x0A, 0, 0))
                continue
            transport = (
                0x09
                if spec["word_len"] in (S7WordLen.TIMER, S7WordLen.COUNTER)
                else 0x04
            )
            encoded_length = len(payload) if transport == 0x09 else len(payload) * 8
            data.extend(struct.pack(">BBH", 0xFF, transport, encoded_length))
            data.extend(payload)
            if index + 1 < count and len(payload) % 2:
                data.append(0)
        return self._response_header(request, S7Function.READ_AREA, count, bytes(data))

    def _handle_write_area(
        self, request: dict, client_address: tuple[str, int]
    ) -> bytes:
        count = request["raw_parameters"][1]
        if count == 1:
            return super()._handle_write_area(request, client_address)
        data = request["raw_data"]
        offset = 0
        results = bytearray()
        specs = self._multi_specs(request)
        for index, spec in enumerate(specs):
            _, transport, encoded_length = struct.unpack(
                ">BBH", data[offset : offset + 4]
            )
            size = encoded_length if transport == 0x09 else encoded_length // 8
            payload = data[offset + 4 : offset + 4 + size]
            success = self._write_to_memory_area(
                spec["area"], spec["db_number"], spec["start"], payload
            )
            results.append(0xFF if success else 0x0A)
            offset += 4 + size
            if index + 1 < count and size % 2:
                offset += 1
        return self._response_header(
            request, S7Function.WRITE_AREA, count, bytes(results)
        )


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
    server = MultiItemServer()
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
