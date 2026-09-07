"""Run the Lean client against an in-process python-snap7 emulator."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
import time
from pathlib import Path

from snap7.s7protocol import S7Function, S7PDUType, S7WordLen
from snap7.server import Server
from snap7.type import SrvArea


class MultiItemServer(Server):
    """Add multi-item handling missing from the python-snap7 3.0 emulator."""

    stale_once = False

    def __init__(self) -> None:
        super().__init__()
        self._lean_szl_fragments: dict[tuple[str, int], list[bytes]] = {}

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
            response = super()._handle_read_area(request, client_address)
            if self.stale_once:
                self.stale_once = False
                stale = bytearray(response)
                stale[4:6] = struct.pack(">H", (request["sequence"] + 1) & 0xFFFF)
                return bytes(stale)
            return response
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

    @staticmethod
    def _szl_record(record_length: int, records: list[bytes]) -> bytes:
        assert all(len(record) == record_length for record in records)
        return struct.pack(">HH", record_length, len(records)) + b"".join(records)

    def _get_szl_data(self, szl_id: int, szl_index: int) -> bytes | None:
        if szl_id == 0x0000:
            ids = [0x0000, 0x0011, 0x001C, 0x0131, 0x0232, 0x0424]
            return self._szl_record(2, [struct.pack(">H", value) for value in ids])
        if szl_id == 0x0011:
            code = b"6ES7 315-2EH14-0AB0"[:20].ljust(20, b"\x00")
            return self._szl_record(
                26, [struct.pack(">H", 1) + code + bytes([0, 3, 3, 0])]
            )
        if szl_id == 0x001C:
            values = [
                b"SNAP7-SERVER",
                b"CPU 315-2 PN/DP",
                b"unused",
                b"Original Siemens Equipment",
                b"S C-C2UR28922012",
                b"CPU 315-2 PN/DP",
            ]
            records = [
                struct.pack(">H", index + 1) + value[:32].ljust(32, b"\x00")
                for index, value in enumerate(values)
            ]
            return self._szl_record(34, records)
        if szl_id == 0x0131 and szl_index == 1:
            return self._szl_record(
                14, [struct.pack(">HHHII", 1, 480, 32, 12_000_000, 100_000_000)]
            )
        if szl_id == 0x0232 and szl_index == 4:
            return self._szl_record(12, [struct.pack(">HHHHHH", 4, 1, 0, 0, 2, 0)])
        if szl_id == 0x0424:
            status = int(self.cpu_state)
            return self._szl_record(4, [struct.pack(">HBB", 0, 0, status)])
        return None

    @staticmethod
    def _userdata_fragment_response(
        request: dict, sequence: int, has_more: bool, payload: bytes
    ) -> bytes:
        parameters = struct.pack(
            ">BBBBBBBBBBBB",
            0,
            1,
            0x12,
            8,
            0x12,
            0x84,
            1,
            sequence,
            1 if sequence else 0,
            1 if has_more else 0,
            0,
            0,
        )
        data = struct.pack(">BBH", 0xFF, 9, len(payload)) + payload
        return (
            struct.pack(
                ">BBHHHH",
                0x32,
                S7PDUType.USERDATA,
                0,
                request["sequence"],
                len(parameters),
                len(data),
            )
            + parameters
            + data
        )

    def _handle_szl(
        self,
        request: dict,
        userdata_params: dict,
        client_address: tuple[str, int],
    ) -> bytes:
        sequence = userdata_params.get("sequence", 0)
        if sequence:
            fragments = self._lean_szl_fragments.get(client_address, [])
            if not fragments:
                return self._build_userdata_error_response(request, 0x8104)
            payload = fragments.pop(0)
            if not fragments:
                self._lean_szl_fragments.pop(client_address, None)
            return self._userdata_fragment_response(
                request, sequence, bool(fragments), payload
            )
        raw_data = request.get("data", {}).get("data", b"")
        if len(raw_data) < 4:
            return self._build_userdata_error_response(request, 0x8104)
        szl_id, szl_index = struct.unpack(">HH", raw_data[:4])
        szl_data = self._get_szl_data(szl_id, szl_index)
        if szl_data is None:
            return self._build_userdata_error_response(request, 0x8104)
        complete = struct.pack(">HH", szl_id, szl_index) + szl_data
        chunks = [complete[index : index + 48] for index in range(0, len(complete), 48)]
        first = chunks.pop(0)
        if chunks:
            self._lean_szl_fragments[client_address] = chunks
        return self._userdata_fragment_response(request, 1, bool(chunks), first)

    def _handle_get_clock(
        self,
        request: dict,
        userdata_params: dict,
        client_address: tuple[str, int],
    ) -> bytes:
        # Stable real-S7 layout: reserved, century marker, then DATE_AND_TIME.
        payload = bytes([0, 0x19, 0x26, 0x09, 0x07, 0x14, 0x05, 0x59, 0, 1])
        return self._build_userdata_success_response(request, userdata_params, payload)


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return int(probe.getsockname()[1])


def hold_connection(listener: socket.socket) -> None:
    connection, _ = listener.accept()
    with connection:
        time.sleep(1)


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
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            stalled_port = int(listener.getsockname()[1])
            thread = threading.Thread(target=hold_connection, args=(listener,))
            thread.start()
            subprocess.run(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "expect-connect-failure",
                    "localhost",
                    str(stalled_port),
                ],
                cwd=root,
                check=True,
            )
            thread.join(timeout=2)
        try:
            with socket.socket(socket.AF_INET6) as listener:
                listener.bind(("::1", 0))
                listener.listen(1)
                stalled_port = int(listener.getsockname()[1])
                thread = threading.Thread(target=hold_connection, args=(listener,))
                thread.start()
                subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "expect-connect-failure",
                        "::1",
                        str(stalled_port),
                    ],
                    cwd=root,
                    check=True,
                )
                thread.join(timeout=2)
        except OSError:
            pass
        server.stale_once = True
        subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-reconnect",
                "localhost",
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
