"""Run the Lean client against an in-process python-snap7 emulator."""

from __future__ import annotations

import socket
import struct
import subprocess
import threading
import time
from pathlib import Path

from snap7.s7protocol import S7Area, S7Function, S7PDUType, S7WordLen
from snap7.server import Server
from snap7.type import SrvArea


class MultiItemServer(Server):
    """Add multi-item handling missing from the python-snap7 3.0 emulator."""

    stale_once = False

    def __init__(self) -> None:
        super().__init__()
        self._lean_szl_fragments: dict[tuple[str, int], list[bytes]] = {}
        self._lean_block_fragments: dict[tuple[str, int], list[bytes]] = {}
        self._upload_contexts: dict[tuple[str, int], dict] = {}

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

    def _parse_address_specification(self, addr_spec: bytes) -> dict:
        spec = super()._parse_address_specification(addr_spec)
        if spec and spec["word_len"] in (S7WordLen.TIMER, S7WordLen.COUNTER):
            # Model-fixture convention: Lean uses direct byte offsets here.
            # The pinned emulator divides these by eight like DB bit addresses.
            # This override tests assembly, not independent PLC compatibility.
            spec["start"] = int.from_bytes(addr_spec[9:12], "big")
        return spec

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
        if count == 1 and request["raw_parameters"][5] not in (
            S7WordLen.TIMER,
            S7WordLen.COUNTER,
        ):
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
        if count == 1 and request["raw_parameters"][5] not in (
            S7WordLen.TIMER,
            S7WordLen.COUNTER,
        ):
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
            ids = [0x0000, 0x0011, 0x001C, 0x0025, 0x0131, 0x0232, 0x0424]
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
        if szl_id == 0x0025:
            return self._szl_record(
                8,
                [
                    struct.pack(">HHBBH", 0x81, 12, 3, 1, 0),
                    struct.pack(">HHBBH", 0x82, 20, 7, 0, 0),
                ],
            )
        return None

    @staticmethod
    def _userdata_fragment_response(
        request: dict,
        sequence: int,
        has_more: bool,
        payload: bytes,
        group: int = 4,
        subfunction: int = 1,
    ) -> bytes:
        parameters = struct.pack(
            ">BBBBBBBBBBBB",
            0,
            1,
            0x12,
            8,
            0x12,
            0x80 | group,
            subfunction,
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

    def _handle_list_blocks_of_type(
        self,
        request: dict,
        userdata_params: dict,
        client_address: tuple[str, int],
    ) -> bytes:
        sequence = userdata_params.get("sequence", 0)
        if sequence:
            fragments = self._lean_block_fragments.get(client_address, [])
            if not fragments:
                return self._build_userdata_error_response(request, 0x8104)
            payload = fragments.pop(0)
            if not fragments:
                self._lean_block_fragments.pop(client_address, None)
            return self._userdata_fragment_response(
                request,
                sequence,
                bool(fragments),
                payload,
                group=3,
                subfunction=2,
            )
        raw_data = request.get("data", {}).get("data", b"")
        if raw_data != bytes([0x30, 0x41]):
            return self._build_userdata_error_response(request, 0x8104)
        fragments = [bytes([0, 1]), bytes([0, 0])]
        first = fragments.pop(0)
        self._lean_block_fragments[client_address] = fragments
        return self._userdata_fragment_response(
            request, 1, True, first, group=3, subfunction=2
        )

    def _handle_get_clock(
        self,
        request: dict,
        userdata_params: dict,
        client_address: tuple[str, int],
    ) -> bytes:
        # Stable real-S7 layout: reserved, century marker, then DATE_AND_TIME.
        payload = bytes([0, 0x19, 0x26, 0x09, 0x07, 0x14, 0x05, 0x59, 0, 1])
        return self._build_userdata_success_response(request, userdata_params, payload)

    def _handle_start_upload(
        self, request: dict, client_address: tuple[str, int]
    ) -> bytes:
        parameters = request["raw_parameters"]
        if len(parameters) != 18 or parameters[9:12] != b"_0A":
            return self._build_error_response(request, 0x8104)
        block_type = parameters[11]
        try:
            block_number = int(parameters[12:17])
        except ValueError:
            return self._build_error_response(request, 0x8104)
        area_key = (S7Area.DB, block_number)
        if block_type != 0x41 or area_key not in self.memory_areas:
            return self._build_error_response(request, 0x8104)
        mc7 = bytes(self.memory_areas[area_key])
        compact = bytearray(36)
        compact[3] = 0
        compact[4] = 0
        compact[5] = 0x0A
        struct.pack_into(">H", compact, 6, block_number)
        struct.pack_into(">I", compact, 8, len(compact) + len(mc7))
        struct.pack_into(">H", compact, 34, len(mc7))
        self._upload_contexts[client_address] = {
            "upload_id": 1,
            "payload": bytes(compact) + mc7,
            "offset": 0,
        }
        response_parameters = (
            bytes([S7Function.START_UPLOAD])
            + bytes(6)
            + bytes([1])
            + bytes(3)
            + f"{len(compact) + len(mc7):05d}".encode("ascii")
        )
        return self._standard_response(request, response_parameters, b"")

    @staticmethod
    def _standard_response(request: dict, parameters: bytes, data: bytes) -> bytes:
        return (
            struct.pack(
                ">BBHHHHBB",
                0x32,
                S7PDUType.ACK_DATA,
                0,
                request["sequence"],
                len(parameters),
                len(data),
                0,
                0,
            )
            + parameters
            + data
        )

    def _handle_upload(self, request: dict, client_address: tuple[str, int]) -> bytes:
        context = self._upload_contexts.get(client_address)
        if context is None:
            return self._build_error_response(request, 0x8104)
        offset = context["offset"]
        complete = context["payload"]
        chunk = complete[offset : offset + 200]
        context["offset"] = offset + len(chunk)
        is_last = context["offset"] == len(complete)
        parameters = bytes([S7Function.UPLOAD, 0 if is_last else 1])
        data = struct.pack(">HH", len(chunk), 0x00FB) + chunk
        return self._standard_response(request, parameters, data)


def free_port() -> int:
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return int(probe.getsockname()[1])


def hold_connection(listener: socket.socket) -> None:
    connection, _ = listener.accept()
    with connection:
        time.sleep(1)


def _receive_exact(connection: socket.socket, size: int) -> bytes:
    result = bytearray()
    while len(result) < size:
        chunk = connection.recv(size - len(result))
        if not chunk:
            raise RuntimeError("peer closed an incomplete test frame")
        result.extend(chunk)
    return bytes(result)


def _receive_tpkt(connection: socket.socket) -> bytes:
    header = _receive_exact(connection, 4)
    version, reserved, length = struct.unpack(">BBH", header)
    if version != 3 or reserved != 0 or length < 4:
        raise RuntimeError("invalid TPKT test frame")
    return _receive_exact(connection, length - 4)


def _send_tpkt(connection: socket.socket, payload: bytes) -> None:
    connection.sendall(struct.pack(">BBH", 3, 0, len(payload) + 4) + payload)


def _receive_s7(connection: socket.socket) -> bytes:
    cotp = _receive_tpkt(connection)
    if cotp[:3] != bytes([2, 0xF0, 0x80]):
        raise RuntimeError("expected a COTP data TPDU")
    return cotp[3:]


def _send_s7(connection: socket.socket, pdu: bytes) -> None:
    _send_tpkt(connection, bytes([2, 0xF0, 0x80]) + pdu)


def _send_s7_segmented(connection: socket.socket, pdu: bytes, split_at: int) -> None:
    _send_tpkt(connection, bytes([2, 0xF0, 0x00]) + pdu[:split_at])
    _send_tpkt(connection, bytes([2, 0xF0, 0x80]) + pdu[split_at:])


def _s7_response(reference: int, parameters: bytes, data: bytes = b"") -> bytes:
    return (
        struct.pack(
            ">BBHHHHBB",
            0x32,
            S7PDUType.ACK_DATA,
            0,
            reference,
            len(parameters),
            len(data),
            0,
            0,
        )
        + parameters
        + data
    )


def _s7_job(reference: int, parameters: bytes) -> bytes:
    return (
        struct.pack(">BBHHHH", 0x32, 1, 0, reference, len(parameters), 0) + parameters
    )


def serve_plc_driven_download(
    listener: socket.socket, expected: bytes, errors: list[Exception]
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(2)
            cr = _receive_tpkt(connection)
            if len(cr) < 7 or cr[1] != 0xE0:
                raise RuntimeError("expected COTP connection request")
            cc = bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:]
            _send_tpkt(connection, cc)
            setup = _receive_s7(connection)
            setup_reference = struct.unpack(">H", setup[4:6])[0]
            _send_s7(
                connection,
                _s7_response(
                    setup_reference,
                    bytes([0xF0, 0, 0, 1, 0, 1, 1, 0xE0]),
                ),
            )
            start = _receive_s7(connection)
            start_reference = struct.unpack(">H", start[4:6])[0]
            _send_s7(connection, _s7_response(start_reference, bytes([0x1A])))
            received = bytearray()
            sequence = 0x7000
            while len(received) < len(expected):
                _send_s7(connection, _s7_job(sequence, bytes([0x1B])))
                response = _receive_s7(connection)
                parameter_length = struct.unpack(">H", response[6:8])[0]
                data_length = struct.unpack(">H", response[8:10])[0]
                parameters = response[12 : 12 + parameter_length]
                data = response[
                    12 + parameter_length : 12 + parameter_length + data_length
                ]
                if (
                    struct.unpack(">H", response[4:6])[0] != sequence
                    or parameters[0] != 0x1B
                ):
                    raise RuntimeError("invalid download-fragment response")
                declared = struct.unpack(">H", data[:2])[0]
                if data[2:4] != bytes([0, 0xFB]) or declared != len(data) - 4:
                    raise RuntimeError("invalid download-fragment data header")
                received.extend(data[4:])
                sequence += 1
            if bytes(received) != expected:
                raise RuntimeError("downloaded block data mismatch")
            _send_s7(connection, _s7_job(sequence, bytes([0x1C])))
            ended = _receive_s7(connection)
            if ended[12:] != bytes([0x1C]):
                raise RuntimeError("invalid download-ended response")
            insert = _receive_s7(connection)
            insert_reference = struct.unpack(">H", insert[4:6])[0]
            if b"_INSE" not in insert:
                raise RuntimeError("download did not insert the transferred block")
            _send_s7(connection, _s7_response(insert_reference, bytes([0x28])))
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_download_integration(root: Path) -> None:
    mc7 = bytes((index * 29 + 7) & 0xFF for index in range(600))
    expected = bytes(34) + struct.pack(">H", len(mc7)) + mc7
    errors: list[Exception] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        port = int(listener.getsockname()[1])
        thread = threading.Thread(
            target=serve_plc_driven_download,
            args=(listener, expected, errors),
        )
        thread.start()
        subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-download",
                "127.0.0.1",
                str(port),
            ],
            cwd=root,
            check=True,
        )
        thread.join(timeout=3)
    if thread.is_alive():
        raise RuntimeError("PLC-driven download server did not finish")
    if errors:
        raise errors[0]


def serve_segmented_responses(listener: socket.socket, errors: list[Exception]) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(2)
            cr = _receive_tpkt(connection)
            if len(cr) < 7 or cr[1] != 0xE0:
                raise RuntimeError("expected COTP connection request")
            cc = bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:]
            _send_tpkt(connection, cc)
            setup = _receive_s7(connection)
            setup_reference = struct.unpack(">H", setup[4:6])[0]
            setup_response = _s7_response(
                setup_reference, bytes([0xF0, 0, 0, 1, 0, 1, 1, 0xE0])
            )
            _send_s7_segmented(connection, setup_response, 7)
            read = _receive_s7(connection)
            read_reference = struct.unpack(">H", read[4:6])[0]
            read_response = _s7_response(
                read_reference,
                bytes([0x04, 1]),
                bytes([0xFF, 0x04, 0, 32, 0xDE, 0xAD, 0xBE, 0xEF]),
            )
            _send_s7_segmented(connection, read_response, 13)
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_segmented_integration(root: Path) -> None:
    errors: list[Exception] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        port = int(listener.getsockname()[1])
        thread = threading.Thread(
            target=serve_segmented_responses,
            args=(listener, errors),
        )
        thread.start()
        subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-segmented",
                "127.0.0.1",
                str(port),
            ],
            cwd=root,
            check=True,
        )
        thread.join(timeout=3)
    if thread.is_alive():
        raise RuntimeError("segmented COTP server did not finish")
    if errors:
        raise errors[0]


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    port = free_port()
    areas = {
        (SrvArea.DB, 1): bytearray(4096),
        (SrvArea.PE, 0): bytearray(256),
        (SrvArea.PA, 0): bytearray(256),
        (SrvArea.MK, 0): bytearray(256),
        (SrvArea.CT, 0): bytearray(2048),
        (SrvArea.TM, 0): bytearray(2048),
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
        expected_elements = bytes((index * 37 + 11) % 256 for index in range(1000))
        for area in (SrvArea.CT, SrvArea.TM):
            if areas[(area, 0)][16:1016] != expected_elements:
                raise AssertionError(
                    "chunked write did not preserve source bytes at the destination"
                )
            if any(areas[(area, 0)][1016:]):
                raise AssertionError("chunked write modified bytes beyond the payload")
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
        run_download_integration(root)
        run_segmented_integration(root)
    finally:
        server.stop()
        server.destroy()


if __name__ == "__main__":
    main()
