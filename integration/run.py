"""Run the Lean client against an in-process python-snap7 emulator."""

from __future__ import annotations

import select
import socket
import struct
import subprocess
import threading
import time
from pathlib import Path

import sequence_conformance
from boundary_operations import run_boundary_operations
from clock_assurance import run_clock_assurance
from compound_operations import run_compound_operations
from concurrency import run_concurrency
from connection_budget import run_connection_budget
from conversation_conformance import run as run_conversation_conformance
from extended_deadlines import run_extended_deadlines
from mixed_operations import run_mixed_operations
from multi_batching import run_multi_batching
from multi_semantics import run_multi_semantics
from operation_conformance import run as run_operation_conformance
from overlap_operations import run_overlap_operations
from queued_batches import run_queued_batches
from queued_lifecycle import run_queued_lifecycle
from resource_stress import run_resource_stress
from retry_budgets import run_retry_budgets
from retry_progress import run_retry_progress
from snap7.s7protocol import S7Area, S7Function, S7PDUType, S7WordLen
from snap7.server import Server
from snap7.type import SrvArea
from stateful_faults import run_stateful_faults
from timeout_cleanup import run_timeout_cleanup
from transfer_deadlines import run_transfer_deadlines
from transport_resources import run_transport_resources
from userdata_completion import run_userdata_completion
from value_conformance import run as run_value_conformance
from write_provenance import run_write_provenance


class MultiItemServer(Server):
    """Add multi-item handling missing from the python-snap7 3.0 emulator."""

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


def _s7_job(reference: int, parameters: bytes, data: bytes = b"") -> bytes:
    return (
        struct.pack(">BBHHHH", 0x32, 1, 0, reference, len(parameters), len(data))
        + parameters
        + data
    )


def serve_handshake_rejection(
    listener: socket.socket, mode: str, errors: list[Exception]
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(2)
            cr = _receive_tpkt(connection)
            cc = bytearray([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + bytearray(cr[7:])
            if mode == "wrong-reference":
                reference = (int.from_bytes(cr[4:6], "big") + 1) & 0xFFFF
                cc[2:4] = reference.to_bytes(2, "big")
            elif mode == "wrong-class":
                cc[6] = 1
            elif mode == "oversized-tpdu":
                cc[-1] = 0x0B
            elif mode == "pdu-too-small":
                pass
            elif mode == "pdu-exceeds-tpdu":
                cc[-1] = 0x08
            else:
                raise ValueError(f"unknown handshake case: {mode}")
            _send_tpkt(connection, bytes(cc))
            if mode in ("pdu-too-small", "pdu-exceeds-tpdu"):
                setup = _receive_s7(connection)
                reference = int.from_bytes(setup[4:6], "big")
                pdu_length = 239 if mode == "pdu-too-small" else 480
                _send_s7(
                    connection,
                    _s7_response(
                        reference,
                        bytes([0xF0, 0, 0, 1, 0, 1]) + pdu_length.to_bytes(2, "big"),
                    ),
                )
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_handshake_rejections(root: Path) -> None:
    for mode, expected in (
        ("wrong-reference", "expected COTP destination reference"),
        ("wrong-class", "expected COTP class option"),
        ("oversized-tpdu", "exceeds requested"),
        ("pdu-too-small", "negotiated PDU length is too small"),
        ("pdu-exceeds-tpdu", "cannot contain 480 payload bytes"),
    ):
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.settimeout(3)
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            thread = threading.Thread(
                target=serve_handshake_rejection, args=(listener, mode, errors)
            )
            thread.start()
            subprocess.run(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "expect-connect-rejection",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                    expected,
                ],
                cwd=root,
                check=True,
                timeout=5,
            )
            thread.join(timeout=3)
        if thread.is_alive():
            raise RuntimeError(f"handshake peer did not finish: {mode}")
        if errors:
            raise errors[0]


def _userdata_response(
    reference: int,
    group: int,
    subfunction: int,
    payload: bytes,
    *,
    declared_length: int | None = None,
    sequence: int = 0,
    has_more_data: bool = False,
    error_code: int = 0,
) -> bytes:
    parameters = bytes(
        [
            0,
            1,
            0x12,
            8,
            0x12,
            0x80 | group,
            subfunction,
            sequence,
            0,
            int(has_more_data),
            (error_code >> 8) & 0xFF,
            error_code & 0xFF,
        ]
    )
    length = len(payload) if declared_length is None else declared_length
    data = bytes([0xFF, 9]) + length.to_bytes(2, "big") + payload
    return (
        struct.pack(">BBHHHH", 0x32, 7, 0, reference, len(parameters), len(data))
        + parameters
        + data
    )


def serve_service_rejection(
    listener: socket.socket, mode: str, errors: list[Exception]
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(3)
            cr = _receive_tpkt(connection)
            _send_tpkt(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
            setup = _receive_s7(connection)
            reference = int.from_bytes(setup[4:6], "big")
            _send_s7(
                connection,
                _s7_response(reference, bytes([0xF0, 0, 0, 1, 0, 1, 1, 0xE0])),
            )
            request = _receive_s7(connection)
            reference = int.from_bytes(request[4:6], "big")
            if mode == "szl-wrong-group":
                _send_s7(
                    connection,
                    _userdata_response(reference, 3, 1, bytes([4, 0x24, 0, 0])),
                )
                return
            if mode in ("szl-invalid-flag-two", "szl-invalid-flag-ff"):
                flag = 2 if mode.endswith("two") else 0xFF
                packet = bytearray(
                    _userdata_response(reference, 4, 1, bytes([4, 0x24, 0, 0]))
                )
                packet[19] = flag
                _send_s7(connection, bytes(packet))
                return
            if mode == "szl-truncated-payload":
                _send_s7(
                    connection,
                    _userdata_response(reference, 4, 1, b"\xaa\xbb", declared_length=4),
                )
                return
            if mode == "szl-invalid-final-records":
                _send_s7(
                    connection,
                    _userdata_response(
                        reference, 4, 1, bytes([4, 0x24, 0, 0, 0, 4, 0, 1, 0xAA])
                    ),
                )
                return
            if mode == "userdata-invalid-final-entries":
                _send_s7(
                    connection,
                    _userdata_response(reference, 3, 2, b"\xaa"),
                )
                return
            if mode == "szl-plc-error":
                _send_s7(
                    connection,
                    _userdata_response(reference, 4, 1, b"", error_code=0x8104),
                )
                listener.settimeout(0.5)
                try:
                    retried, _ = listener.accept()
                except TimeoutError:
                    pass
                else:
                    retried.close()
                    raise RuntimeError("client retried a PLC-rejected request")
                return
            if mode == "szl-endless-fragments":
                for fragment in range(256):
                    payload = b"\x04\x24\x00\x00" if fragment == 0 else b""
                    _send_s7(
                        connection,
                        _userdata_response(
                            reference,
                            4,
                            1,
                            payload,
                            sequence=fragment & 0xFF,
                            has_more_data=True,
                        ),
                    )
                    if fragment != 255:
                        request = _receive_s7(connection)
                        reference = int.from_bytes(request[4:6], "big")
                return
            if not mode.startswith("upload-"):
                raise ValueError(f"unknown service rejection case: {mode}")
            legacy_modes = {
                "upload-invalid-marker",
                "upload-length-mismatch",
                "upload-wrong-function",
            }
            start_parameters = bytes([0x1D]) + bytes(6) + bytes([1])
            if mode not in legacy_modes:
                declared = 2 if mode == "upload-end-bad-ack" else 4
                start_parameters += bytes(3) + f"{declared:05d}".encode("ascii")
            _send_s7(
                connection,
                _s7_response(reference, start_parameters),
            )
            upload = _receive_s7(connection)
            reference = int.from_bytes(upload[4:6], "big")
            if mode == "upload-invalid-marker":
                parameters = bytes([0x1E, 0])
                data = b"\x00\x02\x00\xfa\xde\xad"
            elif mode == "upload-length-mismatch":
                parameters = bytes([0x1E, 0])
                data = b"\x00\x03\x00\xfb\xde\xad"
            elif mode == "upload-wrong-function":
                parameters = bytes([0x1D, 0])
                data = b"\x00\x02\x00\xfb\xde\xad"
            elif mode in ("upload-invalid-flag", "upload-cleanup-bad-ack"):
                parameters = bytes([0x1E, 2])
                data = b"\x00\x02\x00\xfb\xde\xad"
            elif mode == "upload-empty-continuation":
                parameters = bytes([0x1E, 1])
                data = b"\x00\x00\x00\xfb"
            elif mode == "upload-short-final":
                parameters = bytes([0x1E, 0])
                data = b"\x00\x02\x00\xfb\xde\xad"
            elif mode == "upload-long-final":
                parameters = bytes([0x1E, 0])
                data = b"\x00\x05\x00\xfb\x01\x02\x03\x04\x05"
            elif mode == "upload-more-at-declared-length":
                parameters = bytes([0x1E, 1])
                data = b"\x00\x04\x00\xfb\x01\x02\x03\x04"
            elif mode in ("upload-midstream-short", "upload-midstream-overflow"):
                _send_s7(
                    connection,
                    _s7_response(
                        reference, bytes([0x1E, 1]), b"\x00\x02\x00\xfb\x01\x02"
                    ),
                )
                upload = _receive_s7(connection)
                reference = int.from_bytes(upload[4:6], "big")
                if upload[10] != 0x1E or upload[17] != 1:
                    raise RuntimeError(
                        "upload continuation used the wrong function or ID"
                    )
                chunk = b"\x03" if mode == "upload-midstream-short" else b"\x03\x04\x05"
                parameters = bytes([0x1E, 0])
                data = struct.pack(">HH", len(chunk), 0x00FB) + chunk
            elif mode == "upload-end-bad-ack":
                parameters = bytes([0x1E, 0])
                data = b"\x00\x02\x00\xfb\xde\xad"
            else:
                raise ValueError(f"unknown service rejection case: {mode}")
            _send_s7(connection, _s7_response(reference, parameters, data))
            cleanup = _receive_s7(connection)
            if cleanup[10] != 0x1F or cleanup[17] != 1:
                raise RuntimeError(
                    "client omitted end-upload cleanup or used the wrong ID"
                )
            cleanup_reference = int.from_bytes(cleanup[4:6], "big")
            end_parameters = (
                bytes([0x1F, 0])
                if mode in ("upload-end-bad-ack", "upload-cleanup-bad-ack")
                else bytes([0x1F])
            )
            _send_s7(connection, _s7_response(cleanup_reference, end_parameters))
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_service_rejections(root: Path) -> None:
    for mode, operation, expected in (
        ("szl-wrong-group", "szl", "unexpected USER_DATA type or function group"),
        ("szl-invalid-flag-two", "szl", "invalid USER_DATA continuation flag"),
        ("szl-invalid-flag-ff", "szl", "invalid USER_DATA continuation flag"),
        ("szl-truncated-payload", "szl", "unexpectedEnd"),
        ("szl-invalid-final-records", "szl", "SZL header describes"),
        (
            "userdata-invalid-final-entries",
            "userdata",
            "not aligned to four-byte entries",
        ),
        ("szl-plc-error", "szl", "request failed with code"),
        ("szl-endless-fragments", "szl", "256-fragment safety limit"),
        ("upload-invalid-marker", "upload", "invalid upload data marker"),
        (
            "upload-length-mismatch",
            "upload",
            "upload data length does not match its section",
        ),
        ("upload-wrong-function", "upload", "unexpected S7 response function"),
        ("upload-invalid-flag", "upload", "invalid upload continuation flag"),
        ("upload-empty-continuation", "upload", "made no progress"),
        ("upload-short-final", "upload", "does not match the declared block length"),
        ("upload-long-final", "upload", "exceeds the declared block length"),
        (
            "upload-more-at-declared-length",
            "upload",
            "reached the declared block length",
        ),
        (
            "upload-midstream-short",
            "upload",
            "does not match the declared block length",
        ),
        ("upload-midstream-overflow", "upload", "exceeds the declared block length"),
        ("upload-end-bad-ack", "upload", "invalid end-upload response"),
        ("upload-cleanup-bad-ack", "upload", "invalid upload continuation flag"),
    ):
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.settimeout(3)
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            thread = threading.Thread(
                target=serve_service_rejection, args=(listener, mode, errors)
            )
            thread.start()
            subprocess.run(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "integration-service-rejection",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                    operation,
                    expected,
                ],
                cwd=root,
                check=True,
                timeout=10,
            )
            thread.join(timeout=3)
        if thread.is_alive():
            raise RuntimeError(f"service rejection peer did not finish: {mode}")
        if errors:
            raise errors[0]


def _accept_session(listener: socket.socket, pdu_length: int) -> socket.socket:
    connection, _ = listener.accept()
    connection.settimeout(3)
    cr = _receive_tpkt(connection)
    _send_tpkt(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
    setup = _receive_s7(connection)
    reference = int.from_bytes(setup[4:6], "big")
    _send_s7(
        connection,
        _s7_response(
            reference,
            bytes([0xF0, 0, 0, 1, 0, 1]) + pdu_length.to_bytes(2, "big"),
        ),
    )
    return connection


def serve_reconnect_shrink(listener: socket.socket, errors: list[Exception]) -> None:
    try:
        with _accept_session(listener, 480) as connection:
            _receive_s7(connection)
        with _accept_session(listener, 240) as connection:
            disconnect = _receive_tpkt(connection)
            if len(disconnect) < 2 or disconnect[1] != 0x80:
                raise RuntimeError("shrinking reconnect was not disconnected")
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_reconnect_shrink(root: Path) -> None:
    errors: list[Exception] = []
    with socket.socket() as listener:
        listener.settimeout(3)
        listener.bind(("127.0.0.1", 0))
        listener.listen(2)
        thread = threading.Thread(
            target=serve_reconnect_shrink, args=(listener, errors)
        )
        thread.start()
        subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-reconnect-shrink",
                "127.0.0.1",
                str(listener.getsockname()[1]),
            ],
            cwd=root,
            check=True,
            timeout=10,
        )
        thread.join(timeout=3)
    if thread.is_alive():
        raise RuntimeError("shrinking-reconnect peer did not finish")
    if errors:
        raise errors[0]


def serve_reconnect_recovery(listener: socket.socket, errors: list[Exception]) -> None:
    try:
        with _accept_session(listener, 480) as first:
            first_request = _receive_s7(first)
            first_reference = int.from_bytes(first_request[4:6], "big")
        with _accept_session(listener, 480) as second:
            retried_request = _receive_s7(second)
            retried_reference = int.from_bytes(retried_request[4:6], "big")
            if retried_reference != first_reference or retried_request != first_request:
                raise RuntimeError("reconnect did not retry the original request")
            _send_s7(
                second,
                _s7_response(
                    retried_reference,
                    bytes([4, 1]),
                    bytes([0xFF, 4, 0, 32, 0xDE, 0xAD, 0xBE, 0xEF]),
                ),
            )
            disconnect = _receive_tpkt(second)
            if len(disconnect) < 2 or disconnect[1] != 0x80:
                raise RuntimeError("reconnect-recovery client omitted disconnect")
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_reconnect_recovery(root: Path) -> None:
    errors: list[Exception] = []
    with socket.socket() as listener:
        listener.settimeout(3)
        listener.bind(("127.0.0.1", 0))
        listener.listen(2)
        thread = threading.Thread(
            target=serve_reconnect_recovery, args=(listener, errors)
        )
        thread.start()
        subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-reconnect-recovery",
                "127.0.0.1",
                str(listener.getsockname()[1]),
            ],
            cwd=root,
            check=True,
            timeout=10,
        )
        thread.join(timeout=3)
    if thread.is_alive():
        raise RuntimeError("reconnect-recovery peer did not finish")
    if errors:
        raise errors[0]


def _download_service_params(function: int, block_number: int) -> bytes:
    return (
        bytes([function])
        + bytes(7)
        + b"\x09_0A"
        + f"{block_number:05d}".encode()
        + b"P"
    )


def serve_plc_driven_download(
    listener: socket.socket, expected: bytes, pdu_length: int, errors: list[Exception]
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
                    bytes([0xF0, 0, 0, 1, 0, 1]) + pdu_length.to_bytes(2, "big"),
                ),
            )
            start = _receive_s7(connection)
            start_reference = struct.unpack(">H", start[4:6])[0]
            _send_s7(connection, _s7_response(start_reference, bytes([0x1A])))
            received = bytearray()
            sequence = 0x7000
            while len(received) < len(expected):
                _send_s7(
                    connection, _s7_job(sequence, _download_service_params(0x1B, 7))
                )
                response = _receive_s7(connection)
                if len(response) > pdu_length:
                    raise RuntimeError("download fragment exceeded negotiated PDU")
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
            _send_s7(connection, _s7_job(sequence, _download_service_params(0x1C, 7)))
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
    for pdu_length in (240, 480):
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            port = int(listener.getsockname()[1])
            thread = threading.Thread(
                target=serve_plc_driven_download,
                args=(listener, expected, pdu_length, errors),
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


def serve_interrupted_download(
    listener: socket.socket, errors: list[Exception]
) -> None:
    try:
        with _accept_session(listener, 480) as connection:
            start = _receive_s7(connection)
            reference = int.from_bytes(start[4:6], "big")
            _send_s7(connection, _s7_response(reference, bytes([0x1A])))
            _send_s7(connection, _s7_job(0x7000, _download_service_params(0x1B, 7)))
            fragment = _receive_s7(connection)
            if fragment[12:13] != bytes([0x1B]):
                raise RuntimeError("interrupted download returned an invalid fragment")
            # Closing here interrupts the PLC-driven exchange between fragments.
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_download_interruption(root: Path) -> None:
    errors: list[Exception] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        thread = threading.Thread(
            target=serve_interrupted_download, args=(listener, errors)
        )
        thread.start()
        subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-download-interruption",
                "127.0.0.1",
                str(listener.getsockname()[1]),
            ],
            cwd=root,
            check=True,
            timeout=10,
        )
        thread.join(timeout=3)
    if thread.is_alive():
        raise RuntimeError("interrupted-download peer did not finish")
    if errors:
        raise errors[0]


def _expect_download_rejection(connection: socket.socket, mutation: str) -> None:
    connection.settimeout(2)
    try:
        received = _receive_tpkt(connection)
    except ConnectionResetError:
        return
    except RuntimeError as error:
        if str(error) == "peer closed an incomplete test frame":
            return
        raise
    if len(received) >= 2 and received[1] == 0xF0:
        raise RuntimeError(f"client accepted malformed {mutation} download job")


def serve_malformed_download_service(
    listener: socket.socket, mutation: str, errors: list[Exception]
) -> None:
    try:
        with _accept_session(listener, 480) as connection:
            start = _receive_s7(connection)
            reference = int.from_bytes(start[4:6], "big")
            if mutation == "ack-extra":
                _send_s7(connection, _s7_response(reference, bytes([0x1A, 0])))
            elif mutation == "ack-data":
                _send_s7(connection, _s7_response(reference, bytes([0x1A]), b"\x01"))
            else:
                _send_s7(connection, _s7_response(reference, bytes([0x1A])))
                parameters = bytearray(_download_service_params(0x1B, 7))
                data = b""
                if mutation == "wrong-block":
                    parameters[16] = ord("8")
                elif mutation == "reserved":
                    parameters[1] = 1
                elif mutation == "truncated":
                    parameters.pop()
                elif mutation == "data":
                    data = b"\x01"
                _send_s7(connection, _s7_job(0x7000, bytes(parameters), data))
            # The client must reject the job and close before sending block data.
            _expect_download_rejection(connection, mutation)
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def serve_invalid_download_phase(
    listener: socket.socket, mutation: str, errors: list[Exception]
) -> None:
    try:
        with _accept_session(listener, 480) as connection:
            start = _receive_s7(connection)
            reference = int.from_bytes(start[4:6], "big")
            _send_s7(connection, _s7_response(reference, bytes([0x1A])))
            sequence = 0x7000
            if mutation == "early-ended":
                _send_s7(
                    connection,
                    _s7_job(sequence, _download_service_params(0x1C, 7)),
                )
            else:
                received = bytearray()
                while len(received) < 636:
                    _send_s7(
                        connection,
                        _s7_job(sequence, _download_service_params(0x1B, 7)),
                    )
                    response = _receive_s7(connection)
                    if (
                        int.from_bytes(response[4:6], "big") != sequence
                        or response[12] != 0x1B
                    ):
                        raise RuntimeError("invalid response to valid download request")
                    parameter_length = int.from_bytes(response[6:8], "big")
                    data = response[12 + parameter_length :]
                    received.extend(data[4:])
                    sequence += 1
                _send_s7(
                    connection,
                    _s7_job(sequence, _download_service_params(0x1B, 7)),
                )
            _expect_download_rejection(connection, mutation)
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_download_rejections(root: Path) -> None:
    for mutation in (
        "ack-extra",
        "ack-data",
        "wrong-block",
        "reserved",
        "truncated",
        "data",
        "early-ended",
        "extra-fragment",
    ):
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            thread = threading.Thread(
                target=(
                    serve_invalid_download_phase
                    if mutation in ("early-ended", "extra-fragment")
                    else serve_malformed_download_service
                ),
                args=(listener, mutation, errors),
            )
            thread.start()
            subprocess.run(
                [
                    str(root / ".lake/build/bin/lean-s7"),
                    "integration-download-rejection",
                    "127.0.0.1",
                    str(listener.getsockname()[1]),
                ],
                cwd=root,
                check=True,
                timeout=10,
            )
            thread.join(timeout=3)
        if thread.is_alive():
            raise RuntimeError(f"malformed download peer did not finish: {mutation}")
        if errors:
            raise errors[0]


def serve_interrupted_userdata(
    listener: socket.socket, errors: list[Exception]
) -> None:
    try:
        with _accept_session(listener, 480) as connection:
            request = _receive_s7(connection)
            reference = int.from_bytes(request[4:6], "big")
            _send_s7(
                connection,
                _userdata_response(
                    reference,
                    3,
                    2,
                    bytes([0, 1, 0x10, 2]),
                    sequence=7,
                    has_more_data=True,
                ),
            )
            continuation = _receive_s7(connection)
            if continuation[1] != 7 or continuation[15:18] != bytes([0x43, 2, 7]):
                raise RuntimeError("client sent an invalid USER_DATA continuation")
            # Closing here interrupts the exchange after a valid first fragment.
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_userdata_interruption(root: Path) -> None:
    errors: list[Exception] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        thread = threading.Thread(
            target=serve_interrupted_userdata, args=(listener, errors)
        )
        thread.start()
        subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-userdata-interruption",
                "127.0.0.1",
                str(listener.getsockname()[1]),
            ],
            cwd=root,
            check=True,
            timeout=10,
        )
        thread.join(timeout=3)
    if thread.is_alive():
        raise RuntimeError("interrupted-USER_DATA peer did not finish")
    if errors:
        raise errors[0]


def serve_reference_wrap(listener: socket.socket, errors: list[Exception]) -> None:
    try:
        with _accept_session(listener, 480) as connection:
            for expected_reference, value in ((0xFFFF, 0xAA), (0, 0xBB)):
                request = _receive_s7(connection)
                reference = int.from_bytes(request[4:6], "big")
                if reference != expected_reference:
                    raise RuntimeError(
                        f"expected reference {expected_reference}, got {reference}"
                    )
                _send_s7(
                    connection,
                    _s7_response(
                        reference,
                        bytes([4, 1]),
                        bytes([0xFF, 4, 0, 8, value]),
                    ),
                )
            disconnect = _receive_tpkt(connection)
            if len(disconnect) < 2 or disconnect[1] != 0x80:
                raise RuntimeError("reference-wrap client omitted COTP disconnect")
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_reference_wrap(root: Path) -> None:
    errors: list[Exception] = []
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        listener.listen(1)
        thread = threading.Thread(target=serve_reference_wrap, args=(listener, errors))
        thread.start()
        subprocess.run(
            [
                str(root / ".lake/build/bin/lean-s7"),
                "integration-reference-wrap",
                "127.0.0.1",
                str(listener.getsockname()[1]),
            ],
            cwd=root,
            check=True,
            timeout=10,
        )
        thread.join(timeout=3)
    if thread.is_alive():
        raise RuntimeError("reference-wrap peer did not finish")
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


def send_trickle(
    connection: socket.socket, pieces: list[bytes], interval: float
) -> None:
    for piece in pieces:
        # A rejection may send a disconnect before closing. Stop immediately,
        # so a broken pipe cannot disguise the client's own timeout result.
        readable, _, _ = select.select([connection], [], [], interval)
        if readable:
            connection.recv(1024)
            return
        connection.sendall(piece)


def serve_transport_case(
    listener: socket.socket, mode: str, errors: list[Exception]
) -> None:
    try:
        connection, _ = listener.accept()
        with connection:
            connection.settimeout(3)
            cr = _receive_tpkt(connection)
            _send_tpkt(connection, bytes([0x11, 0xD0, cr[4], cr[5], 0, 1, 0]) + cr[7:])
            setup = _receive_s7(connection)
            reference = int.from_bytes(setup[4:6], "big")
            _send_s7(
                connection,
                _s7_response(reference, bytes([0xF0, 0, 0, 1, 0, 1, 1, 0xE0])),
            )
            request = _receive_s7(connection)
            reference = int.from_bytes(request[4:6], "big")
            if mode == "single-overflow":
                _send_tpkt(connection, bytes([2, 0xF0, 0x80]) + bytes(481))
            elif mode == "cumulative-overflow":
                _send_tpkt(connection, bytes([2, 0xF0, 0]) + bytes(300))
                _send_tpkt(connection, bytes([2, 0xF0, 0]) + bytes(181))
            elif mode == "missing-eot":
                _send_tpkt(connection, bytes([2, 0xF0, 0]) + bytes(20))
            elif mode == "truncated-header":
                connection.sendall(bytes([3, 0]))
                return
            elif mode == "stale-flood":
                response = _s7_response(
                    reference + 1, bytes([4, 1]), bytes([255, 4, 0, 32, 1, 2, 3, 4])
                )
                for _ in range(5):
                    _send_s7(connection, response)
            elif mode in ("exact-budget", "fragmented-tcp"):
                response = _s7_response(
                    reference,
                    bytes([4, 1]),
                    bytes([255, 4, 14, 112]) + bytes([0xAA]) * 462,
                )
                if mode == "exact-budget":
                    _send_s7_segmented(connection, response, 300)
                else:
                    packet = (
                        struct.pack(">BBH", 3, 0, len(response) + 7)
                        + bytes([2, 0xF0, 0x80])
                        + response
                    )
                    send_trickle(
                        connection,
                        [packet[:1], packet[1:3], packet[3:8], packet[8:]],
                        0.01,
                    )
            elif mode in ("drip-header", "drip-body", "drip-segments", "drip-stale"):
                response = _s7_response(
                    reference, bytes([4, 1]), bytes([255, 4, 0, 32, 1, 2, 3, 4])
                )
                cotp = bytes([2, 0xF0, 0x80]) + response
                packet = struct.pack(">BBH", 3, 0, len(cotp) + 4) + cotp
                if mode == "drip-header":
                    pieces = [packet[index : index + 1] for index in range(len(packet))]
                elif mode == "drip-body":
                    connection.sendall(packet[:4])
                    pieces = [
                        packet[index : index + 1] for index in range(4, len(packet))
                    ]
                elif mode == "drip-segments":
                    pieces = [bytes([3, 0, 0, 7, 2, 0xF0, 0])] * 8 + [packet]
                else:
                    stale = bytearray(packet)
                    stale[11:13] = (reference + 1).to_bytes(2, "big")
                    pieces = [bytes(stale)] * 4 + [packet]
                send_trickle(connection, pieces, 0.1)
            else:
                raise ValueError(f"unknown transport case: {mode}")
            # Keep the stream open until the client rejects/disconnects. Missing
            # EOT must hit its receive deadline, not pass due to server-side EOF.
            while connection.recv(1024):
                pass
        if mode == "stale-flood":
            listener.settimeout(0.5)
            try:
                retried, _ = listener.accept()
            except TimeoutError:
                pass
            else:
                retried.close()
                raise RuntimeError("client retried a malformed stale-response exchange")
    except (OSError, RuntimeError, struct.error, ValueError, IndexError) as error:
        errors.append(error)


def run_transport_failures(root: Path) -> None:
    for mode, expected in (
        ("exact-budget", "accept"),
        ("fragmented-tcp", "accept"),
        ("single-overflow", "COTP reassembly exceeds payload limit 480"),
        ("cumulative-overflow", "COTP reassembly exceeds payload limit 480"),
        ("missing-eot", "socket receive timed out"),
        ("truncated-header", "bytes still expected"),
        ("stale-flood", "too many stale S7 responses"),
        ("drip-header", "socket receive timed out"),
        ("drip-body", "socket receive timed out"),
        ("drip-segments", "socket receive timed out"),
        ("drip-stale", "socket receive timed out"),
    ):
        errors: list[Exception] = []
        with socket.socket() as listener:
            listener.settimeout(5)
            listener.bind(("127.0.0.1", 0))
            listener.listen(1)
            thread = threading.Thread(
                target=serve_transport_case, args=(listener, mode, errors)
            )
            thread.start()
            try:
                subprocess.run(
                    [
                        str(root / ".lake/build/bin/lean-s7"),
                        "integration-transport",
                        "127.0.0.1",
                        str(listener.getsockname()[1]),
                        expected,
                    ],
                    cwd=root,
                    check=True,
                    timeout=10,
                )
            finally:
                thread.join(timeout=6)
            if thread.is_alive():
                raise RuntimeError(f"transport peer did not finish: {mode}")
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
        run_handshake_rejections(root)
        sequence_conformance.run()
        run_service_rejections(root)
        run_transfer_deadlines(root)
        run_extended_deadlines(root)
        run_concurrency(root)
        run_compound_operations(root)
        run_stateful_faults(root)
        run_retry_progress(root)
        run_retry_budgets(root)
        run_write_provenance(root)
        run_userdata_completion(root)
        run_transport_resources()
        run_timeout_cleanup(root)
        run_connection_budget(root)
        run_queued_lifecycle(root)
        run_resource_stress(root)
        run_mixed_operations()
        run_boundary_operations(root)
        run_overlap_operations(root)
        run_queued_batches(root)
        run_clock_assurance(root)
        run_operation_conformance()
        run_value_conformance()
        run_conversation_conformance()
        run_multi_batching(root)
        run_multi_semantics(root)
        run_reconnect_shrink(root)
        run_reconnect_recovery(root)
        run_download_integration(root)
        run_download_interruption(root)
        run_download_rejections(root)
        run_userdata_interruption(root)
        run_reference_wrap(root)
        run_segmented_integration(root)
        run_transport_failures(root)
    finally:
        server.stop()
        server.destroy()


if __name__ == "__main__":
    main()
