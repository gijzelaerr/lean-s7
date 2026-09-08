# lean-s7

An exploratory Lean 4 implementation of Siemens S7 communication protocols.

The initial foundation implements safe binary decoding, RFC 1006 TPKT framing,
and the COTP connection and data TPDUs used by classic S7 over ISO-on-TCP. The
project is a way to build practical experience with Lean and formal proofs while
investigating how an executable specification and machine-checked protocol
properties can improve python-snap7 and other S7 implementations.

## Purpose

The primary goal is exploration and shared assurance, not merely another S7
client. The executable Lean client lets us compare an independent implementation
with python-snap7, protocol documentation, packet captures, other clients, and
eventually real controllers. Differences expose ambiguous assumptions and useful
conformance cases.

Today, python-snap7 provides a compatibility reference and an emulator for
end-to-end tests. That is differential testing, not a formal proof that either
implementation is correct. As the Lean model matures, it should also generate a
versioned, language-neutral corpus of valid packets, malformed packets, decoded
values, and expected errors that python-snap7 and other implementations can run
in their own test suites.

Formal work will focus on high-value protocol boundaries: safe and total packet
decoding, encode/decode round trips, exact length fields, negotiated PDU limits,
gap-free chunking, order-preserving multi-item batching, response correlation,
and legal connection-state transitions. Formal claims apply only to properties
that have actually been stated and proved in Lean.

## Status

Early development. Do not connect this software to production equipment.

Implemented:

- bounded immutable packet cursor
- big-endian integer encoding and decoding
- strict TPKT encoding and decoding
- COTP connection-request encoding
- COTP connection-confirmation decoding
- COTP data TPDU encoding and decoding
- S7 job framing and setup-communication request encoding
- IPv4 TCP transport and ISO-on-TCP session negotiation
- classic S7 client connection and PDU-length negotiation
- PDU-aware, chunked `Client.readArea` and `Client.writeArea`
- DB, process-input, process-output, marker, counter, and timer accessors
- big-endian integer, REAL/LREAL, bit, STRING, and WSTRING DB accessors
- multi-variable reads and writes with item-count and PDU-aware batching
- IPv4, IPv6, and hostname endpoints with configurable deadlines and TSAP routing
- serialized requests, stale-response filtering, bounded reconnect, and COTP disconnect
- fragmented SZL reads and the SZL directory
- typed order-code, CPU, communication-processor, protection, and CPU-state queries
- PLC clock get/set using validated S7 `DATE_AND_TIME` values
- CPU hot start, cold start, and stop operations
- classic S7 session-password enter/clear operations
- block counts, block lists, and typed block metadata
- fragmented MC7 and full load-memory block uploads
- PLC-driven fragmented block downloads, insertion, and deletion
- memory compression and RAM-to-ROM copy commands
- force-table reads and input/output process-image bit overrides
- a validated raw S7 PDU exchange escape hatch
- protocol-vector and malformed-input tests
- end-to-end tests against the python-snap7 emulator

Next: prove core codec and chunking properties, define a shared conformance-vector
format, and add real-controller evidence. A native Lean emulator remains useful
where it supports those goals, but is not the primary outcome.

This is a classic S7comm client. S7comm Plus, including optimized symbolic
access on newer controllers, is a different protocol and is not implemented.

The current transport accepts IPv4, IPv6, and DNS hostnames. It supports one
complete COTP data TPDU per S7 response; segmented COTP data is not yet implemented.

## Build and test

Install [Lean through `elan`](https://lean-lang.org/install/), then run:

```console
lake build
lake exe lean-s7-tests
lake exe lean-s7
```

To run the end-to-end suite against python-snap7 3.0.0:

```console
python -m pip install "python-snap7==3.0.0"
python integration/run.py
```

The project pins its Lean toolchain in `lean-toolchain`.

## Client example

```lean
import LeanS7

open LeanS7 Std.Net

def readBytes : IO ByteArray := do
  let some address := IPv4Addr.ofString "192.168.1.10"
    | throw <| IO.userError "invalid PLC address"
  let client ← Client.connect {
    endpoint := .ipv4 address
    rack := 0
    slot := 2
    connectTimeoutMs := some 5000
    operationTimeoutMs := some 5000
    reconnectRetries := 2
  }
  try
    let value ← client.dbRead 1 0 4
    let markers ← client.markersRead 0 16
    let temperature ← client.dbReadReal 1 32
    let label ← client.dbReadString 1 64
    let cpu ← client.getCpuInfo
    let state ← client.getCpuState
    let clock ← client.getPlcDateTime
    client.disconnect
    return value
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error
```

Large transfers are split automatically according to the negotiated PDU size.
For DB, input, output, and marker operations, `start` and `size` are byte based.
For timer and counter operations, `start` is a two-byte-aligned byte offset and
`count` is the number of two-byte elements.

Typed DB methods cover signed and unsigned 8-, 16-, 32-, and 64-bit integers,
32-bit REAL, 64-bit LREAL, individual bits, S7 STRING, and S7 WSTRING. Bit
writes use a read-modify-write operation to preserve neighboring bits; callers
must serialize concurrent writes to the same byte when that distinction matters.

`Client.readMulti` and `Client.writeMulti` preserve caller item order, expose
per-item PLC failures, enforce the classic 20-item limit per telegram, and split
larger calls according to both request and response PDU budgets.

Requests on a client are serialized without occupying worker threads while they
wait. `Client.isConnected` reports lifecycle state, and `Client.disconnect`
sends a COTP disconnect request before shutting down the socket. TSAPs, COTP
references/class/TPDU size, deadlines, stale-response allowance, and bounded
reconnect attempts are configurable through `ClientConfig`.

Management methods include `readSzl`, `readSzlList`, `getOrderCode`,
`getCpuInfo`, `getCpInfo`, `getProtection`, `getCpuState`, `getPlcDateTime`,
`setPlcDateTime`, `plcHotStart`, `plcColdStart`, `plcStop`,
`setSessionPassword`, and `clearSessionPassword`. CPU control and clock-setting
calls change PLC state; applications should apply their own authorization and
safety interlocks before exposing them.

Block methods include `listBlocks`, `listBlocksOfType`, `getBlockInfo`,
`upload`, `fullUpload`, `downloadBlock`, `deleteBlock`, `compress`, and
`copyRamToRom`. `downloadBlock` accepts the complete load-memory image returned
by `fullUpload`; the PLC drives fragment requests as required by classic S7.
`rawExchange` is available for services without a typed wrapper, but callers
must provide the reference encoded in the request and decode the returned PDU.

`readForceTable` reads the CPU force table where SZL `0x0025` is supported.
`forceBit` and `cancelForceBit` only write the input/output process image; they
do not create or remove persistent CPU force-table entries and the scan cycle
may overwrite their values.

## Hardware validation

The deterministic suite covers golden wire vectors, malformed responses, the
python-snap7 emulator, fragmented uploads, and a dedicated PLC-driven download
peer. No real Siemens controller has been validated yet. In particular, block
download/delete, CPU start/stop, clock setting, password sessions, compression,
RAM-to-ROM copy, and process-image overrides must be validated on each target
CPU family and firmware before operational use.

## Design

Pure codecs are kept separate from networking. Parsers return structured errors
instead of indexing packet buffers unsafely. Protocol properties will be added
next to the executable definitions they describe.

The existing [python-snap7](https://github.com/gijzelaerr/python-snap7) test
suite and packet behavior currently serve as compatibility evidence, but not as
the protocol specification. The model must also be grounded in protocol
documentation, independent implementations, packet captures, and real PLC
behavior. Testing Python against a proved Lean model can provide much stronger
assurance, but does not by itself constitute a formal proof of the Python code.
This project does not share the python-snap7 API and does not require Python at
runtime.

## License

MIT
