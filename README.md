# lean-s7

An independent Lean 4 implementation of Siemens S7 communication protocols.

The initial foundation implements safe binary decoding, RFC 1006 TPKT framing,
and the COTP connection and data TPDUs used by classic S7 over ISO-on-TCP. The
long-term goal is an executable protocol implementation whose important framing
and state-machine properties are checked by Lean.

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
- protocol-vector and malformed-input tests
- end-to-end tests against the python-snap7 emulator

Next: block upload/download and the remaining advanced classic S7 services,
followed by a Lean emulator server.

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

## Design

Pure codecs are kept separate from networking. Parsers return structured errors
instead of indexing packet buffers unsafely. Protocol properties will be added
next to the executable definitions they describe.

The existing [python-snap7](https://github.com/gijzelaerr/python-snap7) test
suite and packet behavior serve as a compatibility oracle; this project does
not share its API and does not require Python at runtime.

## License

MIT
