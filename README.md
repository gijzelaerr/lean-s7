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
- single-range `Client.dbRead` and `Client.dbWrite`
- protocol-vector and malformed-input tests
- end-to-end tests against the python-snap7 emulator

Next: timeouts, multi-variable operations, additional memory areas, and a Lean emulator server.

The current transport accepts numeric IPv4 addresses and one complete COTP data
TPDU per S7 response. DNS, IPv6, deadlines, and segmented COTP data are not yet
implemented.

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
  let client ← Client.connect { address, rack := 0, slot := 2 }
  try
    let value ← client.dbRead 1 0 4
    client.disconnect
    return value
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error
```

## Design

Pure codecs are kept separate from networking. Parsers return structured errors
instead of indexing packet buffers unsafely. Protocol properties will be added
next to the executable definitions they describe.

The existing [python-snap7](https://github.com/gijzelaerr/python-snap7) test
suite and packet behavior serve as a compatibility oracle; this project does
not share its API and does not require Python at runtime.

## License

MIT
