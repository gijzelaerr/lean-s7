# Request encoders against the official native Snap7 client — 2026-10-08

## Why

The `0x11`/`0x12` follow-up method error
([report](userdata-continuation-method-2026-10-08.md)) survived because lean-s7, the
conformance corpus and the Python oracle all encoded the same assumption. Reading the
native Snap7 source found it; this audit makes the same independent check systematic and
repeatable by running the real native client and recording what it sends.

## Method

`python integration/native_client_requests.py --library <native library>` loads the
pinned, digest-verified native Snap7 client (never linked into lean-s7) and points it at a
recording stub peer on localhost. The stub completes the COTP and S7 setup handshake,
records the first request the client sends for each of 60 operations and closes. For SZL
reads and list-blocks-of-type it first answers one fragment that announces more data and
records the follow-up request as well. The normalized bytes (PDU reference zeroed) are the
golden file `integration/native_client_requests.json`; `--check` regenerates them and fails
on any difference (CI runs it with the native build). `LeanS7/NativeRequestTests.lean`
compares the Lean encoders with the same bytes offline.

## Result

59 comparisons are byte-identical, covering DB/input/output/marker/counter/timer reads, DB
reads and writes, multi-item reads and writes, list blocks, list blocks of type, block info,
start upload, delete and request download for all seven block types, read clock, set clock,
SZL reads, CPU stop/hot/cold start, compress, copy RAM to ROM, session password set (3 and
8 characters) and clear, and the follow-up requests for SZL and list-blocks-of-type. The
native follow-ups confirm the fix directly: method `0x12`, a 12-byte parameter block.

Not mirrored, by design (recorded in the test file): the native client reads and writes
words with the WORD transport size and an element count, where lean-s7 always uses BYTE and
a byte count (both are valid encodings of the same request); bit-addressed requests, which
lean-s7 implements as a byte read-modify-write; and the native PLC-status request, which
lean-s7 does not send. No defect was found beyond the follow-up method already fixed.

## Limits

Request bytes only: the stub returns no meaningful data, so decoders are not exercised.
Download fragments and the end/insert exchange are PLC-driven in lean-s7 and are not part of
the native client's flow. The native client is one implementation, not the specification,
and nothing here qualifies a controller.
