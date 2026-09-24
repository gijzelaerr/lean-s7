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

`LeanS7.CoreProtocolAssurance` states the formal boundary for the implemented
classic-S7 core in one auditable proposition. `LeanS7.coreProtocolAssurance`
is its proof, composing the framing, codec, correlation, negotiation, memory,
batching, chunking, segmentation, and lifecycle theorems. It deliberately does
not claim S7comm Plus or controller-specific service semantics.

## Status

Experimental: the main classic client surface is implemented, but real-controller
compatibility is unvalidated. Do not connect this software to production equipment.
See the [completion matrix](docs/COMPLETENESS.md) and
[supported profile and release gates](docs/RELEASE.md).

Implemented:

- bounded immutable packet cursor
- big-endian integer encoding and decoding
- strict TPKT encoding and decoding
- strict S7 job encoding and decoding
- composed TPKT/COTP/S7 job packet encoding and decoding
- composed TPKT/COTP/S7 ACK_DATA packet encoding and response decoding
- COTP connection-request encoding
- COTP connection-confirmation decoding
- machine-checked COTP connection-confirmation reference and class validation
- bounded, order-independent COTP TLV parameter decoding with last-duplicate lookup
- machine-checked COTP TPDU-size bounds and confirmation negotiation validation
- live-stack rejection tests for invalid COTP references, transport class, TPDU
  size, and incompatible S7 PDU negotiation
- COTP data TPDU encoding and decoding
- ordered COTP data-TPDU reassembly with machine-checked append/EOT invariants
- S7 job framing and setup-communication request encoding
- machine-checked setup-communication request size and codec round trip
- machine-checked lower bound for accepted negotiated S7 PDU budgets
- IPv4 TCP transport and ISO-on-TCP session negotiation
- classic S7 client connection and PDU-length negotiation
- cross-validated negotiated S7 PDU and COTP TPDU payload budgets
- PDU-aware, chunked `Client.readArea` and `Client.writeArea`
- machine-checked gap-free chunk coverage and per-chunk size bounds used by those transfers
- DB, process-input, process-output, marker, counter, and timer accessors
- machine-checked memory-range count, area, alignment, and 24-bit address invariants
- machine-checked exact single-read and single-write request budget formulas
- big-endian integer, REAL/LREAL, bit, STRING, and WSTRING DB accessors
- machine-checked fixed-width signed and unsigned integer round trips and sizes
- multi-variable reads and writes with item-count and PDU-aware batching
- proof-carrying batch plans used by the client, including ordered partitions,
  item counts, request/response budgets, and write payload-size invariants
- IPv4, IPv6, and hostname endpoints with configurable deadlines and TSAP routing
- serialized requests, stale-response filtering, bounded reconnect, and COTP disconnect
- reconnect rejection when a smaller negotiated PDU would invalidate an
  already-planned request or transfer chunk
- strict COTP disconnect decoding with fixed connection/disconnect request sizes
- a machine-checked lifecycle transition system used by connect, reconnect, transport close, and disconnect
- machine-checked response-reference, PLC-status, and function validation invariants
- machine-checked wire-reference extraction for encoded jobs and ACK_DATA responses
- machine-checked ACK_DATA response length and codec round-trip properties
- machine-checked complete-stack ACK_DATA packet round-trip properties
- machine-checked multi-item batching order, coverage, item-count bounds, and
  negotiated request/response PDU budgets
- fragmented SZL reads and the SZL directory
- machine-checked USER_DATA section sizes and request-reference encoding
- typed order-code, CPU, communication-processor, protection, and CPU-state queries
- PLC clock get/set using validated S7 `DATE_AND_TIME` values
- CPU hot start, cold start, and stop operations
- classic S7 session-password enter/clear operations
- block counts, block lists, and typed block metadata
- fragmented MC7 and full load-memory block uploads
- validated upload lengths and continuation flags, with machine-checked bounded
  assembly, byte order, continuation progress, and completion properties
- PLC-driven fragmented block downloads, insertion, and deletion
- exact machine-checked PLC-driven download-fragment size
- machine-checked PLC-driven download phases, ordered fragment-prefix coverage,
  final-completion guard, and negotiated response-budget bound
- live-stack rejection of malformed SZL and upload fragments, including
  continuation limits and end-upload cleanup
- memory compression and RAM-to-ROM copy commands
- force-table reads and input/output process-image bit overrides
- a validated raw S7 PDU exchange escape hatch
- protocol-vector and malformed-input tests
- machine-checked binary-word, TPKT, COTP data, S7 job, and complete outbound
  packet size/round-trip properties
- end-to-end tests against the python-snap7 emulator

Next: close the finite emulator-only gates in the completion matrix, strengthen
independent interoperability evidence, and validate explicit real-controller
profiles. A native Lean emulator remains useful where it supports those goals,
but is not a completeness requirement.

This is a classic S7comm client. S7comm Plus, including optimized symbolic
access on newer controllers, is a different protocol and is not implemented.

The current transport accepts IPv4, IPv6, and DNS hostnames and reassembles
segmented COTP data TPDUs until the end-of-transmission flag.
Reassembly rejects cumulative payloads beyond the negotiated S7 PDU budget before
appending the offending segment. Before negotiation, the default cap is 65535
bytes. The size-bound theorem is included in the core assurance contract.
Reassembly also limits a TSDU to 4096 segments, even with no receive deadline;
low-level receive methods accept a trailing `maxSegments` override. TPKT version,
minimum length, and the remaining body budget are checked before receiving a
declared body. Empty segments consume the segment budget.
Scripted peers test exact-budget acceptance, single and cumulative overflow,
missing EOT, truncated headers, and stale-response exhaustion. Each receive uses
one monotonic deadline across TCP fragments, TPKT headers/payloads, and COTP
segments; stale responses share the same deadline within an exchange attempt.
Continuous small or empty segments cannot refresh that deadline. This bounds
receiving, not sending or the total duration of multiple reconnect attempts.
Timer budgets must be between 0 and 4,294,967,295 milliseconds; larger values
reject as invalid input rather than wrapping. Generic timeout races use native
cancellable timers, not sleeping worker tasks. Cancellation of DNS/connect tasks
remains cooperative. Resolved endpoints are deduplicated in order, and a protocol
failure during connection negotiation does not trigger address fallback.
`connectTimeoutMs` now shares one absolute budget across DNS, all distinct TCP
candidates, COTP negotiation, and S7 setup. S7 setup also obeys the earlier
`operationTimeoutMs` deadline. Failed setup closes the transport directly rather
than starting a separately timed graceful disconnect. These are cooperative
IO deadlines, not a hard real-time cancellation guarantee.

Uploads, downloads, chunked memory reads/writes, multi-item calls, SZL reads,
and segmented block lists additionally share one absolute
receive deadline for the whole transfer. `ClientConfig.transferReceiveTimeoutMs`
defaults to 30000 ms; `none` disables this whole-transfer budget but retains
`operationTimeoutMs` for each exchange. The earlier deadline applies, and a
continuation, retry, or upload cleanup does not refresh the transfer budget.
Only the initial exchange can automatically reconnect; subsequent chunks and
batches are not retried after a partially completed transfer. Download completion
and insertion acknowledgements remain inside the original receive budget.
These transfer receive deadlines do not cancel socket sends or connection
establishment.

Reconnect retries also depend on operation safety. Typed read-only operations
may retry their initial exchange when `reconnectRetries` is nonzero. Writes,
CPU/clock/security commands, raw exchanges, and upload-session allocation do not
replay by default: a missing acknowledgement does not mean the PLC did nothing.
`allowPotentiallyMutatingRetries := true` explicitly accepts possible duplicate
side effects; it does not provide exactly-once execution or retry later chunks.
Retries belong to an already-active operation. Newly queued requests do not
reconnect a session closed by an earlier terminal failure or explicit disconnect.
After an operation exhausts its retries and leaves the client disconnected,
create a new client with `Client.connect`; a later request cannot restart it.
`Client.pendingOperationCount` reports running and queued gate admissions for
diagnostics; the snapshot is not a synchronization lock.

`writeAreaDetailed` and `writeMultiDetailed` return structured wire-level
progress on success and failure. `acknowledged` retains validated per-chunk/item
results, including item rejection codes; `rejected` records scalar/global PLC
rejections, and `uncertain` identifies outstanding writes whose outcome is
unknown. With explicit replay enabled, `replayedUncertain` retains earlier
unacknowledged attempts even if a later attempt succeeds or rejects. Earlier
acknowledged writes are not rolled back. `attempts` preserves chronological
wire-item outcomes, including replayed attempts. Each location carries the
original multi-item `itemIndex` (scalar writes use `none`) and the byte offset
within that item's payload, so duplicate ranges and chunked items remain
distinguishable. Acknowledgements carry the same provenance. The existing
`writeArea`/`writeMulti` APIs retain their signatures and raise the underlying
error when the detailed call fails.
SZL/USER_DATA assembly checks byte and fragment limits before appending; its
order, bounds, fragment progress, and continuation-room properties are proved.
Single-response USER_DATA services reject replies marked as incomplete rather
than exposing an initial fragment or reporting command success. Clock,
block-count, and password peers cover complete and incomplete replies; segmented
SZL and block-list services retain their separate bounded assembly paths.
Empty metadata fragments remain legal and consume a fragment slot.

The deterministic test suite also mutates valid corpus seeds with byte
substitutions, bit flips, truncations, and trailing bytes. It checks structural
and correlation invariants for accepted mutations rather than assuming every
mutation is malformed. Discovered failures become focused corpus regressions.
Short stateful conversations additionally compare production transfer state
machines to independent phase/size/order oracles. Barrier-synchronized peers
exercise concurrent calls, queued failures, disconnect, and reconnect; other
peers inject faults at every upload and segmented SZL receive phase.

Compound bit read-modify-write calls (`dbWriteBit`, `forceBit`, and
`cancelForceBit`) hold the same client gate across both exchanges. STRING and
WSTRING reads hold it across their header and body, including typed decoding.
Their capacity must remain unchanged between the sizing and body headers;
ordinary updates to current length remain allowed. This does not provide a
consistent snapshot across controller scans or other connections.
Each compound call uses one shared receive budget; only its initial read can
reconnect, never a subsequent body read or write. Invalid string header lengths
reject before the body request. This prevents interleaving on the same client,
but does not make the operation atomic against other connections or PLC scan
cycles, nor does it provide a coherent controller-wide snapshot.

## Build and test

Install [Lean through `elan`](https://lean-lang.org/install/), then run:

```console
lake build lean-s7 lean-s7-tests lean-s7-conformance lean-s7-fuzz
lake exe lean-s7-tests
lake exe lean-s7
```

To run the end-to-end suite against python-snap7 3.0.0:

```console
python -m pip install "python-snap7==3.0.0"
python integration/run.py
```

The integration suite also checks an isolated offline Lake consumer of the public
library. See [package usage and release gates](docs/RELEASE.md) for dependency
pinning, supported profiles and the distinction between emulator and hardware
qualification.

The versioned, language-neutral TPKT corpus is generated by Lean and checked in
at `conformance/v1/tpkt.json`. Verify that it is current with:

```console
lake exe lean-s7-conformance | diff - conformance/v1/tpkt.json
lake exe lean-s7-conformance cotp | diff - conformance/v1/cotp-data.json
lake exe lean-s7-conformance s7 | diff - conformance/v1/s7.json
```

It can also expose framing differences in python-snap7 independently of the
end-to-end emulator tests. The pinned 3.0.0 release currently reports known
divergences and exits nonzero:

```console
python integration/tpkt_conformance.py
python integration/cotp_conformance.py
python integration/s7_conformance.py
```

The S7 corpus covers valid and malformed single-read/write responses, USER_DATA
metadata and payloads, block-upload fragments, two-byte element chunking, and
multi-write payload preservation. It also contains complete clock-read,
block-list, CPU-control, and upload lifecycle request packets. The request
vectors additionally cover fixed clock setting, password entry and
clear, block metadata lookup, and PLC-driven download exchange packets. Typed
block-count response cases reject truncation, trailing data, and unknown types.
Block-list records must be four-byte aligned, and block metadata must be exactly
78 bytes; metadata now rejects trailing bytes as well as truncation.
The generator checks fixed expectations against the Lean codecs and chunk
planner before exporting. The Python runner exercises client and protocol
methods with an in-memory peer and exits nonzero
for divergences. See [the corpus contract](conformance/v1/README.md) for field
meanings and the limits of cross-implementation comparisons.

`S7.decodeAreaRead_size` proves that a successful single-area response decode
returns exactly the requested byte count. The internal read loop retains this
proof in its return type and uses `Chunking.ReadAssembly` to preserve response
order, advance byte offsets without gaps or overlap, and return exactly
`count * elementSize` bytes for the completed plan. These assembly properties
are included in the core assurance contract. They do not prove transport liveness
or that a controller supplied the intended memory contents.

The emulator fixture explicitly models Lean's direct counter/timer byte offsets;
python-snap7 3.0.0's generic parser divides those addresses by eight. The
multi-chunk counter/timer tests therefore validate assembly under that model,
not independent agreement on controller addressing.

Five additional generated address vectors pass offline dissection with Wireshark
4.6.8. Run `python integration/addressing_conformance.py` with `tshark` installed.
This independently checks packet interpretation; physical counter/timer indexing
remains unresolved. See [the addressing evidence](reports/addressing-evidence-2026-09-09.md).

The write loop carries a proof that its remaining plan ends exactly at the
payload boundary and uses bounded slices of the original payload. The
`Chunking.writeSlices_complete` theorem proves that concatenating those slices
in order reproduces the original bytes exactly. This establishes local transfer
coverage and payload preservation, not atomic writes or controller persistence.

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
writes use a read-modify-write operation to preserve neighboring bits. Calls on
the same client are serialized; other connections and controller scans still
require application-level coordination when that distinction matters.

`Client.readMulti` and `Client.writeMulti` preserve caller item order, expose
per-item PLC failures, enforce the classic 20-item limit per telegram, and split
larger calls according to both request and response PDU budgets.
Oversized individual items are chunked while retaining item-level PLC failure
codes. A failed item's remaining chunks are skipped, and later items continue
in order. Before sending writes, the entire logical request is validated,
including payload sizes and final addresses, so locally invalid later items
cannot cause earlier writes. This is not atomic: successful write chunks before
a PLC rejection remain written.
Machine-checked encoder/planner correspondence now bounds actual read/write
request bytes, including odd-payload inter-item padding, by their plan budgets.
Planning also respects each transport's 16-bit length field: byte-transport
payloads beyond 8,191 bytes are chunked even when a larger PDU has space.

Requests on a client are serialized without occupying worker threads while they
wait. `Client.isConnected` reports lifecycle state, and `Client.disconnect`
sends a COTP disconnect request before shutting down the socket. TSAPs, COTP
references/class/TPDU size, deadlines, stale-response allowance, and bounded
reconnect attempts are configurable through `ClientConfig`. The initial
post-handshake PDU reference is configurable for deterministic correlation and
wraparound testing; normal clients retain the default reference 2.
Reconnect retries are limited to timeout, disconnect, and transport failures.
Protocol violations, PLC-declared rejection, lifecycle misuse, and invalid
caller input are never automatically resent.

Both live exchange paths and the portable primitive model use the same pure
`retryBudgetAfter` decision. Checked contracts show that a permitted retry has a
positive allowance, eligible error/safety gates, a nonterminal lifecycle and
exactly one fewer allowance. Every chain of successful decisions preserves
`retry_count + final_allowance = initial_allowance`, bounding retries by the
configured budget. This bounds decisions, not native IO completion time or remote
effects. Forty live repeated-failure conversations exercise allowances 0/1/2/4
for typed reads, raw requests and writes with conservative and explicit opt-in
replay policies; exhausted clients reject fresh operations without resurrection.

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

The portable `conformance/v1/operations.json` corpus adds 29 pure operation cases
for string capacity consistency, single-response USER_DATA completion, replay
policy, and caller/chunk write provenance. A separate standard-library Python
oracle checks them without relying on the emulator. Four reproducibly seeded
16-operation live plans combine success, rejection, reconnect, and terminal
faults; failures report their seed and a bounded failure-preserving reduction.
Typed-value assurance now includes surrounded 32-/64-bit integer proofs, float
bit-interpretation proofs, string allocation bounds, STRING decoder locality,
and universal actual STRING/WSTRING encoder/decoder roundtrips with arbitrary
surrounding bytes. STRING covers supported Latin-1 strings; WSTRING covers all
Unicode scalar strings, including surrogate-pair encoding, within their legal
character/UTF-16-unit capacities. Float claims do not assert NaN equality or
preservation of every NaN payload.

Bit-update assurance proves target readback, preservation of every other valid
bit, idempotence, and last-write behavior for arbitrary byte values and surrounding
data. Invalid Nat bit indices reject before byte decoding. Clock assurance proves
actual encode/decode roundtrips for every validated `PlcDateTime` in 1990–2089,
ten-byte encoding, wrong-size rejection, and independent rejection of non-decimal
packed millisecond digits. Weekday is validated as 1–7, not inferred from the date;
controller timezone and firmware behavior are outside these properties.

The additional `conformance/v1/values.json` corpus adds 207 cases for integer limits and byte
order, Latin-1/Unicode storage boundaries, and clock calendar/BCD failures. Run
`python integration/value_conformance.py` for its independent standard-library
oracle. Eight seeded live boundary conversations add 312 parameterized operations
at PDU sizes 240 and 480, including chunk edges and surrogate pairs split across
DB read/write chunks. Reduction preserves retained operation IDs and parameters.

Eight additional seeded histories check 1,040 overlapping reads, writes and bit
updates against independent mutable DB memory, including read-after-write,
duplicate writes and chunk-edge overwrites. Each ends with a complete 2,048-byte
memory observation. Twenty queued mixed-size multi-item conversations combine
29 caller items with five FIFO-admitted calls at PDU240/480, per-item rejection,
early read retry, partial-read failure and lost first/partial write acknowledgements.
They check caller/chunk write provenance and prevent replay or queued resurrection
after terminal closure. These are bounded regression campaigns, not PLC evidence.

Actual decoder contracts now also prove that accepting arbitrary STRING/WSTRING
input implies valid capacity/current headers and a complete allocated storage
region inside the input. General invalid-capacity/current, truncated-header and
incomplete-allocation rejection properties are checked. WSTRING active-unit
locality covers arbitrary valid or malformed UTF-16 content across unrelated
prefixes, allocated padding and suffixes—not only encoder-produced values.

The portable `conformance/v1/conversations.json` corpus exports 32 seeded
primitive histories with complete unframed request/response PDUs and per-event
lifecycle/write-progress observations. Run
`python integration/conversation_conformance.py` for the independent stdlib
oracle, or `lake exe lean-s7-conformance conversations` to regenerate it. Its
replay decisions combine safety, explicit opt-in, error category, supplied retry
budget and terminal-state gates; it does not model socket IO, scheduler ordering,
budget consumption or remote side effects. Live campaigns supply separate IO
evidence rather than turning this primitive model into a proof of the client.

`conformance/v1/sessions.json` adds 24 seeded active-request histories and
323 events: an active reference, consumed retry allowance, reconnect stages,
response validation and chronological write uncertainty. Its independent oracle
is `python integration/session_conformance.py`; regenerate with
`lake exe lean-s7-conformance sessions`. These are single-wire operational
contracts, not a formal equivalence theorem about the IO client. Seventy-five
live conversations separately exercise failed COTP/setup reconnects, terminal
malformations, exhausted allowances and whole-transfer deadline carryover.

Actual multi-response decoder theorems establish read count, positional payload
sizes and sequential wire order, plus write count and per-position status mapping.
USER_DATA decoding now checks octet transport and permits only the documented
service-specific empty clock-set/password acknowledgements. SZL/block-list
continuations retain a stable data-unit identity while echoing opaque sequence
tokens. See [the evidence and limits](reports/userdata-evidence-2026-09-24.md).

Run `python integration/scalability_bench.py --rounds 3` for verified localhost
fragmented-read and multi-item measurements at 240/480-byte PDUs. Operation
timings exclude connection/warmup/verification but include peer/network costs;
RSS samples are post-operation, not allocation or peak-memory measurements.
The integration suite runs small correctness-only smoke cases without timing
thresholds. No client optimization is inferred from these measurements alone.
See the [recorded baseline and measurement limits](reports/scalability-2026-09-24.md).

Active-request phases are now typed rather than string-valued. Eight actual
pure-transition contracts establish allowance preservation, terminal closed
state and unchanged sends/write progress on failed reconnects; 10,752 transition
controls accompany them. The session artifact's JSON remains unchanged. These
contracts describe the pure model, not a formal equivalence proof of Client IO.

`conformance/v1/management.json` adds 180 management decoder cases and 16 generic
opaque-payload continuation histories. Run
`python integration/management_conformance.py` or regenerate with
`lake exe lean-s7-conformance management`. Tokens include repeated/wrapped zero;
zero and nonzero identities, both ACK dialects and terminal malformations are
covered. Generic continuation fixtures are not typed SZL/block records or an
assertion that all services use identical continuation request methods.

`python integration/session_fuzz.py` compares 256 seeded histories with the
independent oracle using actual Lean session transitions and S7 response codecs.
Build its separate test tool with `lake build lean-s7-fuzz`; JSON fixture/parser
dependencies and pure session-model proofs stay outside the normal client
executable and core-library import path.
An import-boundary regression check enforces that separation.
On divergence it saves a single-deletion-minimized replay artifact without
overwriting prior evidence. Replay with `--replay PATH`; extend with
`--per-seed 256` (1,024 cases across four fixed seeds). A separate
`python integration/generative_reconnect.py` campaign runs 32 seeded live Client
conversations outside the fixed reconnect matrix, with `--seed`/`--case` replay.
Neither layer proves full IO equivalence, cancellation or remote write effects.
See the [recorded fuzz coverage and replay limits](reports/session-fuzz-2026-09-24.md).

Public typed SZL and force-table parsers now validate caller-constructed record
extents as well as transport-decoded inputs. Advanced decoder contracts and
exhaustive boundary tests cover block counts/lists/info and force records without
inventing restrictions on opaque fields. See the
[advanced audit and retained limitations](reports/advanced-decoder-evidence-2026-09-24.md).
Block metadata now exposes the compact subtype separately, validates the returned
number, and uses the native five-digit-number-then-`A` request layout. Independent
wire goldens, live identity peers and local emulator rejection controls capture
the previously shared codec/emulator layout defect. See
[the supported block-info policy and evidence](reports/block-management-2026-09-24.md).

Actual USER_DATA decoder contracts now prove correlation and zero parameter
error, FF/09 success versus exact service-scoped empty/final 0A/00 ACKs,
bounded sequential payload reads and complete data-section consumption. Every
accepted packet has exactly `10 + 12 + 4 + payload.size` bytes. These arbitrary
input implications do not depend on packets produced by the local encoder.

Connection-budget peers test stage sharing, distinct-address fallback, and
protocol failures that must not try another candidate. Twelve queued lifecycle
cases establish actual FIFO gate admissions across active read retry, terminal
closure, disconnect, and recoverable rejection. A measured same-process stress
test samples descriptors, threads, and RSS after warmup on Linux and macOS across
216 attempts and 54 retry reconnects. Its bounded plateau checks are regression
evidence, not a proof of leak freedom. For a longer soak:

```console
python integration/resource_stress.py --rounds 32
```

This runs 6,912 attempts and 1,728 retry reconnects in one client-test process.
The separate `Resource soak` workflow runs weekly on Linux and macOS, with a
manual 32/128-round choice (6,912/27,648 attempts). It is separate from the bounded
per-change regression suite. Hosted-platform results and timings must be checked
after enabling the workflow; local macOS results are not Linux CI evidence.

The deterministic suite covers golden wire vectors, malformed responses, the
python-snap7 emulator, fragmented uploads, and a dedicated PLC-driven download
peer. It also interrupts a PLC-driven download between fragments and verifies
that the client reports a disconnected transport and closes its lifecycle.
No real Siemens controller has been validated yet. In particular, block
download/delete, CPU start/stop, clock setting, password sessions, compression,
RAM-to-ROM copy, and process-image overrides must be validated on each target
CPU family and firmware before operational use.

## Design

Pure codecs are kept separate from networking. Parsers return structured errors
instead of indexing packet buffers unsafely. Protocol properties will be added
next to the executable definitions they describe.

The stateful client preserves its existing `IO` API while raising structured
`IO.Error` constructors at its boundaries: invalid caller input, protocol
violations, PLC-reported rejections, receive/connect timeouts, disconnected
transports, and illegal lifecycle transitions are distinct. `classifyClientError` maps those and native
socket failures to the stable `ClientErrorKind` enum, so applications do not
need to parse rendered error messages. The original diagnostic text and OS code
remain available on the caught `IO.Error`.

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
