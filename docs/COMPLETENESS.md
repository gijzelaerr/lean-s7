# Classic S7 completeness contract

This is the finite acceptance roadmap for the existing classic S7 client and
executable protocol specification. It separates implementation, checked
properties, regression evidence and controller compatibility. It is not a
percentage estimate or a claim that all classic S7 services have been specified.

Baseline: 2026-09-24. Code and evidence on the current branch may be unpublished;
a local passing check is not a passing check of a published release.
Experimental 0.1.0 was published after its exact branch revision passed Linux
and macOS. The repeated tag run exposed a remaining compound-deadline fixture
race. The owner approved a fix-forward 0.1.1 release; see
[the patch validation record](../reports/release-readiness-0.1.1-2026-09-24.md).
Full Linux/macOS CI and [official native endpoint cross-tests](../reports/native-interop-2026-09-24.md)
remain required evidence, not hardware qualification.

## Scope and meaning of completion

The target is the public operations in [Client.lean](../LeanS7/Client.lean), the
pure codecs and state machines they use, and reproducible conformance artifacts.
The supported profiles and limitations must be explicit. The user accepts the
result against this contract before any work item is called complete.

Completion does **not** require python-snap7 API parity, a native Lean server,
S7comm Plus, optimized/symbolic DB access, asynchronous API parity, or every
possible USER_DATA service. Those are separate scope decisions. Python is a test
dependency, not a runtime requirement of the client.

Two separate milestones prevent emulator success from implying PLC success:

- **Local-profile candidate:** the non-hardware gates below pass for the declared
  client profile; unresolved controller/runtime boundaries are documented.
- **Controller-qualified profile:** independent captures or lab tests additionally
  establish the relevant behavior on named CPU families and firmware versions.
  This is never a safety certification or universal controller-compatibility claim.

## Feature and assurance matrix

“Covered” means the named tests exist, not that their finite cases exhaust the
state space. “Checked” refers only to the named theorem scope. Source comparisons,
synthetic dissection and independent test oracles are identified separately from
executing another protocol endpoint. The final column identifies the remaining
acceptance boundary; it does not silently require a theorem for every IO function.

| Feature / implementation | Deterministic and live evidence | Checked proof scope | Independent evidence | Remaining acceptance boundary |
| --- | --- | --- | --- | --- |
| Binary IO and TPKT/COTP/S7 framing: [Binary](../LeanS7/Binary.lean), [TPKT](../LeanS7/TPKT.lean), [COTP](../LeanS7/COTP.lean), [Protocol](../LeanS7/Protocol.lean) | [Lean tests](../Tests.lean), golden packets, truncation/mutation controls, [segmentation/resource peers](../integration/transport_resources.py) | Selected encode/decode round trips, sizes, bounded reassembly, segment order and composed stack properties in [core assurance](../LeanS7/Assurance.lean) | TPKT/COTP/S7 portable corpora and separate Python consumers | Retain exact corpus reproduction and rejection checks. No full socket or arbitrary remote-peer theorem is claimed. |
| TCP connection, TSAPs and negotiation: [Transport](../LeanS7/Transport.lean), `Client.connect` | IPv4/IPv6/DNS paths, malformed handshakes, PDU/TPDU negotiation and [connection-budget peers](../integration/connection_budget.py) | Confirmation correlation, payload budgets and minimum negotiated S7 PDU | Scripted peers independent of the emulator | Release documentation must distinguish logical deadlines from native cancellation; runtime limitation is gate H2. |
| Scalar DB/I/Q/M/C/T memory operations and chunking: [S7](../LeanS7/S7.lean), [Chunking](../LeanS7/Chunking.lean), Client area accessors | Emulator reads/writes, aligned-address and whole-range validation, chunk/PDU boundary tests | Address extent/alignment, encoded sizes, complete non-overlapping chunk plans and PDU bounds | [Native source plus synthetic TShark addressing check](../reports/addressing-evidence-2026-09-09.md) | DB/I/Q/M local profile is exercised. Physical counter/timer indexing remains H1; do not infer it from emulator backing memory. |
| Multi-variable reads/writes and detailed write outcomes: [MultiValidation](../LeanS7/MultiValidation.lean), Client batch planners, [WriteProgress](../LeanS7/WriteProgress.lean) | [Batching](../integration/multi_batching.py), [item semantics](../integration/multi_semantics.py), duplicate/overlap cases, [write provenance](../integration/write_provenance.py) and queued calls | Planner order/count/request/response bounds, actual encoder correspondence, actual response count/order/status contracts and chronological progress primitives | Portable S7/sequence/operation/conversation cases and stdlib consumers | Keep item-level rejection distinct from malformed packets and retain lost-ACK uncertainty. No atomic batch or exactly-once guarantee. |
| Typed DB values: [Value](../LeanS7/Value.lean), 8–64-bit integers, REAL/LREAL, bits, STRING/WSTRING | Exhaustive/boundary Lean controls, [live boundaries](../integration/boundary_operations.py), [overlapping memory oracle](../integration/overlap_operations.py) | Surrounded integer/string round trips, supported Unicode/Latin-1 bounds, arbitrary-input storage/locality contracts, bit preservation; floats interpreted through bits | [207 value cases](../conformance/v1/values.json) and independent stdlib oracle | Preserve capacity consistency between compound reads and document non-atomic reads/read-modify-write. No NaN equality, arbitrary NaN-payload or PLC snapshot claim. |
| Serialization, lifecycle and conservative replay: Client gate, [Lifecycle](../LeanS7/Lifecycle.lean), [RetryPolicy](../LeanS7/RetryPolicy.lean) | [Concurrency](../integration/concurrency.py), [queued lifecycle](../integration/queued_lifecycle.py), fixed and seeded reconnect failures, whole-transfer deadline checks | Legal pure lifecycle transitions; the actual shared retry-budget helper decreases allowance and prevents prohibited replay; selected [pure session contracts](../LeanS7/SessionAssurance.lean); the pure [correlation core](../LeanS7/Correlation.lean), which `Client.exchangeBytesCurrent` and `Client.freshReference` call, proves a reply is delivered only to the awaited reference, stale replies (including pre-wrap references) never complete a later request within one 65 536-reference window, and the stale allowance is spent exactly | Separate portable session oracle; scripted live peers | Gate L2 must identify which live observations match the pure model and which are deliberately outside it. Not extracted or proved: the serialization-gate queue order (promise chain in `Client.serialized`), which remains covered by tests and live peers, and the correspondence between the `scan` model and the socket loop beyond the shared `step` function. No full IO/scheduler equivalence or hard-cancellation claim. |
| USER_DATA envelope and fragmented SZL/block-list assembly: [Management](../LeanS7/Management.lean), [UserDataAssembly](../LeanS7/UserDataAssembly.lean) | [31 service/correlation conversations](../integration/userdata_assurance.py), completion guards, fragment/byte bounds, zero/repeated/wrapped opaque tokens | Actual decoder correlation, supported transport/ACK shapes, sequential bounded payload reads and exact extent; bounded ordered assembly and identity helper contracts | [Native/Wireshark source cross-check](../reports/userdata-evidence-2026-09-24.md), management/sequence corpora and stdlib consumers | Retain the documented service-scoped profile. Generic opaque-payload continuation fixtures are not a model of every service's request method. |
| Typed SZL information: order code, CPU/CP information, protection/state, SZL list | Minimal/truncated/metadata-tampered public structures, emulator and fragmented-peer tests | Actual successful typed parsers enforce public SZL record extent; this is not a proof of every field's semantic interpretation | [Native field-offset comparisons](../reports/advanced-decoder-evidence-2026-09-24.md) | Record supported SZL identifiers/layouts; firmware-specific availability and field meaning remain H1. |
| PLC clocks, CPU start/stop and password sessions | [Clock campaign](../integration/clock_assurance.py), management request vectors, emulator services, positive/negative null-ACK peers | Clock encode/decode for validated 1990–2089 values, ten-byte size and selected malformed BCD rejection; USER_DATA envelope contracts | Values/management corpus oracles; native ACK source comparison | Document date range and weekday policy. Timezone, authorization and CPU state changes require H1; no destructive-service operational claim. |
| Block directory and metadata: [Advanced](../LeanS7/Advanced.lean), list/count/info Client operations | Seven-type permutations, duplicate/unknown type records, opaque fields, every block-info prefix and trailing bytes | Block-code round trips/injectivity, decoder extents/alignment and selected date positions/sizes | [Advanced decoder source audit](../reports/advanced-decoder-evidence-2026-09-24.md), S7/management corpus consumers | Gate L1: preserve outer `blockType`, expose distinct `subBlockType`, correlate the returned number and document typed-client versus low-level number limits. Do not assume all controllers return a matching outer type or invent reserved-field constants. |
| Block upload/download and delete: [Upload](../LeanS7/Upload.lean), [Download](../LeanS7/Download.lean), Client transfer operations | Emulator uploads; PLC-driven scripted download at PDU240/480; early/extra fragment, interrupted transfer, cleanup and deadline controls | Bounded ordered upload accumulation, declared-size completion, download phase/prefix/progress and actual fragment encoding budget | Literal request/response vectors and peers independent of emulator | Preserve MC7/full-upload distinction and conservative mutation replay. Remote installation/deletion and firmware behavior require H1. |
| Compression, RAM-to-ROM copy, force-table reads and process-image overrides | Emulator/control vectors, exhaustive force bit/value tests and public SZL metadata checks | Actual force-table identifier/alignment/extent contracts and bit-update properties; not persistent CPU-force semantics | Native format comparisons and independent wire peers/oracles where represented | `forceBit`/`cancelForceBit` are process-image writes, not persistent force-table operations. Maintenance/scan-cycle behavior requires H1. |
| Validated raw exchange | Reference mismatch, packet validity, conservative retry and terminal-failure tests | Reuses framing/correlation/replay helpers; no semantic theorem for arbitrary raw service payloads | Scripted peer checks | Caller owns service payload interpretation; the escape hatch does not enlarge the supported service profile. |

## Decoder extent and rejection inventory

Every decoder reachable from a public `Client` operation, with the checked theorem
that states what a *successful* decode implies. "Contract" theorems prove
correlation (PDU reference), exact parameter/data extents and no trailing bytes;
none claims anything about field semantics. This inventory is checked by
`lake exe lean-s7-axioms`, which fails if a named theorem disappears or depends on
anything beyond `propext`, `Classical.choice` and `Quot.sound`.

| Decoder | Checked theorem | Module |
| --- | --- | --- |
| TPKT, COTP data/disconnect | `TPKT.decode_encode`, `COTP.decodeData_encodeData`, `COTP.decodeDisconnectRequest_encodeDisconnectRequest` | [Assurance](../LeanS7/Assurance.lean) |
| S7 job/response, PDU reference, area reads, multi-item read/write, USER_DATA | Round trips, `decodeAreaRead`/`decodeAreaReadMany`/`decodeAreaWriteMany` extent and count contracts, USER_DATA correlation | [Assurance](../LeanS7/Assurance.lean), [MultiResponseAssurance](../LeanS7/MultiResponseAssurance.lean), [UserDataDecoderAssurance](../LeanS7/UserDataDecoderAssurance.lean) |
| Setup communication | `decodeSetupCommunication_contract` (reference, 8 parameter bytes, PDU length ≥ 240) | [ResponseDecoderAssurance](../LeanS7/ResponseDecoderAssurance.lean) |
| DB write acknowledgement | `decodeDbWrite_contract` | ResponseDecoderAssurance |
| Block upload start/fragment/end | `decodeStartUpload_contract`, `decodeUploadFragment_contract` (data section = 4-byte header + fragment), `decodeEndUpload_contract` | ResponseDecoderAssurance |
| Download request acknowledgement | `decodeRequestDownloadAck_contract` | ResponseDecoderAssurance |
| CPU control | `decodePlcControl_contract` | ResponseDecoderAssurance |
| SZL envelope and first fragment | `decodeSzl_contract` (identity preserved, data = record length × count), `decodeSzlFirst_extent` | ResponseDecoderAssurance |
| Typed SZL parsers, block counts/entries/info, force table | Extent/alignment contracts | [AdvancedDecoderAssurance](../LeanS7/AdvancedDecoderAssurance.lean) |
| Clock | Round trip, ten-byte size, malformed-BCD rejection | [ClockCodecAssurance](../LeanS7/ClockCodecAssurance.lean) |
| Typed values, STRING/WSTRING, REAL/LREAL | Surrounded round trips; floats at the bit level (`getReal_putReal_surrounded_bits`, `getLReal_putLReal_surrounded_bits`); NaN equality stays out of scope | [ValueCodecAssurance](../LeanS7/ValueCodecAssurance.lean), [ValueDecoderAssurance](../LeanS7/ValueDecoderAssurance.lean) |
| `decodeDbRead` | Delegates to `decodeAreaRead` after correlation; covered through that contract, no separate theorem | [S7](../LeanS7/S7.lean) |
| COTP connection confirm, `decodeParameters` | Tests and corpora only; no extent theorem yet | [COTP](../LeanS7/COTP.lean) |

## Finite local-profile exit gates

The remaining work is a bounded closure checklist. A newly discovered defect may
reopen a gate, but extra seeds or unrelated services do not automatically expand
the milestone. Every gate needs a concrete recorded check and owner acceptance.

| Gate | Required result | Current baseline |
| --- | --- | --- |
| L1 — metadata semantics | Preserve outer `BlockInfo.blockType`; expose offset-11 subtype separately; reject a mismatched returned block number. Typed `Client.getBlockInfo` supports numbers 0–65535 and preflights larger values; low-level five-digit request encoding retains 0–99999. Tests must cover valid, mismatched and boundary values; update portable expectations if their schema changes. Outer/subtype matching is not a universal supported invariant. | Locally validated: [policy, native request-layout fix and evidence](../reports/block-management-2026-09-24.md), three checked contracts, 28 assembled request goldens, exhaustive subtype controls and five live identity/preflight peers. Final combined checks pass; owner acceptance remains required. |
| L2 — model/live coverage | Maintain a mapping from generated pure events to observable live Client outcomes for success, correlated/malformed replies, per-item/global rejection, transport loss, failed COTP/setup reconnect, exhausted allowance, duplicate writes and terminal closure. Exercise missing supported combinations with replayable bounded peers; document model-only events and unsupported equivalence claims. | Locally validated: [selected-rule coverage mapping](../reports/live-coverage-2026-09-24.md) records model/client differences; 16 new seeded mixed histories cover successful stale filtering, rejection reuse, reference wrap and terminal no-resurrection. Fixed 75 and seeded 32 reconnect peers also pass combined checks. Owner acceptance remains required; no full IO equivalence is claimed. |
| L3 — reproducible local validation | Clean-build all four targets; run all Lean tests and the full pinned emulator/peer integration suite; reproduce all eight checked-in corpora exactly; check Python lint/format, workflows and whitespace. Inspect claimed theorem dependencies without admissions or added proof axioms. | Passed on the final integrated changes: 163 clean build jobs, all native/full integration tests, eight exact corpus comparisons, 1,024 pure fuzz histories / 23,730 events, Ruff and actionlint; three new contracts/core have standard axioms only. See [validation record](../reports/classic-progress-2026-09-23.md#completion-closure--2026-09-24-locally-validated). Owner acceptance remains required. |
| L4 — supported-profile and release handoff | Document installation/build/use, public operation groups, structured errors, replay/write uncertainty, supported service/value limits, fixture/proof evidence distinctions and hardware/runtime exclusions. Record the tested toolchain/platform/dependencies; verify an isolated downstream Lake consumer using only public library imports. Verify publication and platform checks separately after authorized publication. | Local handoff validated: [supported profile and release gates](RELEASE.md), README usage and [offline external Lake consumer](../integration/package_smoke.py) pass combined checks. Owner acceptance and authorized publication/exact-revision platform checks remain pending; no release has been published. |

These gates deliberately do not require exhaustive fuzzing, a proof of all IO, a
new server, or changes to python-snap7. Packaging must not pull corpus/JSON/fuzz
tool dependencies into the ordinary client; the
[import-boundary guard](../integration/import_boundaries.py) checks that separation.

## Explicit external and runtime boundaries

| Gate | Evidence needed before changing the claim | Current state |
| --- | --- | --- |
| H1 — controller-qualified service profile | Known adjacent counter/timer captures or a lab controller for index semantics; named CPU/firmware tests for read/write, management layouts and service availability; controlled authorization/CPU-control/clock/block-transfer/delete/maintenance/process-image tests. Record request/response captures and outcomes without assuming remote mutation from ACK absence. | No physical Siemens controller has been validated. Synthetic packets, emulator results, source reviews and independently written test oracles do not satisfy this gate. Captures qualify only the behavior they actually show. |
| H2 — hard native cancellation | A usable cancellable-send/immediate-close runtime primitive, implementation using it, and deterministic stuck-send/cleanup tests. | Logical receive/connect/transfer deadlines are exercised, but native send/close limitations remain. Do not claim bounded native IO termination or universal resource cleanup. This is a runtime dependency, not a reason to add unsafe cancellation workarounds. |

Cross-testing an independently implemented endpoint is valuable additional
interoperability evidence, but does not waive H1. The
[official native-server profile](../reports/native-interop-2026-09-24.md) now passes
locally at PDU240/480 for selected memory, metadata and CPU-state operations;
uncovered services do not inherit that result. Source-only comparisons and
standard-library corpus oracles must not be relabeled as native-client execution
or real-controller captures.

## Evidence and update discipline

- [Corpus schema and limits](../conformance/v1/README.md): TPKT, COTP-data, S7,
  operations, values, primitive conversations, active sessions and management.
- [Progress and local validation record](../reports/classic-progress-2026-09-23.md).
- [Seeded fuzz coverage and replay limits](../reports/session-fuzz-2026-09-24.md).
- [0.1.0 release-readiness record](../reports/release-readiness-2026-09-24.md) and
  [release notes](releases/0.1.0.md). Hosted results are revision-specific.
- [USER_DATA supported profile](../reports/userdata-evidence-2026-09-24.md),
  [advanced decoder audit](../reports/advanced-decoder-evidence-2026-09-24.md) and
  [counter/timer addressing evidence](../reports/addressing-evidence-2026-09-09.md).

Update a gate only with linked implementation/evidence and the exact remaining
limitations. Keep earlier reports as dated evidence rather than rewriting their
historical observations. A merged commit, passing CI, or additional proof is not
alone owner acceptance of the completeness milestone.
