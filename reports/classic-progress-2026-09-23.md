# Classic S7 emulator-only assurance — 2026-09-23

## Scope

Continued classic S7 client assurance without access to a physical PLC. Evidence
comes from Lean proofs and deterministic tests, generated conformance vectors,
the pinned python-snap7 3.0.0 emulator, and focused scripted TCP peers. None of
this substitutes for controller-family and firmware validation.

## Implemented

- Added five live-stack negotiation rejection cases for wrong COTP reference,
  transport class, excessive TPDU size, undersized S7 PDU, and an S7 PDU that
  exceeds the negotiated COTP payload budget.
- Extended the S7 corpus from 8 to 48 response, USER_DATA, upload, request,
  chunk, and write cases, alongside the five separate addressing vectors.
- Added malformed USER_DATA cases for wrong group/subfunction, USER_DATA and
  item errors, truncated declared payloads, and trailing payload bytes.
- Added valid and malformed upload-fragment cases, including the final-fragment
  flag, marker validation, declared length, and service-function validation.
- Added nine complete request vectors for clock read, block listing, CPU
  control, and the upload start/fragment/end lifecycle.
- Added fixed clock-setting, password, block-info, and PLC-driven download
  request/response vectors plus strict block-count response cases.
- Added typed block-list and block-metadata response vectors and fixed the Lean
  block-info decoder to reject trailing bytes after its 78-byte structure.
- Added live adversarial SZL and upload peers. They exercise wrong USER_DATA
  groups, truncated payloads, the 256-fragment limit, invalid upload markers,
  inconsistent lengths, wrong functions, and end-upload cleanup after failure.
- Added a PLC-driven download peer that closes between fragments; the client
  reports a structured disconnected error and leaves the connected state.
- Added the equivalent USER_DATA continuation interruption case for fragmented
  block lists.
- Added `DecodeError.remoteFailure` and `ClientErrorKind.plcRejected`, keeping
  PLC-declared failures distinct from malformed packets without message parsing.
- Added deterministic PDU-reference wraparound coverage: a scripted peer checks
  correlated requests at references 65535 and 0.
- Restricted reconnect retries to timeout, disconnect, and transport failures;
  malformed responses, PLC rejections, lifecycle errors, and invalid input are
  never automatically resent. Scripted peers verify that neither a PLC rejection
  nor a stale-response protocol failure opens a second TCP session with retries enabled.
- Replaced the old stale-response reconnect fixture with a two-session transport
  drop/recovery peer that verifies the original request is retried byte-for-byte.
- Split request/value encoding failures into the `invalidInput` category and
  reject raw exchanges whose supplied reference differs from the encoded PDU.
- Added pinned Python lint and formatting checks to CI.
- Reject reconnects that negotiate a smaller S7 PDU than the session whose
  already-planned request is being retried.
- Extended `CoreProtocolAssurance` with explicit TPKT round trips, USER_DATA
  size/reference properties, response-function validation, download-fragment
  size, and transport-closure safety.
- Proved the exact encoded size of PLC-driven download-fragment responses.

## Differential result

python-snap7 3.0.0 passes 10 of the 48 S7 corpus cases. The 38 divergences include
the previously recorded read/write/chunking issues plus acceptance of malformed
USER_DATA metadata and payload lengths, acceptance of malformed upload markers
and lengths, omission of a valid two-byte final upload payload, and fifteen
request/response differences or unsupported operations across block listing,
CPU control, clock setting, block metadata, password handling, and the
upload/download lifecycle.
These are cross-implementation observations, not formal claims about the Python source.

## Validation

- Clean build of `lean-s7`, `lean-s7-tests`, and `lean-s7-conformance`.
- All deterministic Lean tests passed.
- TPKT, COTP, and S7 generated corpora match the checked-in artifacts.
- Full python-snap7 3.0.0 emulator integration suite passed.
- Python lint, formatting, and whitespace checks passed.

## Blocked boundaries

- Socket sends remain unbounded: the current Lean async TCP API exposes receive
  cancellation but no cancellable send or immediate socket-close primitive;
  deterministic send-cancellation coverage depends on such a primitive.
- Physical counter/timer indexing and all real-controller service semantics
  remain unresolved without hardware or captures.

## Download-service validation follow-up

- The Lean client now requires the exact PLC-driven download service parameters:
  function, seven reserved bytes, and the addressed block type and number. It
  rejects an unexpected data section for both fragment and completion jobs.
- Request-download acknowledgements must contain exactly the one-byte service
  function and no data before the client sends any fragment.
- The scripted peer now uses full service requests and checks malformed
  acknowledgements, wrong block numbers, nonzero reserved bytes, truncated
  parameters, and unexpected data. These are emulator-independent rejection
  checks, not evidence of behavior on a physical controller.

## Download phase assurance follow-up

- Added a pure download state machine used by the client for acknowledgement,
  fragment, and completion transitions. Fragment plans contain proof witnesses
  for progress and the negotiated PDU slice bound.
- Proved that each accepted fragment extends exactly the previously sent prefix,
  that no fragment or completion occurs before acknowledgement, that incomplete
  transfers cannot complete, and that encoded responses fit their PDU budget.
  These properties are part of `CoreProtocolAssurance`.
- Scripted peers reject an early download-ended request and an extra fragment
  request after the complete block has been sent. The resulting client error is
  a protocol failure and the transport is closed.
- The successful scripted transfer now runs at both 240- and 480-byte
  negotiated S7 PDU sizes and checks every fragment response against that limit.

## Upload assembly assurance follow-up

- Added a pure upload state machine used by the client. Its bounded accumulator
  checks the cumulative size before appending a fragment. Proofs of byte order,
  cumulative bounds, continuation progress, and exact declared size at completion
  are included in `CoreProtocolAssurance`.
- Enforced the PLC's declared upload length, rejected continuation flags other
  than 0 or 1, and rejected empty continuation fragments. No block data is returned
  until a valid END_UPLOAD acknowledgement. Rejected uploads attempt cleanup
  with the validated upload ID, then close the transport.
- Start-upload replies accept the canonical 16-byte parameters and the explicit
  legacy eight-byte form without a declared length; other sizes, unexpected data,
  and invalid ASCII length digits are rejected. The decimal decoder uses the
  bounded cursor rather than panicking indexing.
- Added two invalid-flag corpus vectors, bringing the S7 corpus to 50 cases.
  Added scripted peers for invalid flags, no progress, early termination,
  declared-length overflow across fragments, continuation at the declared end,
  and malformed END_UPLOAD acknowledgements on success and cleanup paths.
- Validation passed: clean build, all Lean tests, generated corpus comparisons,
  full pinned python-snap7 3.0.0 integration suite, and Python lint/format checks.

## Parallel transfer and batching assurance follow-up

- Added a pure SZL/USER_DATA accumulator with pre-append byte and fragment
  checks, ordered assembly, count progress, completion tracking, and proofs
  that continuing replies leave an available fragment slot. Empty metadata
  fragments remain valid. The client closes failed transfers, including final
  record/entry decoding failures.
- Added a configurable absolute upload/SZL/segmented USER_DATA receive deadline
  (30 seconds by default), shared across continuations, retries, and cleanup.
  Per-exchange limits remain active; disabling the transfer budget does not
  disable those limits. Sends and connection establishment remain outside the
  cancellation guarantee.
- Actual multi-item client loops now use proof-carrying planner certificates
  for ordered partitioning, item count, and both PDU budgets. Added positive
  read-count and exact write-payload properties to the core assurance contract.
  Executable tests check actual encoder accounting and mixed return-code order;
  these tests are not an encoder-correspondence theorem.
- Added deterministic mutation testing over valid corpus seeds. The initial
  2,636 checks found acceptance of USER_DATA continuation flag 2; values other
  than 0 and 1 are now rejected, with two focused corpus regressions (52 S7
  cases). The supported flag values are independently corroborated by the
  [Wireshark S7 dissector's `userdata_lastdataunit_names` definitions](https://github.com/wireshark/wireshark/blob/master/epan/dissectors/packet-s7comm.c).
- Independent peer checks passed: 19 deadline scenarios across all three
  transfer kinds, and four 41-item read/write batching scenarios at 240/480-byte
  PDU sizes with one- and 37-byte payloads and interleaved PLC failures.
- Combined validation passed: clean build, all Lean tests, all three generated
  corpus comparisons, Ruff lint/format, whitespace checks, and the full pinned
  python-snap7 3.0.0 emulator/scripted-peer suite. No real-controller
  compatibility claim is made.

## Extended assurance workstreams

- Implemented logical-range and whole-request write validation before any
  multi-item IO, without imposing the wire packet's 16-bit count limit on
  chunkable logical transfers. Late invalid payloads, areas/DB numbers, and
  final addresses are covered by no-write peers.
- Oversized multi-item transfers now use singleton multi-item decoders for each
  chunk, returning the original PLC item failure code, skipping the failed
  item's remaining chunks, and preserving later item/result order. Successful
  write chunks preceding a PLC rejection remain written; this is not atomic.
- Extended absolute receive budgets to scalar chunked reads/writes, multi-item
  calls, and PLC-driven downloads including final insertion acknowledgement.
  Automatic reconnect retries are restricted to the initial exchange, avoiding
  restarted partially completed transfers.
- Added checked encoder/planner correspondence: actual read requests have
  exactly the planned parameter size; actual write requests fit the conservative
  planned size including inter-item padding. Both planned request-size theorems
  are included in `CoreProtocolAssurance`.
- Added 5,960 expanded mutation/sequence checks, including every bit position,
  mixed multi-item replies, block counts/metadata/lists, clocks, STRING/WSTRING,
  and continuation sequences. These found silent overwriting of duplicate
  block-count types; ambiguous duplicates now reject, with two new corpus cases
  (54 S7 cases).
- Combined validation passed: clean build, all Lean tests, all three corpus
  comparisons, Ruff lint/format, whitespace checks, the full pinned emulator
  suite, and the expanded successful-oversized-transfer peer checks. Sends and
  connection establishment remain outside cancellation guarantees; no
  physical-controller claim is made.
- The final wire-length audit also caught large-PDU planning that could exceed
  the 16-bit bit-length field despite fitting the PDU budget. Byte-transport
  reads/writes now chunk beyond 8,191 payload bytes; octet transport uses its
  byte-length bound. Planner certificates prove representable selected lengths,
  with exact-boundary and fallback tests included.
- Independent new peer checks passed: 18 oversized-item success/failure/prevalidation
  scenarios at PDU sizes 240/480 and 34 extended deadline/prevalidation scenarios,
  including spent-budget reconnect and continuation-no-retry checks.

## Operation safety and conversation assurance

- Five follow-up items are being implemented in parallel: operation-aware
  retries, concurrency/lifecycle peers, structured write progress, stateful
  fault conversations, and broader value-codec proofs/conformance scenarios.
- Retry and write-progress changes share an owner because they affect the
  same client failure paths. Mutation/control/raw operations will not replay
  automatically without explicit opt-in; session-allocating upload start is
  treated conservatively too.
- New exhaustive short conversations compare the production upload, download,
  and USER_DATA state machines to independent arithmetic/phase oracles at each
  accepted prefix. Independent peers inject disconnects and wrong services at
  each upload and segmented SZL receive phase.
- New concurrency peers use process barriers rather than timing guesses. After
  correcting a Python peer framing assumption, the queued-failure test exposed
  a real client defect: service-specific read decoding could fail after the
  cleanup boundary without closing the session. The fix retains the gate
  through typed read, USER_DATA, control-service, and SZL projection validation.
- Codec work adds actual surrounded WORD/INT round-trip theorems and narrowly
  stated floating-point bit interpretation theorems, plus mixed multi-item and
  continuation corpus conversations. Focused tests passed for 31,310 stateful
  conversations, all 65,536 WORD/INT values, 20 upload/SZL wire faults, and 12
  independently decoded corpus conversations. Final combined checks remain pending.
- The combined clean build passed all 82 jobs; the complete Lean test suite,
  generated TPKT/COTP/S7 corpus comparisons, Python lint/format, and whitespace
  checks passed. The full pinned emulator suite is now running with all new
  peers wired in. No commit or push has been made for this follow-up.
- Independent review found a write-progress edge case under explicit replay
  opt-in: a validated rejection of the replay must not erase uncertainty about
  an earlier attempt whose acknowledgement was lost. Earlier-attempt uncertainty
  is being retained separately, with replay-then-rejection regression peers.
- Concurrency failure assertions now distinguish the initiating protocol error
  from disconnected queued calls. Task-creation barriers do not prove every
  competitor has already entered the queue; disconnect and reconnect are
  exercised separately, not as a combined disconnect-during-reconnect scenario.
- Final source refinements preserve earlier write attempts in
  `replayedUncertain`, mark current uncertainty only when sending starts, and
  avoid inventing a write attempt when reconnect fails. Three extra regression
  peers cover scalar/multi replay rejection and rejected reconnect diagnostics;
  successful replay assertions are strengthened (15 retry/progress scenarios total).
- Compact-header/MC7 decoding now stays inside the upload gate as well, with
  a successful raw-transfer/invalid-compact-block regression (21 phase-fault
  scenarios total). These final refinements await the final clean validation.
- Final clean validation passed all 82 build jobs, all Lean tests, all three
  generated corpus comparisons, lint/format, and whitespace checks. Independent
  focused runs against this exact build passed all 15 retry/progress scenarios
  and all four concurrency modes with strict initiating/queued error categories.
  The focused 21-phase fault run also passed, including compact-upload closure.
  The full final emulator suite remains underway.
- Final complete pinned python-snap7 3.0.0 emulator/scripted-peer suite passed
  against the final clean build, including all 15 retry/progress scenarios,
  four concurrency modes, 21 phase faults, and all existing integration checks.
  The complete local validation is green. No follow-up commit or push has
  been made. Progress is wire-range/ordered-result based, not indexed by caller
  item identity; replay uncertainty does not imply rollback or exactly-once IO.
  Sends/connects remain outside cancellation guarantees, and no physical PLC
  compatibility or safety certification is claimed.

## Compound-operation serialization follow-up

- Operation safety/conversation assurance was committed as `8d2fd50`, pushed,
  and merged via PR #15 at the owner's request. Follow-up branch
  `feat/compound-operation-gates` starts from merged main `b074043`.
- DB bit updates and input/output process-image overrides now retain the
  serialization gate across read-modify-write, with one receive budget and
  no replay after the initial read. This excludes same-client calls only;
  controller scans and other connections remain outside that guarantee.
- STRING/WSTRING reads retain the gate through initial header checks, all body
  chunks, and typed decoding. Used lengths exceeding capacity reject before
  body IO. Their two stages share one absolute receive deadline.
- The first eleven independent compound peers passed. Coverage is expanded to
  fourteen scenarios including concurrent bit clears, cancellation of process
  image bits, and a receive deadline spanning the bit read and write. Full
  combined validation is pending; follow-up changes remain uncommitted.
- All fourteen compound peers passed. Final clean build passed all 84 jobs;
  Lean tests, all three generated corpus comparisons, lint/format, and whitespace
  checks passed. The complete pinned emulator suite is running. PR #15's branch
  CI passed; the additional pull-request CI run was still active when inspected.
- Focused concurrency and all fourteen compound peers also passed with
  `LEAN_NUM_THREADS=2` configured. This sets the initial worker pool, not a hard
  cap on native threads: the [pinned Lean runtime](https://raw.githubusercontent.com/leanprover/lean4/v4.33.1/src/runtime/object.cpp)
  can expand workers when a task blocks waiting for another task.
- The complete pinned python-snap7 3.0.0 emulator/scripted-peer suite passed,
  including all fourteen compound scenarios and every existing integration
  check. Combined validation is green. Follow-up changes are on
  `feat/compound-operation-gates`, uncommitted and unpushed.
- Final PR #15 inspection confirmed merged status and success for both CI runs.

## Caller-indexed write diagnostics

- Owner authorized local commits and continued work. Compound-operation fixes
  were committed as `469646d`; the branch remains unpushed.
- Detailed writes now preserve chronological per-wire-item attempts, original
  caller indices, and chunk byte offsets, including duplicate logical ranges.
  Existing summary fields and ordinary write API signatures remain available.
- A reverse-list accumulator avoids repeatedly scanning completed history;
  public diagnostic arrays are materialized once and internal state is cleared.
  Pure proofs cover history preservation, replay location order, acknowledged
  result order, and exact acknowledgement count. These are model properties,
  not an exactly-once or rollback guarantee for PLC writes.
- Unit tests passed, including a 10,000-item trace. Six independent provenance
  peers and all fifteen existing retry/progress peers passed. Complete clean
  validation is pending before the next local commit. No push is authorized.
- Final clean validation passed all 86 build jobs, the complete Lean test suite,
  all three generated corpus comparisons, Python lint/format (16 files), and
  whitespace checks. The complete pinned python-snap7 3.0.0 emulator/scripted-
  peer suite passed, including all six new provenance scenarios and every
  existing integration check. The provenance batch is ready for a local commit;
  no push or physical-PLC validation has been performed.

## String capacity consistency follow-up

- Owner requested push and continued work. Both local commits (`469646d` and
  `a2aa44d`) were inspected for author, committer, message, and attribution, then
  pushed to `origin/feat/compound-operation-gates`. No PR was created or merged.
- Audit found that a smaller capacity in the body header can silently pass
  STRING/WSTRING decoding after the initial sizing read. New peers exercise
  shrinking/growing capacity and valid current-length changes separately;
  implementation and complete validation are underway.
- Independent shrinking-capacity peers reproduced silent acceptance in both
  pre-fix APIs. The fix checks the body capacity against the sizing header and
  reports a protocol failure, closing the session without replay. Current-length
  updates remain permitted; this is not snapshot isolation from controller IO.
- All six new focused peers passed, covering capacity growth/shrinkage and valid
  current-length updates for both string types. Clean combined validation is
  underway; follow-up changes remain uncommitted.
- Final clean build (86 jobs), complete Lean tests, all three generated corpus
  comparisons, Python lint/format, whitespace checks, and the complete pinned
  emulator/scripted-peer suite passed. Compound coverage now totals 20 scenarios.
  CI for the initially pushed head `a2aa44d` completed successfully. The capacity
  fix is ready to commit and push on the same branch; no physical PLC or PR merge
  is involved. Current-length changes do not establish a consistent PLC snapshot.

## Single-response USER_DATA completion follow-up

- The capacity fix was committed and pushed as `2a4010a`; the branch was clean
  at the next owner request to push and continue. No additional PR/merge occurred.
- Audit found that fixed single-response USER_DATA helpers ignore the continuation
  flag. Complete-looking initial clock/block-count payloads and command replies
  can therefore report success despite an incomplete response. Independent peers
  are being added for five services, with positive complete-response controls.
- Independent peers reproduced silent incomplete-response acceptance in all five
  services before the fix. Shared single-response completion validation now
  executes inside the operation gate, before typed payload decoding or command
  success. A pure theorem states that accepted payloads require completion and
  preserve bytes; this does not prove socket IO or exactly-once command execution.
- All ten focused peers and the complete Lean tests passed. Complete replies
  keep the connection usable; incomplete replies fail as protocol errors, close
  the connection, prevent a later scalar write, and do not reconnect/replay even
  with explicit mutation replay enabled. Final clean combined validation follows.
- Final clean build passed all 88 jobs; complete Lean tests, all three corpus
  comparisons, and Python lint/format (17 files) passed. The full suite passed
  all ten completion peers, twenty compound peers, existing retry/provenance
  peers, and segmented-service deadline checks; final transport checks remain
  running. CI for earlier head `2a4010a` completed successfully.
- The complete pinned python-snap7 3.0.0 emulator/scripted-peer suite passed
  against the final clean build, including all existing transport checks. Combined
  local validation is green; the single-response completion fix is ready for a
  commit and push on the same branch. No PR merge or physical-PLC claim is made.

## Five-workstream parallel hardening

- Owner requested all five suggested workstreams in parallel. Three delegated
  workers plus root advanced resource limits, portable regressions, generated
  conversations, typed-value proofs, and timeout/cleanup auditing on the same
  branch. No worktree or separate PR/branch was created.
- COTP now has a finite segment budget (default 4096), including empty segments
  with deadlines disabled. TPKT version/minimum length/body size rejects before
  waiting for the declared body. Pure proofs cover payload bytes and segment
  count; all nine independent resource peers passed.
- `operations.json` exports 29 validated operation cases with an independent
  standard-library-only Python oracle. Four seeded 16-operation live plans and
  bounded exact-failure-preserving reduction passed, including retry/reconnect,
  multi-item mixed results, malformed replies, and dropped write acknowledgements.
- Wider integer and float bit-interpretation surrounded-buffer proofs, string
  allocation/capacity bounds, STRING decoder locality, and empty string encoder
  roundtrips are checked. Extended value tests passed; nonempty Unicode encoder
  roundtrips are tested rather than universally proved.
- Timeout races now use native cancellable timers; budgets over 4,294,967,295 ms
  reject explicitly before DNS/client IO instead of silently wrapping. Resolver
  duplicate endpoints were reproduced and deduplicated; connection protocol
  failures no longer fall through to another candidate. Twenty-eight cleanup
  attempts passed with maximum timers and stalled/malformed confirmations.
- An initial cleanup harness failure also required accepting TCP RST as valid
  closure after unread malformed bytes. Cancellation remains cooperative and
  does not establish process-wide leak freedom or a total connection deadline.
  Combined clean validation is pending; all changes are uncommitted and unpushed.
- Combined clean build passed all 98 jobs, complete Lean tests, four generated
  corpus comparisons, independent operation oracle, Python lint/format (21 files),
  and whitespace checks. Read-only review found no implementation blocker; mixed
  peer cleanup was hardened to close failed handshakes and accept legal terminal
  RST. Final full pinned integration is starting against frozen source.
- Final full pinned python-snap7 3.0.0 emulator/scripted-peer suite passed,
  including nine resource peers, twenty-eight cleanup attempts, four seeded
  mixed-operation plans, the 29-case independent operations oracle, and all
  existing integration tests. All five requested workstreams are implemented
  and combined local validation is green. One coherent local commit follows
  under earlier commit approval; this new batch has not been pushed.

## Connection-lifetime and nonempty string follow-up

- Owner approved the next plan including publication and five parallel streams.
  Commit `4e812ec` was inspected and pushed; PR #16 is open on the combined branch.
  It has not been merged. No branch rewriting or worktrees were used.
- Workstreams cover a shared total connection budget, measured process-resource
  plateau under failure/reconnect stress, distinct-address fallback behavior,
  genuinely queued lifecycle races, and actual nonempty string roundtrip proofs.
- Total connection budget source spans DNS/candidates/COTP/S7 setup, with existing
  operation receive limits retained. A read-only running-plus-queued operation
  count supports explicit admission barriers without private-field reflection.
- Independent peer modules and Linux/Darwin FD/thread/RSS sampling are in progress.
  Nonempty Latin-1 STRING roundtrip is checked; WSTRING proofs remain underway.
  No new commit/push is made yet; focused and combined validation are pending.
- Checked universal actual STRING roundtrips for every supported Latin-1 string
  and WSTRING roundtrips for every Unicode scalar string, including supplementary
  characters, within legal capacities and arbitrary surrounding buffers. Both
  are part of `CoreProtocolAssurance`; exhaustive Latin-1/BMP and 4,096 astral
  boundary regressions pass. No axioms, admissions, or placeholder proofs added.
- Twelve genuinely admitted queued lifecycle cases exposed and fixed fresh
  queued requests reconnecting an already-poisoned session. Both exchange paths
  now reject fresh disconnected operations outside the retry catch, while an
  active read can still reconnect within its own retry. All twelve focused cases
  and the four prior concurrency cases pass.
- Darwin measured baseline/peak for the 216-attempt stress: FD8/8, threads7/7,
  RSS5,586,944/5,636,096 bytes. Optional `--rounds 32` same-process soak passed
  6,912 attempts/1,728 retry reconnects: FD8/8, threads7/7,
  RSS5,685,248/5,701,632 bytes. Synthetic checker tests detect each metric's
  excess growth and missing measurements. These are bounded regression evidence,
  not leak-freedom or real-time cancellation proofs; Linux remains a CI platform
  check. Unit tests and lint/format (24 files) pass; final clean validation pending.
- The initial apparent refused-endpoint stall was a fixture error: bound but
  non-listening sockets on Darwin silently dropped SYNs. The distinct-refusal
  fixture now closes an ephemeral endpoint before testing; no unsupported native
  runtime defect is claimed. Failed S7 setup intentionally closes directly, so
  the previous replay-reconnect-reject peer is updated to require EOF/reset with
  no continued traffic rather than a separately budgeted graceful disconnect.
- Nine portable native connection/fallback peers and fifteen prior retry peers
  passed. An additional Darwin pending-TCP probe returned and exited under its
  250 ms budget; portable immediate-refusal platforms omit only that probe.
  Connection stages now race native Async tasks directly, with best-effort task
  cancellation; underlying OS cancellation remains unproved. Final cleanup review
  corrected an exception-rollback-sensitive mutable flag to an IO.Ref so an
  established socket is actually shut down after handshake failure.
- First combined clean build overlapped a final focused Transport rebuild and
  lost the generated Transport.olean during Client compilation. This is a build
  coordination failure, not accepted validation. Source is now frozen and all
  further clean/native builds are root-owned; complete clean validation restarts.
- Restarted clean build passed all 106 jobs with frozen source. Complete Lean
  tests and all four exact generated corpus comparisons pass; Ruff lint/format
  (24 files) and whitespace checks pass. The final full pinned emulator suite and
  repeated 6,912-attempt measured soak are running; no new commit/push yet.
- Final complete pinned python-snap7 3.0.0 emulator/scripted-peer suite passed,
  including the nine connection-budget cases, pending-TCP process-exit probe,
  twelve queued lifecycle cases, all prior retry/provenance/transfer tests, and
  the independent 29-case operations oracle. Final frozen-build 216-attempt
  plateau: FD8/8, threads7/7, RSS5,603,328/5,668,864 bytes. Repeated long soak
  passed 6,912 attempts/1,728 retry reconnects (8,640 physical TCP connections):
  FD8/8, threads7/7, RSS5,603,328/5,619,712 bytes. All five follow-up workstreams
  are implemented and locally validated. Publication stays on the same branch
  and PR #16 under owner approval; it has not been merged. Native OS cancellation,
  ordinary-send bounds, universal leak freedom, and physical PLC validation
  remain outside the proven/tested guarantees.

## PR #16 merge and next non-blocking work

- Owner requested merging #16. Both Linux CI runs passed. Local `main` was
  fast-forwarded to the exact validated `082ec79` and pushed after inspecting
  all six outgoing commits' authors, committers, messages, and empty trailers.
  No new merge commit, history rewriting, or branch deletion was needed.
  GitHub confirms #16 MERGED at 2026-09-23T18:31:50Z; local/origin main match.
- Read-only review confirmed a new clock-decoder bug, not yet fixed:
  `S7.decodePlcDateTime (bytes #[0,0x19,0x26,0x09,0x23,0x12,0x34,0x56,0x12,0xa3])`
  returns a valid-looking date/time with millisecond=130 despite non-decimal BCD
  digit A in the final byte's high nibble. A native Lean evaluation reproduced it.
- Recommended emulator-only follow-ups: fix clock BCD validation and prove valid
  DATE_AND_TIME roundtrips; prove bit-update isolation/idempotence/readback;
  export wide values, Unicode and clock boundaries as portable conformance cases;
  broaden existing mixed-fault generators beyond operation order to PDU/payload/
  capacity boundaries; add dedicated longer Linux/macOS soak CI coverage.
  These are recommendations, not newly authorized implementation or automation.

## Clock, bit, and generated boundary assurance

- Owner approved all five follow-ups in parallel. Work is on one new branch,
  `feat/classic-value-boundary-assurance`, starting at merged #16 (`082ec79`).
  The preceding progress-log update is preserved. Separate workers own clock
  codec/fix proofs, bit-update proofs, and generated boundary conversations;
  root owns portable value corpus, shared wiring, docs, and soak CI.
- New weekly/manual soak workflow targets Linux and macOS independently with
  32 rounds by default and an optional 128-round manual choice. It uses the
  existing process-metric checker; no automation is enabled until publication
  and merge. Source/corpus/proof work and combined local checks remain underway.
- Clock's packed final millisecond digit now rejects A–F independently of other
  fields. Actual universal validated-value roundtrip, ten-byte encoding, wrong
  length rejection, and independent invalid-digit proofs are checked. Tests span
  all 36,525 supported dates, 7,000 millisecond/weekday combinations, calendar
  decoder negatives, and full-stack read-only clock-query controls/rejections.
- Bit-update actual-API properties quantify arbitrary UInt8 values, Nat indices,
  Boolean updates and surrounding data. Readback, unrelated-bit preservation,
  idempotence, overwrite and invalid-index rejection are in CoreProtocolAssurance.
  Axiom audit contains only standard propext/Classical.choice/Quot.sound; a
  provisional reflection-based approach was replaced by kernel-checked algebra.
- Eight reproducibly seeded native boundary plans passed 312 parameterized
  operations at PDU240/480. Fifteen synthetic closure checks reject partial or
  unauthorized traffic. Parameter-aware reduction preserves operation IDs,
  addresses, lengths and values; generator independently checks mandatory edges.
- Portable integer/Unicode/clock value corpus and stdlib Python oracle are
  implemented. Initial 190 cases passed, then review added decoder-only calendar
  failures, exact integer schema versions, compact representation negatives and
  byte/value mutations. Soak workflows parse and actionlint1.7.7 passes locally.
  Source is frozen pending root integration/wiring checks and full clean validation;
  all current follow-up changes are uncommitted and unpublished.
- Root focused checks pass: all eight boundary plans/312 operations; 16 full-stack
  clock queries (10 decimal controls, six A–F rejections with terminal cleanup);
  final portable corpus 207/207 independent cases (34 integer, 30 string,
  143 clock). Schema tests reject Boolean/float versions; compact-byte tests
  detect malformed shape/ranges/aggregate sizes, and byte/value/status mutations.
- Root independently audited clock roundtrip and four main bit-update theorems:
  only standard propext/Classical.choice/Quot.sound axioms. Original 0xA3 clock
  reproducer now returns `invalidField 9 "invalid BCD millisecond digit"`.
  No admissions, native certificate axioms, or new user axioms are present.
  All source is frozen; one root-owned clean combined validation starts next.
- Clean combined build passed all 118 jobs. Complete native Lean tests pass,
  including clock-calendar/bit regression suites and the new corpus validator.
  All five generated corpus comparisons are exact; independent values oracle
  passes 207/207 cases. Ruff lint/format (27 files), whitespace checks, and both
  workflow files' pinned actionlint check pass. Final full emulator integration
  and timed 128-round measured soak are running; no publication or merge yet.
- Final full pinned python-snap7 3.0.0 emulator/scripted-peer suite passed, including
  all previous compound/concurrency/retry/transfer tests, the new eight boundary
  conversations (312 operations), sixteen clock-query peers, and both independent
  operation/value oracles. Bounded 216-attempt stress remained FD8/8, threads7/7,
  RSS5,603,328/5,619,712 bytes. The larger 128-round soak remains in progress;
  source is uncommitted on the new branch and hosted-platform runs are pending.
- Timed final 128-round macOS soak passed: 27,648 logical attempts, 6,912 retry
  reconnects, 34,560 physical TCP sessions; 181.98 seconds wall time. Baseline/peak
  FD8/8, threads7/7, RSS5,603,328/5,652,480 bytes (+49,152 bytes). Both proposed
  manual lengths have local macOS regression evidence; hosted-platform cold build
  and soak evidence still requires CI after publication. Plateau is relative,
  not universal leak freedom or hard native-operation cancellation.
- All five requested workstreams are implemented and combined local checks are
  green. One coherent local commit records the batch under standing owner commit
  approval. Publication is a separate step; no new PR has been opened or merged,
  and weekly/manual CI activation awaits merging the workflow into main.

## Value-boundary branch publication and follow-up review

- Owner requested pushing and identifying the next work. Published validated
  commit `f26364f` on `feat/classic-value-boundary-assurance`; local HEAD and
  upstream match. Before pushing, checked the sole outgoing commit's full author,
  committer, message and empty trailers. Both identities are Gijs Molenaar
  <gijsmolenaar@gmail.com>. No PR creation, merge or history rewrite occurred.
- Read-only source review identified further emulator-only assurance work:
  seeded overlapping read/write histories checked against an independent mutable
  memory model (the new boundary peers currently use per-operation payloads and
  separate addresses); generated mixed-size multi-item batches combined with
  queued calls and injected failures (existing generators and queue/batch tests
  cover these separately); successful-decoder validity and general malformed
  STRING/WSTRING rejection/locality proofs beyond existing encoder roundtrips;
  and exporting generated lifecycle/retry/write-progress conversations to the
  portable corpus, which currently has fixed multi-item/USER_DATA sequences.
- These are proposed extensions, not newly discovered bugs or authorized fixes.
  Start with the stateful overlap campaign for practical bug discovery. No PLC
  is required; controller-specific compatibility remains unvalidated. The soak
  schedule still requires merging its workflow into main. This publication log
  is a local documentation-only update after the pushed commit.

## Stateful, queued, decoder and portable conversation follow-ups

- Owner approved all four follow-ups in parallel on the existing value-boundary
  branch. Existing publication-log delta is preserved. Separate workers own
  overlapping mutable-memory histories, queued mixed-size multi-item faults,
  and actual decoder contracts; root owns portable primitive conversations and
  shared suite/export/CI/documentation wiring. No new push or PR is authorized
  by this implementation step alone.
- Focused live overlap campaign passed eight PDU240/480 histories: 1,040 operations
  and eight complete 2,048-byte DB observations. Independent bit/wire/model and
  parameter-preserving reducer checks pass; deliberate unrelated-bit and final
  guard-byte corruptions were caught by native observations. No client bug found.
- Focused queued campaign passed twenty conversations with 29 caller items per
  multi operation and five FIFO-admitted calls. It checks early-read retry identity,
  no retry after oversized-read first-chunk acknowledgement, lost first/partial
  write ACK provenance, recoverable item rejection, duplicate ranges, queue
  cleanup and no terminal resurrection. Independent wire mutations were rejected.
- Actual decoder success/header/allocation bounds and arbitrary-body capacity/
  current rejection proofs compile. Proof-only WSTRING locality in Value.lean
  quantifies arbitrary valid or malformed active UTF16 units and unrelated
  surrounding data; decoder implementations are unchanged. Final contract wiring,
  regressions, axiom audit and complete local validation are pending.
- Portable generated primitive histories and independent stdlib oracle are
  implemented: 32 seed/template combinations with full S7 wire exchanges,
  per-event lifecycle/progress observations, conservative/opt-in replay controls,
  malformed ACKs, duplicate caller identity and prefix uncertainty. Added pending
  reference correlation and invalid-length read controls after focused review;
  refreshed export and full validation are pending. Scope explicitly excludes
  IO scheduling, retry-budget consumption, remote memory and exactly-once writes.
- All streams are frozen and wired into the normal suite. Root-owned clean build
  passed all 128 jobs; complete native tests passed, including new exhaustive
  decoder regressions. All six generated corpus comparisons match exactly;
  independent primitive-conversation oracle passes 32/32 cases and 252 steps,
  including malformed ACK length/reference and invalid read-length controls.
- Root independently audited all 11 decoder contracts: only propext/Quot.sound;
  the extended CoreProtocolAssurance uses only the existing standard
  propext/Classical.choice/Quot.sound. No admissions, native certificates, new
  user axioms or decoder implementation changes. Ruff lint/format (30 files),
  whitespace checks and pinned actionlint1.7.7 both-workflow checks pass. Pinned
  emulator version remains python-snap7 3.0.0. Complete integration is running;
  no commit, push, PR or merge for this follow-up batch yet.
- Complete pinned-emulator/scripted-peer integration passed, including both new
  live campaigns (1,040 overlap operations and all 20 queued conversations),
  the 32/252-step primitive corpus oracle, all existing clock/boundary/transfer/
  retry/deadline/concurrency tests and final transport cases. Default measured
  stress passed 216 attempts/54 retry reconnects: FD8/8, threads7/7,
  RSS5,636,096/5,652,480 bytes (+16,384 bytes). No new client defect was found.
- All four requested streams are implemented and combined local checks are green.
  Recording one coherent local commit under standing owner commit approval;
  no new push, PR creation or merge. Portable histories are explicitly scoped
  to primitives and do not assert complete IO-client equivalence. The earlier
  publication-progress delta is included rather than discarded.

## Shared retry-budget decision and repeated-failure continuation

- Owner requested pushing and continuing. Published validated `83373d2` after
  checking author, committer, full message and empty trailers; no PR or merge.
- Read-only review found the aggregate retry guard duplicated in the two live
  exchange paths and portable primitive model. Continuing with a behavior-preserving
  shared pure decision, universal allowance/accounting proofs and repeated-failure
  live campaigns. No newly confirmed bug or change to conservative replay policy.
- `retryBudgetAfter` now returns the next allowance only when budget, lifecycle,
  error category and operation-safety gates permit retry; both live exchange paths
  use its returned value. Actual error classification is retained. Portable model
  uses the same primitive instead of a shadow aggregate guard; exported schema
  and eligibility semantics are unchanged. Pure proof and focused tests underway.
- Nine universal retry contracts compile, including exact equivalence to the
  existing eligibility guard, terminal/exhausted/nonretryable/default-mutation
  rejection, positive/decreasing allowance and general chain accounting/bounds.
  Both live exchange paths now use the same next-allowance value rather than
  duplicating the decrement. CoreProtocolAssurance includes the actual primitive's
  terminal/exhausted/soundness/decrease/chain-accounting properties.
- Focused repeated-failure campaign passed forty conversations across typed read,
  raw default/opt-in and write default/opt-in modes at allowances 0/1/2/4. Exact
  request/reference identity and physical attempt counts were preserved; eligible
  retries succeeded at the boundary or stopped at exhaustion, while conservative
  raw/writes never replayed. Fresh operations did not resurrect exhausted clients.
- Final root-owned clean build passed all 130 jobs. Full native tests pass,
  including 4,352 gate decisions, huge Nat budgets, 65 repeated chains and the
  strengthened live-write chronology/provenance checks. All six corpus exports
  remain exactly unchanged; Ruff lint/format (31 files) and whitespace checks pass.
  Nine new retry theorem axiom audits use only standard propext/Classical.choice/
  Quot.sound; no admissions, native certificates or new user axioms. Full final
  emulator/scripted-peer integration is running before commit/publication.
- Complete final emulator/scripted-peer suite passed, including all forty new
  repeated-failure conversations with strengthened chronological write outcomes
  and location provenance, all twenty queued batch cases, 1,040 overlap operations
  and every prior transfer/deadline/clock/transport regression. Default measured
  stress passed 216 attempts/54 retry reconnects: FD8/8, threads7/7,
  RSS5,619,712/5,701,632 bytes (+81,920 bytes). No new bug was found.
- All local checks are green. Recording and publishing the coherent retry-budget
  continuation on the existing branch under the owner's push/continue instruction,
  with full author/committer/message/trailer inspection before publication. No
  PR creation or merge; no claims of full IO termination, exactly-once writes,
  hard native cancellation or physical-controller compatibility.

## Five parallel emulator-only assurance streams (2026-09-24)

- Owner approved all five proposed streams in parallel: reconnect-stage failures,
  USER_DATA shape/continuation audit, actual multi-response decoder proofs,
  portable active-request histories, and scalability measurements before changes.
- Reconnect-stage tests and benchmark harness are implemented. USER_DATA audit
  reproduced two decoder defects: non-octet FF payload acceptance and rejection
  of native Snap7's service-specific successful empty acknowledgements. Narrow
  fixes are backed by native-server and Wireshark source evidence in the new
  USER_DATA evidence report. Client continuation identity correlation is being
  connected to both SZL and block-list assembly; sequence tokens stay opaque.
- Actual decoder proofs and active-request corpus are in progress. No physical
  controller, production compatibility, exactly-once write, full IO termination,
  or hard cancellation claim. No commit/push/PR/merge for this batch yet.
- All five sources are implemented/frozen. Reconnect campaign passed 75 native
  conversations; portable sessions passed its independent strict oracle at
  24 cases/323 events with mutation/fixed controls. Actual multi-response tests
  include 53,760 write byte/position cases, 60 mixed reads and 255 failure codes.
- Final root-owned clean build passed all 142 jobs. All seven corpus exports
  matched exactly before the final clean; rerunning all native/corpus/axiom
  checks and full integration now. Ruff lint/format passes all 35 Python files;
  pinned actionlint1.7.7 passes both workflows. The stale-reference live fixture
  now explicitly sets zero stale allowance rather than contradicting the
  default bounded-stale policy. No production correlation-policy change.
- Final native tests and all seven exact corpus comparisons passed after clean.
  Root audited all nine multi-response contracts, both actual continuation-helper
  contracts and the extended CoreProtocolAssurance: standard Lean axioms only
  (propext/Classical.choice/Quot.sound). No admissions, native certificates, new
  user axioms or multi-response decoder algorithm changes. Full integration is
  still running; benchmark measurements will be recorded once it is idle.
- Complete final pinned python-snap7 3.0.0 emulator/scripted-peer suite passed,
  including all 75 reconnect-stage cases, all 31 new USER_DATA conversations,
  active-session oracle 24/24 cases/323 steps, benchmark smoke correctness and
  every prior transfer/deadline/overlap/queued/transport campaign. Measured stress
  passed 216 attempts/54 retry reconnects: FD8/8, threads7/7,
  RSS5,636,096/5,668,864 bytes (+32,768 bytes). Final idle scalability run started;
  no client algorithm optimizations or publication actions have been taken.
- Final idle benchmark passed all 18 cases with three measured rounds each.
  Raw samples and measurement limits are tracked in scalability-2026-09-24.json
  and scalability-2026-09-24.md. Largest 256-KiB read medians were 305.483 ms at
  PDU240 and 148.902 ms at PDU480; 2,048-item read/write medians were
  29.195/44.201 ms and 26.480/27.255 ms respectively. Tested-size scaling is
  broadly proportional; no speculative core optimization, complexity or PLC
  performance claim. RSS observations are completion-triggered, not guaranteed
  inter-operation snapshots, peaks or allocation counts.
- All five requested streams and combined local checks are complete. Recording
  one coherent local commit under standing owner commit approval; no new push,
  PR creation or merge. Final metadata must use the owner's author/committer
  identity and contain no attribution trailers. Hardware validation remains
  separate; python-snap7's repository is untouched.
