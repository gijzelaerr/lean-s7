# Selected operational-model rules and actual client coverage

## Scope

The pure single-wire model in `LeanS7/SessionConformance.lean` and its proofs
describe selected operational rules. They are not an equivalence theorem about
`Client` IO. This report maps those rules to independently observed localhost
tests and records important differences instead of treating pure-model fuzzing
as live-client evidence. No physical PLC, firmware compatibility, industrial
safety or exactly-once effects claim follows from these checks.

## Coverage mapping

| Rule or boundary | Pure evidence | Actual client evidence | Remaining distinction |
| --- | --- | --- | --- |
| Operation-aware retry permission and shared retry budget | `retryBudgetAfter`, session failure contracts; generated model events | `reconnect_faults.py`: 75 fixed conversations; `generative_reconnect.py`: 32 configurations outside the fixed suite, including reconnect COTP/setup EOF and terminal stage faults | Only the retry-policy decision is shared; transport IO is not formally equivalent to the model |
| A reconnect-stage failure consumes budget without a new operation send | Failure contracts and typed reconnect phases | Both reconnect campaigns independently count sessions and exact operation resends; native fixture checks chronological write attempts and prior uncertainty | Bounded selected traces, not all network schedules |
| Lost write ACK and opt-in replay preserve earlier uncertain effects | Write-progress contracts/model trace | Existing retry/provenance peers plus fixed/seeded reconnect campaigns assert acknowledged, pending and replayed-unknown attempts | ACKs cannot prove remote effects of earlier attempts |
| Duplicate destinations retain caller/chunk identity and chronological writes | Write-progress primitives, portable conversation/session cases and seeded model histories | `write_provenance.py` duplicate scenarios, overlap/queued-batch peers and retry campaigns independently check item indices, chunk offsets and attempt order | The new scalar correlation histories use distinct destinations; duplicate-address coverage comes from these existing live campaigns, not the scalar generator |
| Correlated successful response completes current operation | Actual codec contracts and model response transitions | Existing live campaigns and new `live_correlation.py` exact request/payload checks | Model uses multi-item codec/configuration; new campaign observes scalar reads/writes |
| Stale response filtering uses a bounded common receive deadline | Not represented as a filtering loop in the session model; mismatched response events are codec failures there | Existing stale-flood/drip-stale deadline checks plus new successful stale counts 0, 1 and 2 before a current reply | New checks cover selected cleanly framed stale ACKs, not arbitrary malformed stale packets |
| PLC rejection releases the operation gate while allowing appropriate same-session reuse | Global PLC rejection currently drives the single-wire model into disconnected/failed; multi-item item rejection is a decoded result | Existing queued PLC/batch campaigns plus new scalar global and item rejection histories check connected lifecycle, fresh healthy calls, and zero pending calls | This is a documented model/client semantic difference, not evidence of parity. Scalar item rejection yields `plcRejected` and a globally-rejected scalar write attempt because scalar progress does not expose an item code |
| Terminal protocol error prevents fresh-call resurrection | Model closed/terminal gating contracts | Existing lifecycle/fault campaigns; new stale-overflow/malformed-current suffixes observe disconnect, fresh-call `disconnected` and no extra accepted socket | Pure explicit `.closed` differs from actual disconnected-after-failure; neither cancels arbitrary underlying socket tasks |
| Request reference wrap and per-call progress reset | Codec correlation contracts; model caller supplies reference and begin resets progress | Existing reference-wrap test plus new mixed histories check wire reference 65535, then 0, then increasing; exact one-call write attempt arrays | Model does not allocate references or implement the serialization gate |

## New bounded mixed-correlation campaign

Files: `LeanS7/LiveCorrelationTests.lean` and `integration/live_correlation.py`.
The default campaign runs four deterministic seeds (`7`, `2026`, `65535`,
`5715779`) across negotiated PDU lengths 240/480 and two terminal suffixes:
16 conversations with nine scalar operations each.

Every history has shuffled read/write success, global PLC rejection and item
PLC rejection categories. Before each current response, zero, one or two
structurally valid stale ACKs carry a different reference. Stale responses vary
between unrelated-service ACKs and global PLC errors. Two final healthy calls
prove reuse after the earlier rejections and reset write progress before the
terminal operation. The terminal suffix is either three stale replies with no
current reply (configured maximum is two) or a current-reference wrong-service
ACK following two stale replies.

The independent Python peer constructs exact expected job bytes without calling
Lean or the pure-model oracle. It checks the header, section extents, request
reference, function, DB/address, item count and payload. Its self-checks reject
mutations of discriminator, reference, section length, function, address and
write payload. Existing framing helpers and the COTP/setup handshake are reused;
this is independent request/outcome validation, not a second independent
transport implementation or normative protocol specification.

The actual native client asserts payload/error category, connected versus
terminal lifecycle, gate release and exact per-call write attempt locations and
outcomes. Terminal write failures retain a pending uncertain attempt; known
scalar rejection records a rejected attempt. The peer then checks only expected
COTP disconnect/EOF traffic, no additional request and no reconnect socket.
No mutating retry is enabled. A two-retry read configuration makes an accidental
protocol retry visible to the listening peer.

Validated on 2026-09-24:

- Focused Lean module check and native build (108 jobs) passed.
- All 16 live conversations passed: 144 operations, 200 stale ACKs,
  64 successful operations, 64 recoverable PLC rejections and 16 terminal faults.
- Deterministic generator, reference-wrap and exact-wire mutation controls passed.
- Ruff lint and formatting checks passed for the new harness.

The sandbox forbids loopback binding by default; the live campaign was run with
approval for localhost-only dynamic sockets. No emulator changes were needed.
Failures print a deterministic bounded replay command, for example:

```console
python integration/live_correlation.py --seed 7 --pdu 240 --terminal overflow
```

## Closure boundary

This closes the selected successful-stale-filtering / mixed scalar rejection
test gap and supplies L2's scoped coverage mapping, not full model/live parity.
Stale receive loops,
scalar versus multi-item rejection semantics, reference allocation, gate
scheduling, transfer phases and socket cancellation still require separately
scoped modeling or explicit exclusions. The documented global-rejection model
difference should be resolved before any future model-to-client equivalence
claim; changing it would also change the versioned session corpus semantics.
