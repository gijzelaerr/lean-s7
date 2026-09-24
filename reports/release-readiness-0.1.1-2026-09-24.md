# Classic S7 0.1.1 patch readiness — 2026-09-24

Owner authorized fixing the failed tag CI and publishing 0.1.1. Version 0.1.0
is immutable; no tag move, force push or production qualification is authorized.

- [0.1.0 branch CI](https://github.com/gijzelaerr/lean-s7/actions/runs/35980545833)
  passed on Linux/macOS for `100b2808f1d5407dd19cb86adb1e4c3b3e903e39`.
- [Repeated tag CI](https://github.com/gijzelaerr/lean-s7/actions/runs/35981008712)
  passed Linux but failed macOS in the compound WSTRING deadline peer:
  `compound timed out before valid first response`.
- The fixture delayed 150 ms within a 250 ms whole-call budget, requiring the
  first stage to succeed with only 100 ms scheduling margin. New test-only
  timings: shared budget 3,000 ms, exchange 6,000 ms, first peer delay 1 s,
  second peer observation 2.5 s. Second-stage deadline-reset regressions must
  still fail, while successful first-stage scheduling has a 2 s margin.
- The full suite repeats STRING/WSTRING/bit deadline cases twice and includes
  a deliberately wrong fresh-budget substitute for each. The peer's precise
  second-stage rejection diagnostic, plus client failure, is required; an
  unrelated failure does not count as mutation detection.
- Only test tooling/configuration, package version and release documentation
  change. Production Client/Transport/codecs/proofs remain unchanged. All
  experimental/no-PLC/no-hard-cancellation limits remain.

Validation and publication are pending. The release will attach exact branch
and tag check results outside the source tree, keeping the tested commit fixed.

- Focused local checks passed all 20 compound scenarios, three rounds of each
  STRING/WSTRING/bit deadline test, and all three fresh-budget substitutes.
  Each substitute triggered exactly its intended budget-refresh diagnostic;
  no unrelated failure was accepted. Ruff lint/format and whitespace checks
  pass. Starting the final clean build and full integration before commit.

- Final local validation passed on macOS arm64: clean build (165 jobs), complete
  native suite, all eight exact corpora, full pinned emulator/fault integration
  including two compound deadline rounds and all three mutations, both native
  endpoint profiles, Ruff lint/format, actionlint for both workflows and
  whitespace checks. Independent endpoint library fingerprint:
  `cd50afa408251588a7a781dc7083f34a5cb8d3bc4bc6aa561d05b6bdddb220b8`.
  Ready to commit/push; exact branch and tag CI remain release gates.

- Candidate `fbaa460` passed Linux; macOS passed all revised compound scenarios,
  both deadline rounds and all three mutation controls. It then exposed another
  fixture margin in the `combined` connection test: an initial 180 ms stage
  had to complete inside a 250 ms total limit before reaching the intended
  second stage. Scaled combined/fallback controls to a 3 s shared allowance,
  a 1 s first peer stage and a 2.5 s second stage. The latter still fits a
  fresh 3 s budget but exceeds the 2 s remaining on the original deadline.
  The operation control uses a 1 s limit with a withheld 1.5 s response;
  closure observation has 200 ms slack. Production deadlines are unchanged.

- Focused connection validation passed all nine portable cases. Scaling the
  shared `combined` mode initially changed the independent pending-TCP probe's
  timing too; local testing caught its two-second process timeout. Isolated that
  probe under `pending-tcp`, preserving its original 250 ms budget and two-second
  process-exit assertion. All ten locally applicable controls now pass. Starting
  the full clean verification again before the fix-forward commit.

- Final fix-forward local validation passed: clean build (165 jobs), complete
  native suite, eight exact corpus comparisons, full pinned emulator/fault
  integration including revised connection and repeated compound controls,
  native endpoint PDU240/480 profiles, Ruff lint/format, actionlint and whitespace
  checks. The earlier candidate's platform evidence is
  [run 35982464937](https://github.com/gijzelaerr/lean-s7/actions/runs/35982464937);
  it is not evidence for this fix-forward revision. Ready to commit/push and
  verify both branch and tag runs before release publication.

- Candidate `db5aad9` passed Linux. macOS passed the revised deadlines, resource
  and lifecycle campaigns and reached the final transport tests, then reset
  the peer's post-response `recv` during rejection cleanup. The oracle treated
  reset as an unexpected failure although Lean separately verified its precise
  rejection. Added a narrow cleanup-only receive helper allowing EOF/reset;
  strict handshake/request reads and the stale-flood no-retry guard remain.
  Self-controls verify byte preservation, EOF/reset handling and propagation of
  timeout and unrelated socket errors. No broad exception suppression.

- Cleanup fix-forward passed focused transport controls and the complete local
  clean build (165 jobs), native suite, eight exact corpora, full emulator/fault
  integration, independent native profiles, Ruff lint/format, actionlint and
  whitespace checks. Resource stress: 216 attempts / 54 retry reconnects,
  descriptors 8→8, threads 7→7, RSS 5,750,784→5,849,088 bytes. Pending TCP still
  exits under its independent two-second limit (258 ms observed). Awaiting this
  fix-forward revision's branch and tag checks before publishing 0.1.1.
