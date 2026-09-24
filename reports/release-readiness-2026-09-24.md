# Classic S7 0.1.0 release readiness — 2026-09-24

The repository owner approved release version 0.1.0. This is an experimental
classic-S7 client/specification release, not controller qualification or a
safety certification. Publication waits for the exact final candidate's checks.

## Progress

- Published the three locally validated commits through
  `f34125859df0bf61855bd11004d089b7c344a58c`; author/committer/messages/trailers were
  inspected and contain only the repository-owner identity, without attribution
  trailers. No history rewrite.
- Linux CI for that revision started as run35975220750. The previous CI
  configuration exercised only Linux; adding the full macOS matrix instead of
  calling local macOS evidence hosted-platform validation.
- Building a pinned SCADACS/native Snap7 dependency for independent endpoint
  cross-tests. This is separate from the Python server emulator; neither endpoint
  substitutes for real-controller evidence.
- Supported-profile review and release notes retain explicit limits: classic
  protocol only, no API parity/S7Plus requirement, physical counter/timer and
  controller-changing semantics unqualified, conservative replay with unknown
  lost-ACK effects, no full IO-equivalence or hard socket-cancellation guarantee.

Further validation and publication results will be appended before release.

- [Linux CI passed](https://github.com/gijzelaerr/lean-s7/actions/runs/35975220750)
  for published `f341258`. This is evidence for that revision only, not the
  pending matrix/native-test candidate.
- Switched from the crashing older fork to pinned, unmodified official native
  Snap7 revision `30f37da3114024a71ba93f7fd855c680b97a406f`. Both focused localhost
  PDU240/480 profiles pass on macOS arm64; independent oracle validates all five
  buffers/9,728 bytes per profile. See [scope/provenance](native-interop-2026-09-24.md).
- Added full Linux/macOS CI matrix with the independent endpoint test; prepared
  `docs/releases/0.1.0.md`. Owner selected 0.1.0 rather than a prerelease version.
  Final clean validation and exact-revision hosted checks are still pending.
- Source and test harnesses frozen for the final root-owned clean build. Native
  build now emits a provenance manifest; tests verify pinned source/binary
  digests and run surrounding-byte/missing/extra-identity negative controls.
  No native-source patch remains. Full local validation is running before the
  final candidate commit/push; release will use its exact tested commit.

- Final local checks passed on macOS arm64: clean build (165 jobs), complete
  native test suite, all eight exact conformance-corpus reproductions, full
  pinned Python emulator/scripted integration, independent native endpoint
  PDU240/480 tests, Ruff lint/format, actionlint for both workflows, and whitespace
  checks. The final local native library SHA256 is
  `0d0eac0fdcd6632a67cd4bcfbdaa6e57f43d2c5242b30909c02a591fb99e520e`;
  this identifies that local build, not a portable reproducible-binary promise.
  The candidate is ready to commit and publish for exact-revision Linux/macOS
  checks. Release publication remains gated on both hosted jobs succeeding.

- Candidate `2134bb1` passed the entire Linux job, including the independent
  endpoint. macOS compiled successfully but exposed a fragile existing unit
  test: its successful first stage slept 80 ms inside a 120 ms budget, leaving
  only 40 ms scheduling margin. Increased only that test's shared budget/stage
  durations to 3,000/1,000/2,500 ms. It still distinguishes the reused deadline
  from a fresh per-stage budget; production timeout behavior is unchanged.
  Preparing a fix-forward candidate after repeating the full local checks.

- Fix-forward local validation passed: clean build (165 jobs), complete native
  tests, eight exact corpora, complete emulator/fault integration, Ruff and
  actionlint. Resource stress passed 216 attempts / 54 retry reconnects with
  descriptors 8→8, threads 7→7, and RSS 5,685,248→5,750,784 bytes. Both official
  native endpoint profiles passed again; the rebuilt local library SHA256 is
  `e2c25f3f363e30e575856bc20b024bef38aad0b10fe64015ad5fddc8744a57e9`.
  Extended pure-model differential campaign also passed 1,024 histories /
  23,730 events on the unchanged model. Awaiting the fix-forward candidate's
  exact-revision hosted results before tagging; no release tag yet.

- Candidate `00d13bd` passed native tests on both platforms. macOS then exposed
  another fixture race: the initial retry peer waits 230 ms before closing,
  while the client test allowed only 250 ms to observe that EOF. An exchange
  timeout can make the peer return before entering the reconnect handshake.
  Raised only retry-fixture exchange allowance to 1,000 ms and its successful
  transfer allowance to 2,000 ms. The rejection control retains its original
  420 ms shared transfer deadline, so reconnect must still not reset it.
  Production defaults/deadlines are unchanged. Full local checks will repeat.

- Retry-fixture fix-forward passed the full local clean build, native suite,
  eight exact corpus reproductions, complete emulator/fault integration,
  independent native profiles, Ruff lint/format, actionlint and whitespace
  checks. Resource stress again held descriptors 8→8 and threads 7→7 across
  216 attempts / 54 retry reconnects (RSS 5,701,632→5,783,552 bytes). Local native
  library SHA256: `cd50afa408251588a7a781dc7083f34a5cb8d3bc4bc6aa561d05b6bdddb220b8`.
  Ready for the next exact-revision hosted gate; release remains unpublished.
