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
