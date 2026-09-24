# Supported profile and release gates

## Current profile

This is an experimental classic S7comm Lean client and executable specification,
not a production-qualified driver. Version 0.1.0 is the approved initial
experimental release, not a compatibility certification. See
[the completion matrix](COMPLETENESS.md) for the bounded feature scope and open
gates. S7comm Plus, optimized symbolic access, a native server, and python-snap7
API parity are not release requirements for this profile.

- Toolchain: exactly the checked-in `lean-toolchain` (Lean 4.33.1).
- Runtime: Lean/native networking; Python is only needed for test harnesses.
- Endpoint: IPv4, IPv6 or hostname; classic ISO-on-TCP with configured rack/slot
  or explicit TSAP. Connection negotiation must satisfy both S7 and COTP limits.
- Validation: local macOS testing, pinned python-snap7 3.0.0 emulator, independent
  portable-vector oracles, scripted TCP peers and a pinned official native Snap7
  endpoint. Linux and macOS are full CI targets; inspect
  the results for the exact revision before claiming platform validation.
- No real Siemens controller family or firmware is qualified yet. Counter/timer
  addressing and controller-specific management semantics need independent
  captures or hardware. Read/write tests against the emulator are not evidence
  of physical controller behavior.
- Retries are conservative by default. Explicit mutating retries can duplicate
  side effects. Detailed write progress reports uncertainty, not exactly-once
  execution or rollback.
- Receive and connection budgets are cooperative. Socket sends and underlying
  OS cancellation are not covered by hard deadlines. No industrial safety,
  real-time, full client IO-equivalence or universal interoperability guarantee
  is provided.
- Process-image bit overrides are not persistent CPU force-table operations.
- Typed `Client.getBlockInfo` supports block numbers 0–65535 and checks the
  returned number. The low-level request codec retains the five-digit 0–99999
  domain. Metadata exposes the outer type and compact subtype separately;
  neither is universally correlated with the requested type. See
  [the policy and evidence](../reports/block-management-2026-09-24.md).

Controller-changing services (download/delete, CPU control, clock/password
changes, compression, RAM-to-ROM copy and process-image writes) must not be used
operationally before explicit validation on the target controller and firmware.
The emulator and scripted peers run on localhost; no PLC access is required by
the test suite.

## Consume the library

Use the same toolchain and add a dependency to a consumer's `lakefile.toml`:

```toml
[[require]]
name = "lean-s7"
git = "https://github.com/gijzelaerr/lean-s7.git"
rev = "<reviewed-full-commit-hash>"
```

Choose a published full commit hash rather than a moving branch, then run
`lake update` and commit the consumer's `lake-manifest.json`. Import `LeanS7` for
the public library or `LeanS7.Client` for the client surface. The separate
`lean-s7-fuzz` executable and JSON/session fixtures are test tooling, not runtime
requirements. No prebuilt binary distribution is promised.

An offline external consumer check builds a separate temporary Lake package,
imports the public library, checks the core proof, compiles the Client API and
runs setup/value codec round trips:

```console
python integration/package_smoke.py
```

It uses a local path dependency and opens no sockets. It does not test remote
Git retrieval, a release archive, cross compilation or PLC interoperability.

Independent endpoint cross-tests build an unmodified, SHA-256-pinned official
native Snap7 source revision into `.lake/native-snap7`, then exercise localhost
PDU240/480 profiles. A C++ compiler and network access for the initial source
archive download are required. The native library is not linked into lean-s7:

```console
python integration/native_snap7_build.py
python integration/native_snap7.py --library .lake/native-snap7/libsnap7.dylib
```

Use `libsnap7.so` on Linux. The test checks the build manifest and library digest,
then independently compares all registered backing memory after actual Client
IO. The profile covers DB/I/Q/M memory, batching, typed strings/bits, rejection
reuse, metadata and CPU-state queries, not unsupported native-server upload or
other controller-changing services. See
[the endpoint evidence](../reports/native-interop-2026-09-24.md).

## Exit gates

An emulator-only experimental release and a hardware-qualified profile are
different milestones. A merge alone satisfies neither.

Before proposing an emulator-only experimental release:

- Close or explicitly defer each emulator-only gate in `COMPLETENESS.md`, with
  recorded reason and supported-profile impact. Do not silently call a deferred
  item verified.
- Run the full clean build/native/integration/lint/format checks in `CLAUDE.md`;
  compare all eight generated corpora exactly and run the external consumer test.
- Audit theorem claims and their axiom dependencies; proofs must not rely on
  admissions or newly introduced user axioms.
- Check the exact candidate revision's Linux/macOS CI and resource-soak evidence;
  document missing platform evidence rather than borrowing earlier results.
- Review exported API and corpus-schema changes, including backward-compatibility
  decisions. Keep the client/library free of fixture-only imports.
- Record tested revision, toolchain, emulator version, supported operations,
  known limits and reproduction commands. Choose version/tag and publication
  only with repository-owner approval.

Before claiming any hardware-qualified profile, additionally record controller
model, firmware, access configuration, captures and reproducible non-destructive
tests; validate counter/timer addressing and each claimed service. Validate
controller-changing operations separately on appropriate test equipment with
explicit authorization. Qualification applies only to those recorded profiles,
not all classic-S7 controllers.
