# Independent official native Snap7 endpoint — 2026-09-24

## Endpoint and provenance

This runs actual Lean Client IO against a different protocol implementation, not
the Python emulator or an oracle driven by Lean output. It is localhost testing
of registered buffers, not physical PLC qualification.

- Source: [official Snap7](https://github.com/davenardella/snap7), pinned revision
  [`30f37da3114024a71ba93f7fd855c680b97a406f`](https://github.com/davenardella/snap7/tree/30f37da3114024a71ba93f7fd855c680b97a406f).
- Source archive SHA-256:
  `2840d50a833d928e5175b8ccc5383fae0fcc3e826c07e60b2b4190a30c613c36`.
- Native C++ source is compiled unmodified. No wire, ABI or behavior patch is
  applied to the official endpoint. It remains a separate test dependency and
  is never linked into the client/library.
- Builder records source revision/digest, compiler, platform/machine and native
  binary digest. Harness checks that manifest and binary digest before loading
  the C API. This is reproduction bookkeeping, not a signed supply-chain proof.
- Python ctypes only registers task-owned storage, starts/stops the native
  server, and verifies memory. It does not implement S7 framing or translate
  requests for this endpoint. No python-snap7 code is imported by the harness.

## Profile and observable checks

`LeanS7/NativeInteropTests.lean` drives two fresh native-server profiles at PDU240
and PDU480. Each independently allocates DB1/DB2 (4,096 bytes each) and process
input/output/marker buffers (512 bytes each). Every byte is initialized by an
independent stdlib oracle.

The actual client checks negotiated PDU length; complete initial DB contents;
1,401-byte chunked DB writes/readback; Latin-1 STRING and supplementary UTF-16
WSTRING; bit update; 40 odd-size multi-item writes and matching batched reads;
chunked I/Q/M reads/writes; recoverable missing-DB rejection and same-session
reuse; metadata for two distinct block numbers; CPU-state query; gate release
and clean disconnect.

Metadata checks are endpoint-profile expectations, not new universal decoder
restrictions. The official server returns outer type zero and compact DB subtype
0x0a, corroborating why those fields must remain distinct. Returned block numbers
match requested DB1/DB2 with the corrected native number-then-`A` request layout.

After native stop, the independent Python oracle compares the **complete** five
backing buffers against separately constructed expected bytes: 9,728 bytes per
profile, 19,456 across both. This detects incorrect target selection, encoded
typed bytes and mutations outside intended ranges—not merely self-consistent
client readback. Negative controls mutate each buffer's final surrounding byte
and reject missing/extra buffer identities. It remains bounded evidence, not
exhaustive proof of arbitrary IO schedules or remote side effects.

## Reproduce

```console
lake build lean-s7
python integration/native_snap7_build.py
python integration/native_snap7.py --library .lake/native-snap7/libsnap7.dylib
```

Use `.so` on Linux. Build requires a C++ compiler and initial archive download;
tests bind only dynamic localhost ports. Full CI runs the same profile on Linux
and macOS. Platform results must be checked at the exact candidate revision.

## Limits and validation progress

Both focused profiles pass locally on macOS arm64. No new production Client
defect was found. Final clean/native/emulator/corpus/platform checks are recorded
in [release readiness](release-readiness-2026-09-24.md).

Native-server upload/full-upload and other unsupported services are excluded
from this endpoint profile. (Update, 2026-10-08: the official server's source
answers every start-upload with a "need password" header error, so the native
profile now also asserts that `upload` surfaces that as a PLC rejection and
that the client then ends the session cleanly, as it does for every failed block
upload, with no pending operation. This is evidence for the refusal path only; no
positive upload evidence exists from this endpoint. The profile also builds and
passes on Windows with the pinned source and MSVC, producing `snap7.dll`.) Their existing scripted-peer/emulator evidence is
not relabeled as independent native-server success. Physical counter/timer
indexing, controller/firmware-specific layouts/availability, controller-changing
operations and hard cancellation remain unqualified.

An initial attempt used the older SCADACS fork at
`f6ff90317ca5d54250f4dcd29209689a74e26d82`. It required a macOS compile guard and
then crashed in native destruction. That attempt was abandoned and contributes
**no successful interoperability evidence**; neither its source nor its patch
is part of the final test dependency. No causal claim about the crash follows
from that observation, and no external repository was modified.
