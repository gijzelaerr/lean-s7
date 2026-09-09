# python-snap7 classic-S7 audit — 2026-09-08

Investigated python-snap7 master `383852f3eb6465c92aebd7d3457c14e7d6f4f92a`
against lean-s7 `ad1b54265d7867ecac6d0e6927986add0760cf6b`.
The local Python checkout matched GitHub master at investigation time. The
checkout's `snap7.__version__` is stale (`3.0.0`), so results are identified by
commit, not presented as a released-version test. Python 3.13, macOS.

## Existing issues

Reviewed the open issue list, recent closed issues, relevant historical keyword
matches and open PR titles before filing. Executable verification was scoped to
classic S7, which lean-s7 models; it does not validate S7CommPlus, PPI, or
hardware/configuration-specific reports such as #844.

| Issue | Verdict on current master | Qualification |
| --- | --- | --- |
| [#862](https://github.com/gijzelaerr/python-snap7/issues/862) oversized TPKT encoder input | Reproduced | Input is rejected, but with `struct.error`; exception-contract hardening, not acceptance of oversized frames. |
| [#863](https://github.com/gijzelaerr/python-snap7/issues/863) nonzero COTP TPDU number | Reproduced | Invalid Class 0 number accepted. |
| [#864](https://github.com/gijzelaerr/python-snap7/issues/864) undersized TPKT encoder output | Reproduced | Private helper accepts undersized payload; ordinary DT construction supplies a three-byte header. |
| [#865](https://github.com/gijzelaerr/python-snap7/issues/865) COTP header length ignored | Reproduced | Malformed input exposes payload despite invalid LI. |
| [#866](https://github.com/gijzelaerr/python-snap7/issues/866) undersized TPKT receive frame | Reproduced at framing boundary | Corpus intentionally substitutes the next-layer parser. The normal COTP path rejects a two-byte payload later. |
| [#813](https://github.com/gijzelaerr/python-snap7/issues/813) server CC off by one (closed) | Fixed on tested master | Exact CC bytes and LI regression test passes. |
| [#804](https://github.com/gijzelaerr/python-snap7/issues/804) server fragmentation / INT-DINT widths (closed) | Fixes present in source | Server reassembles to EOT; INT/DINT are included in both width mappings. Reassembly-bound regression test passes. |

The five open conformance reports are valid as stated, but their impact differs.
No duplicates, closures, or comments were added to these existing issues.
TPKT length bounds were cross-checked against
[RFC 1006 section 6](https://www.rfc-editor.org/rfc/rfc1006.html#section-6);
Class 0 handling against
[RFC 2126 section 6.5](https://www.rfc-editor.org/rfc/rfc2126.html#section-6.5).

## New confirmed bugs filed

| Issue | Observed failure |
| --- | --- |
| [#867](https://github.com/gijzelaerr/python-snap7/issues/867) | `db_read(1, 0, 4)` silently returns one byte from an incomplete successful item. |
| [#868](https://github.com/gijzelaerr/python-snap7/issues/868) | `db_write` returns success for a READ response with the matching reference. |
| [#869](https://github.com/gijzelaerr/python-snap7/issues/869) | A 500-WORD read at PDU=480 requests a 942-byte response and overlaps chunks. |
| [#870](https://github.com/gijzelaerr/python-snap7/issues/870) | `write_multi_vars` turns two WORDs into two BYTEs, dropping half the payload. |

Each issue includes a self-contained reproduction, actual/expected behavior,
source revision, and an explanation of the Lean comparison. Every published
Python snippet was executed before filing. Transport was replaced by an in-memory
peer; the public client methods and real protocol codecs were exercised. No
physical PLC was contacted and no production-compatibility claim is made.

The Python reproductions deliberately assert the observed buggy behavior. They
are an audit artifact, not passing conformance tests; they should fail when the
corresponding bugs are repaired.

## Reproduction and checks

With a sibling python-snap7 checkout and its Python environment:

```sh
PYTHONPATH=../python-snap7 ../python-snap7/.venv/bin/python -B integration/tpkt_conformance.py
PYTHONPATH=../python-snap7 ../python-snap7/.venv/bin/python -B integration/cotp_conformance.py
PYTHONPATH=../python-snap7 ../python-snap7/.venv/bin/python -B integration/snap7_bug_audit.py
lake env lean --run integration/Snap7BugAudit.lean
lake build lean-s7 lean-s7-tests
lake exe lean-s7-tests
ruff check integration/snap7_bug_audit.py
ruff format --check integration/snap7_bug_audit.py
```

Observed: three TPKT and two COTP divergences (expected nonzero exits); all four
new Python bugs reproduced; Lean rejected both invalid responses and computed
two-byte-element counts `[231, 231, 38]`; Lean build/tests and Python lint/format
checks passed. Two focused upstream server regression tests also passed.

Formal claims remain limited to the existing checked Lean theorems. The new
Lean probe executes decoders and chunk planning; it adds no theorem. Lean has no
Python ctypes API and no DB WORD override: the latter comparisons use the common
element-to-byte arithmetic, with captured Python requests as the direct evidence.

No implementation fixes, commits, or pushes were made during this audit.
