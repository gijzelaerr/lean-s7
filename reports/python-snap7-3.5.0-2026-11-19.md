# python-snap7 3.5.0 against the conformance corpus — 2026-11-19

Differential evidence from `python integration/python_snap7_consumer.py` against the
released python-snap7 3.5.0, with the adapter of [the 3.4.0 report](python-snap7-3.4.0-2026-11-08.md)
unchanged. The reviewed result is `integration/python_snap7_baseline-3.5.0.json`.

| Result | 3.4.0 | 3.5.0 |
| --- | ---: | ---: |
| agree | 419 | 419 |
| gap | 85 | 85 |
| ambiguity | 14 | 14 |
| disagree | 62 | 62 |

## What 3.5.0 changes

No case changes status, and no recorded detail changes: the 3.5.0 baseline is identical to
the 3.4.0 one, byte for byte. The 62 disagreements and 14 ambiguities are the cases the
3.4.0 report classifies, with the same classification.

The 3.5.0 fixes touch behaviour that no corpus case exercises:

- gijzelaerr/python-snap7#988: `get_cpu_state()` reads SZL 0x0424 instead of sending a read
  request with no address, and the python-snap7 server refuses such a request.
- gijzelaerr/python-snap7#989: `read_tags` and `read_multi_vars` accept more than 20 items and
  split them over several requests of at most 20; `read_tags` refuses a symbolic tag.

A corpus case for the SZL 0x0424 reply, and for a read request without an address
specification, would let the next review check #988.

## Checks

All run on Windows with python-snap7 3.5.0:

- **`python integration/python_snap7_consumer.py`:** 580 cases, matching the new baseline.
- **`python integration/python_snap7_fuzz.py`:** no accepted-but-different values.
- **`python integration/real_captures.py`:** exits 0. python-snap7 reports the same five
  block-info request notes as with 3.4.0.
