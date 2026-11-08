# python-snap7 3.4.0 against the conformance corpus — 2026-11-08

Differential evidence from `python integration/python_snap7_consumer.py` against the
released python-snap7 3.4.0, after the two adapter corrections that
[the 3.3.1 report](python-snap7-3.3.1-2026-11-02.md) left out (#67). The reviewed result is
`integration/python_snap7_baseline-3.4.0.json`.

| Result | 3.3.1, as recorded | 3.3.1, corrected adapter | 3.4.0 |
| --- | ---: | ---: | ---: |
| agree | 413 | 409 | 419 |
| gap | 85 | 85 | 85 |
| ambiguity | 20 | 14 | 14 |
| disagree | 62 | 72 | 62 |

## Adapter corrections

Both corrections make the consumer test python-snap7 instead of doing its work for it. They
are applied to every version, so the 3.3.1 baseline is re-recorded with them. The 3.0.0
baseline does not change.

1. **Clock digits.** The decode check for a rejected ten-byte clock reply now covers the
   three millisecond digits (byte 8 and the high nibble of byte 9), not only year to second
   (bytes 2-7). It does this only when the installed python-snap7 decodes milliseconds,
   which a probe with a known reply decides: 3.3.1 and 3.4.0 do. 3.0.0 does not, because it
   returns the current time instead of decoding the reply. The detail for a
   reply whose only invalid field is the weekday now reads "python-snap7 decodes no weekday,
   the only invalid field". It used to say "no weekday or milliseconds", which was out of
   date for 3.3.1.
2. **Fragment references.** `assemble()` no longer calls `validate_pdu_reference`. For the
   two services python-snap7 implements, SZL (group 4) and the block list (group 3), each
   continuation case also runs the library's own follow-up loop:
   - `Client.read_szl` or `Client.list_blocks_of_type`, against the corpus replies, through a
     scripted connection;
   - numbered from the first step's reference;
   - a reply it refuses over its PDU reference counts as the rejection.

   Before, the four `fragments-*-reference` cases agreed only because the adapter checked
   the reference itself.

With the corrected adapter, 3.3.1 reports both bugs from its report as 10 disagreements:
`clock-millisecond-low-bcd-10..15` and `fragments-{3,4}-{0,81}-reference`.

## What 3.4.0 changes

Exactly those 10 cases move from disagree to agree. No other case changes status.

- **Clock:** gijzelaerr/python-snap7#966 rejects a millisecond digit above 9, in the client
  and the server, so `clock-millisecond-low-bcd-10..15` agree.
- **Fragments:** gijzelaerr/python-snap7#967 sends `read_szl` and `list_blocks_of_type`
  follow-ups through `_send_receive`, which checks the PDU reference. The real loops now
  refuse the out-of-order third fragment at the step the corpus expects. 3.3.1 accepted it
  and returned the assembled result.

The 62 remaining disagreements are the same cases as the 62 in 3.3.1, with the same
classification:

- leniency: transport size, last-data-unit on single-response services, data-unit
  reference;
- deliberate python-snap7 behaviour;
- lean-s7 stricter than the evidence supports.

The 14 ambiguities are the weekday cases (python-snap7 does not decode the weekday) and
the remaining clock-decode ambiguities the 3.3.1 report lists.

gijzelaerr/python-snap7#968 (`set_wchar` above U+FFFF), #973 (public tag codec), #974 (strict
`parse_tag`), #975 (setters refuse a short buffer) and #979 (COTP disconnect reference) are
also in 3.4.0. No corpus case exercises them.

## Checks

All run on Windows with python-snap7 3.4.0, unless stated otherwise:

- **`python integration/python_snap7_consumer.py`:** 580 cases, matching the new baseline.
  - The same run with 3.0.0 and 3.3.1 matches their baselines.
- **`python integration/python_snap7_fuzz.py`:** no accepted-but-different values.
- **`python integration/real_captures.py`:** exits 0. python-snap7 reports the same
  block-info request notes as with 3.3.1.
