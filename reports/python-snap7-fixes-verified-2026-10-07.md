# python-snap7 fixes verified against the corpus and real captures — 2026-10-07

All ten python-snap7 issues filed from this work ([#923](https://github.com/gijzelaerr/python-snap7/issues/923)–[#927](https://github.com/gijzelaerr/python-snap7/issues/927),
[#930](https://github.com/gijzelaerr/python-snap7/issues/930), [#931](https://github.com/gijzelaerr/python-snap7/issues/931) and
[#935](https://github.com/gijzelaerr/python-snap7/issues/935)–[#937](https://github.com/gijzelaerr/python-snap7/issues/937)) were fixed on python-snap7 `master` within hours
(commits #928–#942, up to `4550e93`) and closed. This report re-runs the evidence that
motivated them against that build. It is **unreleased**: the latest release is still
3.2.1, and the development build reports the same version string, so its results are
not stored as a reviewed baseline (`--no-baseline` prints them without touching one).

## Real captures

`python integration/real_captures.py` with the `master` build (see
[the replay report](real-s7-300-captures-2026-10-07.md)): python-snap7 now matches the
real traffic almost everywhere. Per capture, python-snap7 checks ok: 17/17 (clock), 70/70
(SZL status), 27/31 (block lists), 17/18 (download), 41/41 (upload and CPU control). Its
read-SZL and follow-up requests, ten-byte clock replies, set-clock acknowledgements
(through the new `accept_null_ack` option), `_GARB` and `_MODU` jobs and upload path are
byte-identical to or accepted from the real devices. The only remaining differences are
the five block-info requests, which end in the file-system letter `A` where the real
engineering tool sends `B`. Lean and native Snap7 also use `A`, so this is a choice, not
an error, and the report keeps it as a recorded difference.

## Corpus consumer (467 cases)

| | 3.2.1 (released) | `master` (`4550e93`) |
| --- | ---: | ---: |
| agree | 385 | 379 |
| disagree | 68 | 56 |
| gap | 12 | 12 |
| ambiguity | 2 | 20 |

Twelve cases flipped from disagree to agree: the block-count duplicate cases (the table
must now be exactly 28 bytes), the block-info request layout, the two out-of-range years,
and the seven clock round trips (ten-byte reply and Sunday-first weekday). None regressed.

Eighteen cases moved from agree to ambiguity, which is a consequence of the fix and not a
regression: python-snap7 previously rejected every ten-byte clock reply, so the
rejection cases agreed vacuously. Now that it decodes the reply, it returns a `datetime`
with no weekday and no milliseconds, so it cannot validate the only fields those cases
make invalid (weekday 0 and 8–15, millisecond digits above 9). The consumer labels this
`ambiguity` ("python-snap7 decodes no weekday or milliseconds") unless a BCD digit it does
decode is invalid, which would stay a disagreement. The corpus `set-clock` request fixes an
arbitrary weekday that python-snap7 derives from the date, so a request differing only in
that nibble is also an ambiguity. The reviewed 3.0.0 and 3.2.1 baselines still verify
(the 3.0.0 baseline was regenerated: 50 clock cases changed from disagree to ambiguity).

The 56 remaining disagreements are the hardening leads in
[the 3.2.1 report](python-snap7-3.2.1-2026-10-07.md) (transport size, last-data-unit
values, short string storage, supplementary WSTRING characters, a failed multi-read item),
which were not filed.
