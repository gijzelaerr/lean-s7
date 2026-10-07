# Wireshark S7comm cross-check of the conformance corpus — 2026-10-07

Independent-decoder evidence from `python integration/wireshark_corpus.py` using
TShark 4.6.8 (Wireshark's `s7comm` dissector). Corpus PDUs are wrapped in TPKT/COTP
and synthetic Ethernet/IPv4/TCP port-102 frames of an offline pcap, dissected with
`tshark -T fields`, and compared with the corpus's decoded values. No sockets or
controllers are involved. This is **not** controller qualification (gate H1), and it
does not prove either decoder correct: it shows where two independently written
decoders of the same bytes agree.

The check is optional and is not run in CI (it needs `tshark`). The reviewed
classification of every probe is in
[`integration/wireshark_baseline.json`](../integration/wireshark_baseline.json); the
run fails if any probe changes status, and warns if `tshark` is not 4.6.x.

## Result

232 probes: **73 agree, 156 limitation, 3 fixture, 0 disagree.**

| Status | Meaning |
| --- | --- |
| agree | Accepted case: every compared dissected field equals the corpus value. Rejected case: the dissector also reports the packet as malformed. |
| limitation | A corpus rejection that the dissector decodes without complaint. |
| fixture | The dissector's service-specific payload parser reports a malformed packet because the corpus fixture is shorter than the real record; envelope fields still agree. |
| disagree | An accepted case whose fields differ. None. |

Compared fields for accepted cases: ROSCTR, PDU reference, function code, USER_DATA
function group, subfunction, sequence number, data-unit reference, last-data-unit
flag, return code, transport size, data length, item DB/area/byte address/length for
read and write requests, per-item return codes and read payload bytes, upload
continuation flag and fragment bytes, and read/write response payloads. The 17 request
packets are checked against independently stated function and group/subfunction
numbers (see `REQUEST_SHAPE`); they are not derived from lean-s7.

Findings of interest:

- **The last-data-unit flag agrees.** Wireshark reports `Last data unit: Yes (0x00)`
  for `complete-szl` and the opposite for `continuation-with-more-data`, matching the
  corpus's `has_more_data` (this also matches the upload `functionstatus.more` flag).
- **Odd-length padding agrees.** For `mixed-read-odd-padding` the dissector yields the
  same per-item payloads (`aa`, `bbcc`) and the failure code 5 for the middle item.
- **Fixtures with synthetic SZL/clock payloads (3 cases).** `complete-szl` carries SZL
  0x0424 with a four-byte record and `ff-4-1-9-2`/`ff-7-1-9-2` carry two-byte
  SZL/clock payloads. The dissector applies the real 0x0424 and clock layouts and
  raises a malformed-packet exception, though the USER_DATA envelope agrees. The
  corpus documents that the management cases are generic codec histories, not typed
  record fixtures. If these were ever used as dissector-visible examples they would
  need realistic records; that would be a corpus change and, under
  `VERSIONING.md`, a compatible addition only if existing cases are not altered.
- **Limitations (156).** 139 are management decoder rejections (wrong group or
  subfunction, USER_DATA/item error codes, truncated or trailing payloads, invalid
  continuation flags); the other 17 are `s7.json` rejections (USER_DATA, upload,
  read/write and multi-item responses with truncated, trailing, mismatched or
  invalid content). The dissector is a display tool: it shows what is present and
  does not enforce the length, reference, flag and marker rules a strict client
  applies. This does not indicate a lean-s7 defect, and it means Wireshark cannot be
  used as an oracle for the rejection side of the corpus. The rejections remain
  covered by the Lean theorems, the stdlib oracles and the python-snap7 consumer.

## What this does not cover

Management continuation conversations, block-count/info payload cases, SZL record
contents, typed values and the session/conversation corpora are not dissected here
(the dissector needs a request context for some, and several are not wire-level). The
earlier addressing check in `integration/addressing_conformance.py` and
[its report](addressing-evidence-2026-09-09.md) is separate and unchanged.
