# Corpus consumer: conversation, management-continuation and operations arrays — 2026-10-08

`integration/python_snap7_consumer.py` now maps every array of the conformance corpus
instead of only 467 cases: 580 cases, with a reviewed baseline for python-snap7 3.0.0
and 3.2.1. The 467 earlier classifications are unchanged; this adds 113 cases. As
before this is differential evidence, not a verdict on either side.

| Array | Cases | 3.2.1 result | What was compared |
| --- | ---: | --- | --- |
| `s7/address_cases` | 5 | 5 agree | `build_read_request` bytes for DB, counter and timer starts (counters and timers use the `COUNTER`/`TIMER` word length and an index start) |
| `s7/chunk_cases` | 1 | 1 agree | `_read_chunk_count` at PDU 480: 231, 231, 38 elements at byte starts 0, 462, 924 |
| `s7/userdata_conversation_cases` | 6 | 4 agree, 2 gap | a fragment loop around `parse_response`, `validate_pdu_reference` and `check_userdata_response` (python-snap7 has no assembler) |
| `management/continuation_cases` | 16 | 8 agree, 8 disagree | the same loop, plus `build_userdata_followup_request` against the corpus follow-up bytes |
| `operations/single_userdata_cases` | 8 | 2 agree, 6 disagree | `check_userdata_response` on single USER_DATA replies |
| `operations/string_read_cases` | 12 | 6 agree, 6 gap | `get_string`/`get_wstring` on the body; capacity-consistency cases are client state |
| `operations/write_progress_cases`, `retry_policy_cases`, `conversations`, `sessions` | 65 | gap | python-snap7 has no counterpart API |

The gap rows are recorded as such rather than skipped, so a future python-snap7 API
for them shows up as a baseline change.

## Leads (not filed; each needs independent evidence)

1. **Follow-up request layout (8 cases).** The corpus follow-up carries an 8-byte
   parameter block `12 08 11 4x 0y <seq> 00 00` and a data section of `0a 00 00 00`;
   python-snap7's `build_userdata_followup_request` sends a 4-byte block
   (`12 04 11 4x 0y <seq>`). Which form real controllers require is not established
   here; check against the real-capture continuation requests before calling either side
   wrong.
2. **Group/subfunction identity (4 cases, `fragments-*-identity`).** A fragment whose
   group or subfunction changes mid-conversation is not rejected by the loop python-snap7
   supports.
3. **Single responses with the continuation flag set (6 cases).** An "incomplete"
   single-response reply (flag 1) and an invalid continuation discriminator (flag 2) are
   accepted by `check_userdata_response`. This matches the hardening leads already in
   [the 3.2.1 report](python-snap7-3.2.1-2026-10-07.md).

## Limits

The conversation loop is this script's model of what a python-snap7 client would do,
not a python-snap7 function, so those rows say more about the missing assembler than
about its codecs. The assembly byte limit and the "fragment after completion" rejection
are corpus policies python-snap7 does not express, and are recorded as gaps.
