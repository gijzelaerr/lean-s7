# Replay of real S7-300 captures — 2026-10-07

`python integration/real_captures.py` replays five public captures of a **real
Siemens S7-300** (PLC 192.168.1.40, talking to an engineering tool or libnodave)
through the Lean codecs. The captures are Wireshark's published S7comm samples, listed
on the [sample captures page](https://wiki.wireshark.org/SampleCaptures#s7comm-s7-communication).
They are downloaded on demand into `.lake/captures` and pinned by SHA-256; they are not
stored in this repository, and the check is optional (it needs network access once and
`lake build lean-s7-decode`).

This is independent wire evidence from a real controller for the **exact conversations in
those files**. It does not identify the CPU model or firmware, and it does not qualify
any controller family: gate H1 stays open. What the captures show is recorded below, and
nothing more is claimed.

| Capture (SHA-256 prefix) | S7 PDUs | Content |
| --- | ---: | --- |
| `s7comm_reading_setting_plc_time` (`d74c1eca`) | 26 | SZL reads, read clock (5x), set clock |
| `s7comm_reading_plc_status` (`e71f81b4`) | 144 | SZL reads, CPU state, one clock read |
| `s7comm_program_blocklist_onlineview` (`b2e70143`) | 70 | block counts, block lists, block-info requests (incl. PLC error replies) |
| `s7comm_downloading_block_db1` (`48725bd1`) | 48 | request download, three PLC-driven download-block exchanges, download ended, insert block |
| `s7comm_varservice_libnodavedemo` (`a1ff275c`) | 16 | single-item variable reads and writes |

## Method

The harness parses the pcap itself (Ethernet, IPv4, TCP, TPKT, COTP with end-of-TSDU
reassembly), so no `tshark` is needed; as a cross-check (`--tshark`) its S7 PDU count
equals Wireshark's `s7comm` frame count for every capture (26, 144, 70, 48, 16). Each PDU
then goes through the Lean decoders and encoders via `lean-s7-decode`:

- every PLC USER_DATA response is decoded (envelope; block-count, list and info
  payloads; clock), and PLC error replies (non-zero error code) must be rejected;
- the ten-byte clock payload is compared with an independent BCD decoding in the harness;
- every captured client request the library can build is re-encoded with the captured PDU
  reference and compared byte for byte: read clock, list blocks, list blocks of type,
  block info, read SZL and continuation, single-item reads, request download, download
  fragment and download-ended replies, insert block;
- the PLC-sent download service jobs (`0x1b`, `0x1c`) must pass `validateDownloadServiceRequest`;
- single-item variable-read responses must decode to the requested size.

## Result

**lean-s7: 295 of 295 checks agree** (28, 141, 76, 47 and 3 per capture). No Lean
decoder rejected a genuine PLC reply and every request the library builds is
byte-identical to the real tool's, with one documented exception below.

Facts the real device establishes:

1. **The clock reply is ten data bytes.** For example `ff 09 00 0a | 00 19 14 08 20 11 59 43 91 24`
   is 2014-08-20 11:59:43, reserved byte, century byte `0x19`, millisecond digits and
   weekday in the last two bytes. The Lean clock decoder accepts all six real replies.
2. **The weekday nibble is Sunday = 1.** The reply above carries `4` for a Wednesday
   (2014-08-20 is ISO weekday 3).
3. **A set-clock acknowledgement is return code `0x0a` with no data and error 0.** Lean
   accepts it.
4. **PLC error replies are visible and rejected.** Three block-info requests (frames 44
   and 78 of the block-list capture, 38 of the download capture) return error `0xd209`,
   and one SZL request returns `0xd402`; Lean rejects all four, which the harness
   requires.
5. **PLC-driven download matches the Lean model exactly:** the request-download job, the
   three `0x1b` fragment exchanges (222, 222 and 56 bytes, continuation flag `1`, `1`, `0`),
   the `0x1c` end exchange and the `_INSE` job are byte-identical to the Lean encoders'
   output, and the PLC's service jobs validate. The fragment data is `length, 0x00fb, payload`.
   This is download evidence only; the captures contain no block upload (issue #24).
6. **Block-info request, file-system letter.** The engineering tool's request is
   `'0' type 'NNNNN' 'B'`; Lean and native Snap7 end it with `'A'`. The layout is
   otherwise identical (prefix, type, five digits, letter). Wireshark's S7comm
   dissector names the letter the file system (`A` active, `B` active and passive,
   `P` passive). Lean's choice `A` matches native Snap7's constant and was not
   observed against this PLC; both letters are therefore recorded as a difference, not
   as an error.

## python-snap7 3.2.1 on the same real bytes

Run when python-snap7 is installed (notes only; they do not fail the harness):

- All six real clock replies are rejected ("Clock response must contain exactly eight
  bytes"), which confirms [python-snap7 #925](https://github.com/gijzelaerr/python-snap7/issues/925) against a real PLC.
- The real set-clock acknowledgement (return code `0x0a`, no data) is rejected as
  "USERDATA request failed: Object does not exist (0x0a)", although the PLC reported
  success.
- Its block-info request `0AA00001` differs from the real tool's `0A00001B`, which
  confirms the field-order bug in [#927](https://github.com/gijzelaerr/python-snap7/issues/927) (the letter comes after the number).
- Its read-SZL request differs from the real tool's on every SZL read (all 63 in the
  status capture): the data header is `0a 00 00 04 <id> <index>` where the real tool
  sends `ff 09 00 04 <id> <index>` (return code `0xff`, octet-string transport size). Its
  follow-up request for further SZL fragments uses an eight-byte parameter block with
  method `0x11` (`00 01 12 04 11 44 01 <seq>`), where the real tool sends twelve bytes with
  method `0x12` (`00 01 12 08 12 44 01 <seq> 00 00 00 00`), which the Lean encoder
  reproduces exactly. Whether a PLC tolerates python-snap7's variants was not tested here;
  this records only that they differ from the real tool.
- The clock read and list-blocks requests, the block-count reply and the other
  requests/replies it can parse match the real traffic.

The weekday encoding of [#924](https://github.com/gijzelaerr/python-snap7/issues/924) is
confirmed by fact 2 above: a real PLC labels Wednesday 4.

## Limits

Five captures from one S7-300 in 2014 show what that PLC did in those sessions. They do
not show behavior of other CPUs, S7-1200/1500 controllers, firmware versions, password
protected sessions, uploads, or write-heavy workloads, and the captured client
(an engineering tool and libnodave) is not lean-s7. Redistribution terms of the
captures are not stated on the sample page, which is why they are fetched rather than
committed.
