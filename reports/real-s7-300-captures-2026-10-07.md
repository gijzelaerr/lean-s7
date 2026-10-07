# Replay of real Siemens controller captures — 2026-10-07

`python integration/real_captures.py` replays six public captures of real Siemens
controllers through the Lean codecs: five of an **S7-300** (PLC 192.168.1.40, talking to
an engineering tool or libnodave; Wireshark's published S7comm samples, listed on the
[sample captures page](https://wiki.wireshark.org/SampleCaptures#s7comm-s7-communication))
and one test trace of the CISA [icsnpp-s7comm](https://github.com/cisagov/icsnpp-s7comm)
parser (BSD-3-Clause; a Snap7-based client against a device at `:102`, commit
`58d46fac`), which contains four complete block uploads. The captures are downloaded on
demand into `.lake/captures` and pinned by SHA-256; they are not stored in this
repository, and the check is optional (it needs network access once and
`lake build lean-s7-decode`). The controller behind the CISA trace is not identified
in the repository, so it is described only as "a device".

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
| `icsnpp_snap7_upload` (`2b91f6a8`) | 64 | four complete uploads of system data block 0, a refused OB 0 upload, block counts, clock, CPU stop, copy RAM to ROM, compress and cold start |

## Method

The harness parses the pcap itself (Ethernet, IPv4, TCP, TPKT, COTP with end-of-TSDU
reassembly), so no `tshark` is needed; as a cross-check (`--tshark`) its S7 PDU count
equals Wireshark's `s7comm` frame count for every capture (26, 144, 70, 48, 16, 64). Each PDU
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

**lean-s7: 351 of 351 checks agree** (28, 141, 76, 48, 3 and 55 per capture). No Lean
decoder rejected a genuine PLC reply and every request the library builds is
byte-identical to the real tool's, with one documented exception below.

Facts the real device establishes:

1. **The clock reply is ten data bytes.** For example `ff 09 00 0a | 00 19 14 08 20 11 59 43 91 24`
   is 2014-08-20 11:59:43, reserved byte, century byte `0x19`, millisecond digits and
   weekday in the last two bytes. The Lean clock decoder accepts all seven real replies.
2. **The weekday nibble is Sunday = 1.** The reply above carries `4` for a Wednesday
   (2014-08-20 is ISO weekday 3).
3. **A set-clock acknowledgement is return code `0x0a` with no data and error 0.** Lean
   accepts it.
4. **PLC error replies are visible and rejected.** Four block-info requests (frames 44
   and 78 of the block-list capture, 38 of the download capture, 24 of the upload trace)
   return error `0xd209`, one SZL request returns `0xd402` and a start-upload of OB 0
   returns `0xd20c`; Lean rejects all six, which the harness requires.
5. **PLC-driven download matches the Lean model exactly:** the request-download job, the
   three `0x1b` fragment exchanges (222, 222 and 56 bytes, continuation flag `1`, `1`, `0`),
   the `0x1c` end exchange and the `_INSE` job are byte-identical to the Lean encoders'
   output, and the PLC's service jobs validate. The fragment data is `length, 0x00fb, payload`.
   This is download evidence only; the captures contain no block upload (issue #24).
6. **A real upload matches the Lean model.** The CISA trace performs four complete uploads
   of system data block 0 (`_0B00000A`): the start-upload request is byte-identical to
   `encodeStartUpload`; the reply carries upload id 7 and the load size as ASCII digits
   (`0000216`), which `decodeStartUpload` accepts with size 216; the upload reply is
   `1e 00` with data `00d8 00fb` plus 216 bytes in a single, last fragment, which
   `decodeUploadFragment` accepts; the end-upload job and its empty reply decode. The PLC
   also refuses a start-upload of OB 0 with an acknowledgement carrying error `0xd20c`,
   which Lean rejects. This is single-fragment, full-block evidence for one device: no
   multi-fragment upload, no PDU-size variation and no MC7-versus-full-upload comparison
   (issue #24 stays open for those).
7. **CPU-control jobs match.** The trace's stop (`0x29`), cold start, copy-RAM-to-ROM
   (`_MODU`) and compress (`_GARB`) jobs are byte-identical to `encodePlcStop`,
   `encodePlcColdStart`, `encodeCopyRamToRom` and `encodeCompress`, and the PLC's
   acknowledgements decode. No CPU state change was confirmed from the captures.
8. **Block-info request, file-system letter.** The engineering tool's request is
   `'0' type 'NNNNN' 'B'`; Lean and native Snap7 end it with `'A'`. The layout is
   otherwise identical (prefix, type, five digits, letter). Wireshark's S7comm
   dissector names the letter the file system (`A` active, `B` active and passive,
   `P` passive). Lean's choice `A` matches native Snap7's constant and was not
   observed against this PLC; both letters are therefore recorded as a difference, not
   as an error.

## python-snap7 3.2.1 on the same real bytes

Run when python-snap7 is installed (notes only; they do not fail the harness):

- All seven real clock replies are rejected ("Clock response must contain exactly eight
  bytes"), which confirms [python-snap7 #925](https://github.com/gijzelaerr/python-snap7/issues/925) against a real PLC.
- Both real set-clock acknowledgements (return code `0x0a`, no data) are rejected as
  "USERDATA request failed: Object does not exist (0x0a)", although the PLC reported
  success.
- Its block-info request `0AA00001` differs from the real tool's `0A00001B`, which
  confirms the field-order bug in [#927](https://github.com/gijzelaerr/python-snap7/issues/927) (the letter comes after the number).
- Its read-SZL request differs from the real tool's on every SZL read (all 93 across the
  captures, 66 of them in the status capture): the data header is `0a 00 00 04 <id> <index>` where the real tool
  sends `ff 09 00 04 <id> <index>` (return code `0xff`, octet-string transport size). Its
  follow-up request for further SZL fragments (all 5 in the captures) uses an eight-byte parameter block with
  method `0x11` (`00 01 12 04 11 44 01 <seq>`), where the real tool sends twelve bytes with
  method `0x12` (`00 01 12 08 12 44 01 <seq> 00 00 00 00`), which the Lean encoder
  reproduces exactly. Whether a PLC tolerates python-snap7's variants was not tested here;
  this records only that they differ from the real tool.
- Its upload path matches the real device: the start-upload, upload and end-upload
  requests are byte-identical and it parses the real replies (upload id 7, length 216, a
  216-byte last fragment, the empty end-upload reply).
- Its compress and copy-RAM-to-ROM requests use the PI service name `_MSZL` where the real
  jobs use `_GARB` and `_MODU` (native Snap7's `TReqFunCompress`/`TReqFunCopyRamToRom`
  comments name `_GARB` and `_MODU` too); its CPU stop and cold start match.
- The clock read and list-blocks requests, the block-count reply and the other
  requests/replies it can parse match the real traffic.

The weekday encoding of [#924](https://github.com/gijzelaerr/python-snap7/issues/924) is
confirmed by fact 2 above: a real PLC labels Wednesday 4.

## Always-on regression vectors

Eighteen of the captured PDUs (read clock request and reply, set-clock acknowledgement, a
SZL request, reply and error reply, the request-download job, a PLC download service job,
a download fragment reply, the download-ended reply and the insert-block job) are also
embedded as exact hex in `LeanS7/RealDeviceTests.lean`, which `lake exe lean-s7-tests`
runs without network access. They pin the facts above: byte-identical requests, the
ten-byte clock with weekday 4 for a Wednesday, the empty set-clock acknowledgement, a
genuine SZL reply and a PLC error reply that must be rejected.

## Limits

Five captures from one S7-300 in 2014 and one trace of an unidentified device show what
those controllers did in those sessions. They do not show behavior of other CPUs,
S7-1200/1500 controllers, firmware versions, password-protected sessions, multi-fragment
uploads, or write-heavy workloads, and the captured clients (an engineering tool,
libnodave and a Snap7-based tool) are not lean-s7. The five Wireshark samples carry no
stated redistribution terms, and the CISA trace is BSD-3-Clause; all are fetched and
hash-checked rather than committed.
