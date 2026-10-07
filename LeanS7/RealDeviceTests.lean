import LeanS7.Client

/-! Regression vectors taken from public Wireshark captures of a real Siemens S7-300
(`s7comm_reading_setting_plc_time`, `s7comm_reading_plc_status` and
`s7comm_downloading_block_db1`; see `reports/real-s7-300-captures-2026-10-07.md` and
`integration/real_captures.py`). Each string is the S7 PDU exactly as captured. They
show what that PLC and engineering tool exchanged in those sessions; they do not
qualify any controller family or firmware. -/

namespace LeanS7.RealDeviceTests

open LeanS7

private def readClockRequest : String := "3207000007000008000400011204114701000a000000"
private def clockReply : String := "320700000700000c000e000112081287010100000000ff09000a00191408201159439124"
private def setClockAck : String := "320700000c00000c00040001120812870201000000000a000000"
private def szlRequest : String := "320700000300000800080001120411440100ff09000401320004"
private def szlReply : String := "320700000300000c0034000112081284010100000000ff090030013200040028000100040001000000010002000000005656bc04a3d58401d6b202000000000000000000000000000000"
private def szlRefused : String := "320700000c00000c000400011208128401010000d4020a000000"
private def downloadRequest : String := "320100000e00002000001a00010000000000095f30413030303031500d31303030353030303030343030"
private def downloadJob : String := "320100000100001200001b00000000000000095f3041303030303150"
private def fragmentReply : String := "320300000100000200e200001b0100de00fb70700101050a0001000001f400000000029147602bb5029147602bb5001c000000000190000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"
private def downloadEnded : String := "3203000007000001000000001c"
private def insertBlock : String := "320100000f00001a000028000000000000fd000a01003041303030303150055f494e5345"

private def require (value : Bool) (label : String) : IO Unit :=
  unless value do throw <| IO.userError s!"real device vectors: {label}"

private def hexValue (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10

private def hex (text : String) : ByteArray :=
  let rec go : List Char -> ByteArray -> ByteArray
    | high :: low :: rest, acc => go rest (acc.push (UInt8.ofNat (hexValue high * 16 + hexValue low)))
    | _, acc => acc
  go text.toList ByteArray.empty

private def sameBytes (result : Except S7.EncodeError ByteArray) (expected : String) : Bool :=
  match result with
  | .ok actual => actual == hex expected
  | .error _ => false

def run : IO Unit := do
  -- Requests the library builds are byte-identical to the real tool's.
  require (sameBytes (S7.encodeReadClock 0x0700) readClockRequest) "read clock request"
  require (sameBytes (S7.encodeReadSzl 0x0300 0x0132 4) szlRequest) "read SZL request"
  require (sameBytes (S7.encodeRequestDownload 0x0e00 .dataBlock 1 500 400) downloadRequest)
    "request download"
  require (sameBytes (S7.encodeDownloadEndedResponse 0x0700) downloadEnded) "download ended reply"
  require (sameBytes (S7.encodeInsertBlock 0x0f00 .dataBlock 1) insertBlock) "insert block"
  let fragment := hex fragmentReply
  -- ACK_DATA header (12) + two parameter bytes + length (2) + marker (2), then the payload.
  require (sameBytes (S7.encodeDownloadFragmentResponse 0x0100 false (fragment.extract 18 fragment.size))
    fragmentReply) "download fragment reply"
  -- The PLC's ten-byte clock reply decodes; Wednesday is weekday 4 (Sunday = 1).
  match S7.decodeUserDataResponse 0x0700 7 1 (hex clockReply) with
  | .error _ => throw <| IO.userError "real device vectors: clock reply rejected"
  | .ok response =>
    require (response.payload.size == 10) "clock payload is ten bytes"
    match S7.decodePlcDateTime response.payload with
    | .error _ => throw <| IO.userError "real device vectors: clock payload rejected"
    | .ok time =>
      require (time.year == 2014 && time.month == 8 && time.day == 20 && time.hour == 11 &&
        time.minute == 59 && time.second == 43 && time.millisecond == 912 && time.weekday == 4)
        "clock fields"
  -- A set-clock acknowledgement is return code 0x0a with no data.
  match S7.decodeUserDataResponse 0x0c00 7 2 (hex setClockAck) with
  | .ok response => require response.payload.isEmpty "set-clock acknowledgement carries no data"
  | .error _ => throw <| IO.userError "real device vectors: set-clock acknowledgement rejected"
  -- A genuine SZL reply is accepted; the PLC's error reply (0xd402) is rejected.
  match S7.decodeUserDataResponse 0x0300 4 1 (hex szlReply) with
  | .ok response =>
    match S7.decodeSzlFirst response with
    | .ok (id, index, rest) =>
      require (id == 0x0132 && index == 4) "SZL identity"
      require (rest.size == 44) "SZL fragment size"
      match S7.decodeSzl id index rest with
      | .ok szl =>
        let header := szl.recordLength == 40 && szl.recordCount == 1 && szl.data.size == 40
        require header "SZL record header"
      | .error _ => throw <| IO.userError "real device vectors: SZL did not decode"
    | .error _ => throw <| IO.userError "real device vectors: SZL first fragment rejected"
  | .error _ => throw <| IO.userError "real device vectors: SZL reply rejected"
  match S7.decodeUserDataResponse 0x0c00 4 1 (hex szlRefused) with
  | .ok _ => throw <| IO.userError "real device vectors: PLC error reply accepted"
  | .error _ => pure ()
  -- The PLC-sent download service job validates for data block 1.
  match S7.decodeJobPdu (hex downloadJob) with
  | .ok job =>
    match S7.validateDownloadServiceRequest job S7.downloadFunction .dataBlock 1 with
    | .ok _ => pure ()
    | .error _ => throw <| IO.userError "real device vectors: download service job rejected"
  | .error _ => throw <| IO.userError "real device vectors: download job did not decode"
  IO.println "real S7-300 device vectors passed"

end LeanS7.RealDeviceTests
