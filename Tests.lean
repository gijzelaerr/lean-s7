import LeanS7

open LeanS7

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def isOkEq [BEq α] (result : Except ε α) (expected : α) : Bool :=
  match result with
  | .ok value => value == expected
  | .error _ => false

def testBinary : IO Unit := do
  let cursor : Cursor := { data := bytes #[0x12, 0x34, 0x56] }
  match cursor.readUInt16BE with
  | .ok (value, cursor) =>
      check (value == 0x1234) "big-endian UInt16 decoding failed"
      check (cursor.remaining == 1) "cursor did not advance"
  | .error err => throw <| IO.userError s!"unexpected binary decode error: {repr err}"

def testTPKTRoundTrip : IO Unit := do
  let frame : TPKT.Frame := { payload := bytes #[2, 0xf0, 0x80, 0xde, 0xad] }
  match TPKT.encode frame with
  | .error err => throw <| IO.userError s!"unexpected TPKT encode error: {repr err}"
  | .ok encoded =>
      check (encoded == bytes #[3, 0, 0, 9, 2, 0xf0, 0x80, 0xde, 0xad]) "unexpected TPKT wire encoding"
      check (match TPKT.decode encoded with | .ok decoded => decoded == frame | .error _ => false)
        "TPKT round trip failed"

def testTPKTRejectsMalformedFrames : IO Unit := do
  check (match TPKT.decode (bytes #[4, 0, 0, 4]) with | .error _ => true | _ => false)
    "invalid TPKT version was accepted"
  check (match TPKT.decode (bytes #[3, 0, 0, 8, 0xaa]) with | .error _ => true | _ => false)
    "invalid TPKT length was accepted"
  check (match TPKT.decode (bytes #[3, 0, 0, 6, 0xaa, 0xbb]) with
    | .error _ => true | _ => false) "undersized TPKT frame was accepted"

def testTPKTIgnoresReservedInput : IO Unit := do
  let expected : TPKT.Frame := { payload := bytes #[2, 0xf0, 0x80] }
  check (isOkEq (TPKT.decode (bytes #[3, 0xff, 0, 7, 2, 0xf0, 0x80])) expected)
    "TPKT reserved byte was not ignored on input"

def testTPKTSizeBoundary : IO Unit := do
  let minimumPayloadSize := TPKT.minFrameSize - TPKT.headerSize
  let minimumFrame : TPKT.Frame := {
    payload := ByteArray.mk (Array.replicate minimumPayloadSize 0xaa)
  }
  match TPKT.encode minimumFrame with
  | .error err => throw <| IO.userError s!"minimum-size TPKT frame was rejected: {repr err}"
  | .ok encoded =>
      check (encoded.size == TPKT.minFrameSize) "minimum-size TPKT frame has the wrong size"
      check (isOkEq (TPKT.decode encoded) minimumFrame) "minimum-size TPKT round trip failed"

  let undersizedFrame : TPKT.Frame := {
    payload := ByteArray.mk (Array.replicate (minimumPayloadSize - 1) 0xaa)
  }
  check (match TPKT.encode undersizedFrame with
    | .error (.frameTooSmall size minimum) =>
        size == TPKT.minFrameSize - 1 && minimum == TPKT.minFrameSize
    | .error _ | .ok _ => false) "undersized TPKT frame was encoded"

  let maximumPayloadSize := TPKT.maxFrameSize - TPKT.headerSize
  let maximumFrame : TPKT.Frame := {
    payload := ByteArray.mk (Array.replicate maximumPayloadSize 0xaa)
  }
  match TPKT.encode maximumFrame with
  | .error err => throw <| IO.userError s!"maximum-size TPKT frame was rejected: {repr err}"
  | .ok encoded =>
      check (encoded.size == TPKT.maxFrameSize) "maximum-size TPKT frame has the wrong size"
      check (isOkEq (TPKT.decode encoded) maximumFrame) "maximum-size TPKT round trip failed"

  let oversizedFrame : TPKT.Frame := {
    payload := ByteArray.mk (Array.replicate (maximumPayloadSize + 1) 0xaa)
  }
  check (match TPKT.encode oversizedFrame with
    | .error (.frameTooLarge size maximum) =>
        size == TPKT.maxFrameSize + 1 && maximum == TPKT.maxFrameSize
    | .error _ | .ok _ => false) "oversized TPKT frame was accepted"

def tpktEncodeErrorName : TPKT.EncodeError → String
  | .frameTooSmall _ _ => "frame-too-small"
  | .frameTooLarge _ _ => "frame-too-large"

def tpktDecodeErrorName : DecodeError → String
  | .unexpectedEnd _ _ _ => "unexpected-end"
  | .invalidField 0 _ => "invalid-version"
  | .invalidField 2 message =>
      if message.startsWith "invalid TPKT length" then
        "length-below-minimum"
      else
        "length-mismatch"
  | .invalidField _ _ | .trailingBytes _ _ => "other-decode-error"

def testTPKTConformanceCorpus : IO Unit := do
  for test in Conformance.TPKT.encodeCases do
    let actual := TPKT.encode { payload := test.payload.materialize }
    let conforms := match test.expected, actual with
      | .accept expected, .ok packet => packet == expected.materialize
      | .reject expected, .error error => tpktEncodeErrorName error == expected
      | _, _ => false
    check conforms s!"TPKT encode conformance case failed: {test.id}"

  for test in Conformance.TPKT.decodeCases do
    let actual := TPKT.decode test.packet.materialize
    let conforms := match test.expected, actual with
      | .accept expected, .ok frame => frame.payload == expected.materialize
      | .reject expected, .error error => tpktDecodeErrorName error == expected
      | _, _ => false
    check conforms s!"TPKT decode conformance case failed: {test.id}"

def testCOTPConnectionRequest : IO Unit := do
  let encoded := COTP.encodeConnectionRequest {}
  let expected := bytes #[
    0x11, 0xe0, 0x00, 0x00, 0x00, 0x01, 0x00,
    0xc1, 0x02, 0x01, 0x00,
    0xc2, 0x02, 0x01, 0x02,
    0xc0, 0x01, 0x0a]
  check (encoded == expected) "unexpected COTP connection request encoding"
  let disconnect := COTP.encodeDisconnectRequest {
    destinationReference := 0x1234
    sourceReference := 0x5678
    reason := 0
  }
  check (disconnect == bytes #[0x06, 0x80, 0x12, 0x34, 0x56, 0x78, 0x00])
    "unexpected COTP disconnect request encoding"

def testCOTPDataRoundTrip : IO Unit := do
  let pdu : COTP.Data := { payload := bytes #[0x32, 0x01, 0x00] }
  let encoded := COTP.encodeData pdu
  check (encoded == bytes #[2, 0xf0, 0x80, 0x32, 0x01, 0x00]) "unexpected COTP data encoding"
  check (match COTP.decodeData encoded with | .ok decoded => decoded == pdu | .error _ => false)
    "COTP data round trip failed"
  let segment : COTP.Data := { payload := bytes #[0x32], endOfTransmission := false }
  check (isOkEq (COTP.decodeData (COTP.encodeData segment)) segment)
    "segmented COTP data round trip failed"
  check (match COTP.decodeData (bytes #[3, 0xf0, 0x80, 0x32]) with
    | .error _ => true | .ok _ => false) "invalid COTP data header length was accepted"
  check (match COTP.decodeData (bytes #[2, 0xf0, 0x81, 0x32]) with
    | .error _ => true | .ok _ => false) "nonzero COTP TPDU number was accepted"

def cotpDecodeErrorName : DecodeError → String
  | .unexpectedEnd _ _ _ => "unexpected-end"
  | .invalidField 0 _ => "invalid-header-length"
  | .invalidField 1 _ => "invalid-tpdu-code"
  | .invalidField 2 _ => "nonzero-tpdu-number"
  | .invalidField _ _ | .trailingBytes _ _ => "other-decode-error"

def testCOTPConformanceCorpus : IO Unit := do
  for test in Conformance.COTP.encodeCases do
    let actual := COTP.encodeData {
      payload := test.payload.materialize
      endOfTransmission := test.endOfTransmission
    }
    check (actual == test.expected.materialize)
      s!"COTP encode conformance case failed: {test.id}"

  for test in Conformance.COTP.decodeCases do
    let actual := COTP.decodeData test.packet.materialize
    let conforms := match test.expected, actual with
      | .accept expected, .ok data =>
          data.payload == expected.payload.materialize &&
            data.endOfTransmission == expected.endOfTransmission
      | .reject expected, .error error => cotpDecodeErrorName error == expected
      | _, _ => false
    check conforms s!"COTP decode conformance case failed: {test.id}"

def testS7SetupCommunication : IO Unit := do
  let expected := bytes #[
    0x32, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x08, 0x00, 0x00,
    0xf0, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01, 0xe0]
  match S7.encodeSetupCommunication 1 with
  | .error err => throw <| IO.userError s!"could not encode S7 handshake: {repr err}"
  | .ok encoded =>
      check (encoded == expected) "unexpected S7 setup-communication encoding"
      check (isOkEq (S7.decodeJob encoded) {
        reference := 1
        parameters := bytes #[0xf0, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01, 0xe0]
      }) "S7 setup-communication job round trip failed"
      let cotp := COTP.encodeData { payload := encoded }
      match TPKT.encode { payload := cotp } with
      | .ok packet => check (packet.size == 25) "unexpected complete handshake packet size"
      | .error err => throw <| IO.userError s!"could not frame S7 handshake: {repr err}"

  let job : S7.Job := {
    reference := 0x1234
    parameters := bytes #[0x04, 0x01]
    data := bytes #[0xaa, 0xbb, 0xcc]
  }
  match S7.encodeJob job with
  | .error err => throw <| IO.userError s!"could not encode generic S7 job: {repr err}"
  | .ok encoded =>
      check (encoded.size == S7.jobHeaderSize + job.parameters.size + job.data.size)
        "generic S7 job encoded length is incorrect"
      check (isOkEq (S7.decodeJob encoded) job) "generic S7 job round trip failed"

  match Protocol.encodeJob job with
  | .error err => throw <| IO.userError s!"could not encode complete S7 packet: {repr err}"
  | .ok packet =>
      check (isOkEq (Protocol.decodeJob packet) job)
        "complete TPKT/COTP/S7 job round trip failed"

  match TPKT.encode {
    payload := COTP.encodeData {
      payload := bytes #[0x32, 0x01, 0, 0, 0, 1, 0, 0, 0, 0]
      endOfTransmission := false
    }
  } with
  | .error err => throw <| IO.userError s!"could not frame segmented S7 test: {repr err}"
  | .ok packet =>
      check (match Protocol.decodeJob packet with | .error _ => true | .ok _ => false)
        "segmented COTP data was accepted as a complete S7 job"

  check (match S7.decodeJob (bytes #[0x31, 0x01, 0, 0, 0, 1, 0, 0, 0, 0]) with
    | .error _ => true | .ok _ => false) "invalid S7 job protocol ID was accepted"
  check (match S7.decodeJob (bytes #[0x32, 0x03, 0, 0, 0, 1, 0, 0, 0, 0]) with
    | .error _ => true | .ok _ => false) "non-job S7 PDU was accepted as a job"
  check (match S7.decodeJob (bytes #[0x32, 0x01, 0, 0, 0, 1, 0, 1, 0, 0]) with
    | .error _ => true | .ok _ => false) "truncated S7 job section was accepted"
  check (match S7.decodeJob (bytes #[0x32, 0x01, 0, 0, 0, 1, 0, 0, 0, 0, 0]) with
    | .error _ => true | .ok _ => false) "trailing S7 job byte was accepted"

def testS7ResponseDecoding : IO Unit := do
  let setupAck := bytes #[
    0x32, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00,
    0xf0, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01, 0xe0]
  match S7.decodeResponse setupAck with
  | .error err => throw <| IO.userError s!"could not decode setup ACK: {repr err}"
  | .ok response =>
      check (match S7.validateResponse response 2 S7.setupCommunicationFunction with
        | .error _ => true | .ok _ => false) "mismatched S7 response reference was accepted"
      check (match S7.validateResponse { response with errorClass := 0x81 }
          1 S7.setupCommunicationFunction with
        | .error _ => true | .ok _ => false) "S7 PLC error status was accepted"
      check (match S7.validateResponse response 1 S7.readFunction with
        | .error _ => true | .ok _ => false) "wrong S7 response function was accepted"
      match S7.decodeSetupCommunication 1 response with
      | .ok setup => check (setup.pduLength == 480) "unexpected negotiated PDU length"
      | .error err => throw <| IO.userError s!"could not decode setup parameters: {repr err}"
  check (match S7.decodeResponse (setupAck.extract 0 15) with | .error _ => true | _ => false)
    "truncated S7 response was accepted"

def testS7DbVectors : IO Unit := do
  let readRange : S7.DbRange := { dbNumber := 1, start := 10, size := 4 }
  match S7.encodeDbRead 2 readRange with
  | .error err => throw <| IO.userError s!"could not encode DB read: {repr err}"
  | .ok request =>
      let expected := bytes #[
        0x32, 0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x0e, 0x00, 0x00,
        0x04, 0x01, 0x12, 0x0a, 0x10, 0x02, 0x00, 0x04, 0x00, 0x01,
        0x84, 0x00, 0x00, 0x50]
      check (request == expected) "unexpected DB read request encoding"
  let readAck := bytes #[
    0x32, 0x03, 0x00, 0x00, 0x00, 0x02, 0x00, 0x02, 0x00, 0x08, 0x00, 0x00,
    0x04, 0x01, 0xff, 0x04, 0x00, 0x20, 0xaa, 0xbb, 0xcc, 0xdd]
  match S7.decodeResponse readAck with
  | .error err => throw <| IO.userError s!"could not decode DB read ACK: {repr err}"
  | .ok response =>
      match S7.decodeDbRead 2 response with
      | .ok payload => check (payload == bytes #[0xaa, 0xbb, 0xcc, 0xdd]) "wrong DB read payload"
      | .error err => throw <| IO.userError s!"could not extract DB read payload: {repr err}"
  let payload := bytes #[0xde, 0xad, 0xbe, 0xef]
  match S7.encodeDbWrite 3 1 16 payload with
  | .error err => throw <| IO.userError s!"could not encode DB write: {repr err}"
  | .ok request =>
      let expected := bytes #[
        0x32, 0x01, 0x00, 0x00, 0x00, 0x03, 0x00, 0x0e, 0x00, 0x08,
        0x05, 0x01, 0x12, 0x0a, 0x10, 0x02, 0x00, 0x04, 0x00, 0x01,
        0x84, 0x00, 0x00, 0x80, 0x00, 0x04, 0x00, 0x20, 0xde, 0xad,
        0xbe, 0xef]
      check (request == expected) "unexpected DB write request encoding"
  let writeAck := bytes #[
    0x32, 0x03, 0x00, 0x00, 0x00, 0x03, 0x00, 0x02, 0x00, 0x01, 0x00, 0x00,
    0x05, 0x01, 0xff]
  match S7.decodeResponse writeAck with
  | .error err => throw <| IO.userError s!"could not decode DB write ACK: {repr err}"
  | .ok response =>
      match S7.decodeDbWrite 3 response with
      | .ok () => pure ()
      | .error err => throw <| IO.userError s!"could not validate DB write ACK: {repr err}"

def testS7AreaVectors : IO Unit := do
  let counterRange : S7.MemoryRange := {
    area := .counters
    dbNumber := 0
    start := 4
    count := 2
  }
  match S7.encodeAreaRead 4 counterRange with
  | .error err => throw <| IO.userError s!"could not encode counter read: {repr err}"
  | .ok request =>
      let expected := bytes #[
        0x32, 0x01, 0x00, 0x00, 0x00, 0x04, 0x00, 0x0e, 0x00, 0x00,
        0x04, 0x01, 0x12, 0x0a, 0x10, 0x1c, 0x00, 0x02, 0x00, 0x00,
        0x1c, 0x00, 0x00, 0x04]
      check (request == expected) "unexpected counter read request encoding"
  let timerPayload := bytes #[0x12, 0x34, 0x56, 0x78]
  let timerRange : S7.MemoryRange := {
    area := .timers
    dbNumber := 0
    start := 4
    count := 2
  }
  match S7.encodeAreaWrite 5 timerRange timerPayload with
  | .error err => throw <| IO.userError s!"could not encode timer write: {repr err}"
  | .ok request =>
      let expected := bytes #[
        0x32, 0x01, 0x00, 0x00, 0x00, 0x05, 0x00, 0x0e, 0x00, 0x08,
        0x05, 0x01, 0x12, 0x0a, 0x10, 0x1d, 0x00, 0x02, 0x00, 0x00,
        0x1d, 0x00, 0x00, 0x04, 0x00, 0x09, 0x00, 0x04, 0x12, 0x34,
        0x56, 0x78]
      check (request == expected) "unexpected timer write request encoding"
  let timerAck := bytes #[
    0x32, 0x03, 0x00, 0x00, 0x00, 0x05, 0x00, 0x02, 0x00, 0x08, 0x00, 0x00,
    0x04, 0x01, 0xff, 0x09, 0x00, 0x04, 0x12, 0x34, 0x56, 0x78]
  match S7.decodeResponse timerAck with
  | .error err => throw <| IO.userError s!"could not decode timer ACK: {repr err}"
  | .ok response =>
      match S7.decodeAreaRead 5 .timers 4 response with
      | .ok payload => check (payload == timerPayload) "wrong timer read payload"
      | .error err => throw <| IO.userError s!"could not extract timer payload: {repr err}"
  check (match S7.encodeAreaRead 6 {
      area := .markers, dbNumber := 1, start := 0, count := 1
    } with | .error (.invalidDbNumber 1) => true | _ => false)
    "non-DB area accepted a DB number"
  check (match S7.encodeAreaWrite 6 timerRange (bytes #[0]) with
    | .error (.invalidPayloadSize 1 4) => true | _ => false)
    "mis-sized timer payload was accepted"
  check (match S7.encodeAreaRead 6 { counterRange with start := 3 } with
    | .error (.misalignedAddress 3 2) => true | _ => false)
    "misaligned counter address was accepted"
  check (match S7.encodeAreaRead 6 {
      area := .dataBlocks, dbNumber := 1, start := 0x200000, count := 1
    } with | .error (.addressTooLarge _) => true | _ => false)
    "out-of-range byte address was accepted"

def testValues : IO Unit := do
  let numeric := bytes #[
    0x80, 0x12, 0x34, 0x89, 0xab, 0xcd, 0xef,
    0x01, 0x23, 0x45, 0x67, 0x89, 0xab, 0xcd, 0xef]
  check (isOkEq (Value.getUInt8 numeric 0) 0x80) "UInt8 decoding failed"
  check (isOkEq (Value.getInt8 numeric 0) (UInt8.toInt8 0x80)) "Int8 decoding failed"
  check (isOkEq (Value.getUInt16 numeric 1) 0x1234) "UInt16 decoding failed"
  check (isOkEq (Value.getInt16 (Value.putInt16 (UInt16.toInt16 0x8123))) (UInt16.toInt16 0x8123))
    "Int16 round trip failed"
  check (isOkEq (Value.getUInt32 numeric 3) 0x89abcdef) "UInt32 decoding failed"
  check (isOkEq (Value.getInt32 (Value.putInt32 (UInt32.toInt32 0x89abcdef)))
    (UInt32.toInt32 0x89abcdef)) "Int32 round trip failed"
  check (isOkEq (Value.getUInt64 numeric 7) 0x0123456789abcdef) "UInt64 decoding failed"
  check (isOkEq (Value.getInt64 (Value.putInt64 (UInt64.toInt64 0x8123456789abcdef)))
    (UInt64.toInt64 0x8123456789abcdef)) "Int64 round trip failed"
  let real := Float32.ofBits 0x41480000
  match Value.getReal (Value.putReal real) with
  | .ok decoded => check (decoded.toBits == real.toBits) "REAL round trip failed"
  | .error err => throw <| IO.userError s!"REAL decoding failed: {repr err}"
  let lreal := Float.ofBits 0x400921fb54442d18
  match Value.getLReal (Value.putLReal lreal) with
  | .ok decoded => check (decoded.toBits == lreal.toBits) "LREAL round trip failed"
  | .error err => throw <| IO.userError s!"LREAL decoding failed: {repr err}"
  check (isOkEq (Value.setBit 0xa0 0 true) 0xa1) "setting a bit changed neighboring bits"
  check (isOkEq (Value.setBit 0xa1 5 false) 0x81) "clearing a bit changed neighboring bits"
  check (isOkEq (Value.getBit (bytes #[0x81]) 0 7) true) "bit decoding failed"
  check (match Value.getBit (bytes #[0]) 0 8 with
    | .error (.invalidBitIndex 8) => true | _ => false) "invalid bit index was accepted"
  match Value.encodeString 8 "S7 café" with
  | .error err => throw <| IO.userError s!"STRING encoding failed: {repr err}"
  | .ok encoded =>
      check (encoded.size == 10) "STRING field has the wrong size"
      check (isOkEq (Value.decodeString encoded) "S7 café") "STRING round trip failed"
  check (match Value.encodeString 4 "hello" with
    | .error (.valueTooLong 5 4) => true | _ => false) "oversized STRING was accepted"
  check (match Value.decodeString (bytes #[4, 5, 0, 0, 0, 0]) with
    | .error (.invalidStringHeader 5 4) => true | _ => false) "invalid STRING length was accepted"
  check (match Value.encodeString 4 "λ" with
    | .error (.invalidCharacter _) => true | _ => false) "non-Latin-1 STRING character was accepted"
  match Value.encodeWString 8 "PLC 🚀" with
  | .error err => throw <| IO.userError s!"WSTRING encoding failed: {repr err}"
  | .ok encoded =>
      check (encoded.size == 20) "WSTRING field has the wrong size"
      check (isOkEq (Value.decodeWString encoded) "PLC 🚀") "WSTRING round trip failed"
  check (match Value.decodeWString (bytes #[0, 1, 0, 1, 0xd8, 0x00]) with
    | .error (.invalidUtf16 0 _) => true | _ => false) "invalid UTF-16 was accepted"

def testS7MultiVectors : IO Unit := do
  let dbRange : S7.MemoryRange :=
    { area := .dataBlocks, dbNumber := 1, start := 0, count := 3 }
  let markerRange : S7.MemoryRange :=
    { area := .markers, dbNumber := 0, start := 4, count := 2 }
  let ranges := #[dbRange, markerRange]
  match S7.encodeAreaReadMany 7 ranges with
  | .error err => throw <| IO.userError s!"could not encode multi-read: {repr err}"
  | .ok request =>
      let expected := bytes #[
        0x32, 0x01, 0x00, 0x00, 0x00, 0x07, 0x00, 0x1a, 0x00, 0x00,
        0x04, 0x02,
        0x12, 0x0a, 0x10, 0x02, 0x00, 0x03, 0x00, 0x01, 0x84, 0x00, 0x00, 0x00,
        0x12, 0x0a, 0x10, 0x02, 0x00, 0x02, 0x00, 0x00, 0x83, 0x00, 0x00, 0x20]
      check (request == expected) "unexpected multi-read request encoding"
  let readAck := bytes #[
    0x32, 0x03, 0x00, 0x00, 0x00, 0x07, 0x00, 0x02, 0x00, 0x0e, 0x00, 0x00,
    0x04, 0x02,
    0xff, 0x04, 0x00, 0x18, 0xaa, 0xbb, 0xcc, 0x00,
    0xff, 0x04, 0x00, 0x10, 0x11, 0x22]
  match S7.decodeResponse readAck with
  | .error err => throw <| IO.userError s!"could not decode multi-read ACK: {repr err}"
  | .ok response =>
      let expected := #[
        S7.ReadItemResult.success (bytes #[0xaa, 0xbb, 0xcc]),
        S7.ReadItemResult.success (bytes #[0x11, 0x22])]
      check (isOkEq (S7.decodeAreaReadMany 7 ranges response) expected)
        "multi-read results or fill-byte handling were incorrect"
  let partialReadAck := bytes #[
    0x32, 0x03, 0x00, 0x00, 0x00, 0x07, 0x00, 0x02, 0x00, 0x0c, 0x00, 0x00,
    0x04, 0x02,
    0xff, 0x04, 0x00, 0x18, 0xaa, 0xbb, 0xcc, 0x00,
    0x05, 0x00, 0x00, 0x00]
  match S7.decodeResponse partialReadAck with
  | .error err => throw <| IO.userError s!"could not decode partial multi-read ACK: {repr err}"
  | .ok response =>
      let expected := #[
        S7.ReadItemResult.success (bytes #[0xaa, 0xbb, 0xcc]),
        S7.ReadItemResult.failure 0x05]
      check (isOkEq (S7.decodeAreaReadMany 7 ranges response) expected)
        "multi-read item failure was not preserved"
  let writes : Array S7.WriteItem := #[
    { range := dbRange, payload := bytes #[0xaa, 0xbb, 0xcc] },
    { range := markerRange, payload := bytes #[0x11, 0x22] }
  ]
  match S7.encodeAreaWriteMany 8 writes with
  | .error err => throw <| IO.userError s!"could not encode multi-write: {repr err}"
  | .ok request =>
      let expected := bytes #[
        0x32, 0x01, 0x00, 0x00, 0x00, 0x08, 0x00, 0x1a, 0x00, 0x0e,
        0x05, 0x02,
        0x12, 0x0a, 0x10, 0x02, 0x00, 0x03, 0x00, 0x01, 0x84, 0x00, 0x00, 0x00,
        0x12, 0x0a, 0x10, 0x02, 0x00, 0x02, 0x00, 0x00, 0x83, 0x00, 0x00, 0x20,
        0x00, 0x04, 0x00, 0x18, 0xaa, 0xbb, 0xcc, 0x00,
        0x00, 0x04, 0x00, 0x10, 0x11, 0x22]
      check (request == expected) "unexpected multi-write request encoding"
  let writeAck := bytes #[
    0x32, 0x03, 0x00, 0x00, 0x00, 0x08, 0x00, 0x02, 0x00, 0x02, 0x00, 0x00,
    0x05, 0x02, 0xff, 0x05]
  match S7.decodeResponse writeAck with
  | .error err => throw <| IO.userError s!"could not decode multi-write ACK: {repr err}"
  | .ok response =>
      let expected := #[S7.WriteItemResult.success, S7.WriteItemResult.failure 0x05]
      check (isOkEq (S7.decodeAreaWriteMany 8 2 response) expected)
        "multi-write item results were incorrect"
  let tooMany := Array.replicate 21 dbRange
  check (match S7.encodeAreaReadMany 9 tooMany with
    | .error (.invalidSize 21) => true | _ => false) "more than 20 read items were accepted"

def testS7ManagementVectors : IO Unit := do
  let readSzl := bytes #[
    0x32, 0x07, 0, 0, 0, 9, 0, 8, 0, 8,
    0, 1, 0x12, 4, 0x11, 0x44, 1, 0,
    0xff, 9, 0, 4, 0x04, 0x24, 0, 0]
  check (isOkEq (S7.encodeReadSzl 9 0x0424 0) readSzl)
    "unexpected read-SZL request encoding"
  let responsePdu := bytes #[
    0x32, 0x07, 0, 0, 0, 9, 0, 12, 0, 16,
    0, 1, 0x12, 8, 0x12, 0x84, 1, 3, 0x22, 1, 0, 0,
    0xff, 9, 0, 12, 0x04, 0x24, 0, 0, 0, 4, 0, 1, 0, 0, 0, 8]
  match S7.decodeUserDataResponse 9 S7.szlGroup S7.readSzlSubfunction responsePdu with
  | .error err => throw <| IO.userError s!"could not decode USER_DATA response: {repr err}"
  | .ok response =>
      check response.hasMoreData "fragment continuation flag was lost"
      check (response.sequence == 3 && response.dataUnitReference == 0x22)
        "fragment sequence metadata was decoded incorrectly"
      let (id, index, payload) ← match S7.decodeSzlFirst response with
        | .ok value => pure value
        | .error err => throw <| IO.userError s!"could not decode first SZL fragment: {repr err}"
      check (id == 0x0424 && index == 0) "SZL identity was decoded incorrectly"
      match S7.decodeSzl id index payload with
      | .error err => throw <| IO.userError s!"could not decode SZL records: {repr err}"
      | .ok szl =>
          check (szl.recordLength == 4 && szl.recordCount == 1)
            "SZL record framing was decoded incorrectly"
          check (isOkEq (S7.parseCpuState szl) .running) "CPU RUN state was not decoded"
  let clock : S7.PlcDateTime := {
    year := 2026, month := 9, day := 7, hour := 14, minute := 5, second := 59,
    millisecond := 123, weekday := 1
  }
  match S7.encodePlcDateTime clock with
  | .error err => throw <| IO.userError s!"could not encode PLC clock: {repr err}"
  | .ok encoded =>
      check (encoded == bytes #[0, 0x19, 0x26, 0x09, 0x07, 0x14, 0x05, 0x59, 0x12, 0x31])
        "unexpected PLC DATE_AND_TIME encoding"
      check (isOkEq (S7.decodePlcDateTime encoded) clock) "PLC clock round trip failed"
  check (match S7.decodePlcDateTime (bytes #[0, 0x19, 0x26, 0x1a, 7, 0, 0, 0, 0, 1]) with
    | .error _ => true | _ => false) "invalid BCD clock value was accepted"
  check (isOkEq (S7.encodePassword "secret") (bytes #[0x26, 0x30, 0x10, 0x17, 0x20, 0x36, 0x55, 0x43]))
    "unexpected S7 password encoding"
  check (match S7.encodePassword "" with | .error _ => true | _ => false)
    "empty session password was accepted"
  check (isOkEq (S7.encodePlcStop 10) (bytes #[
    0x32, 1, 0, 0, 0, 10, 0, 16, 0, 0,
    0x29, 0, 0, 0, 0, 0, 9, 0x50, 0x5f, 0x50, 0x52, 0x4f, 0x47, 0x52, 0x41, 0x4d]))
    "unexpected PLC stop request encoding"
  check (isOkEq (S7.encodePlcHotStart 11) (bytes #[
    0x32, 1, 0, 0, 0, 11, 0, 20, 0, 0,
    0x28, 0, 0, 0, 0, 0, 0, 0xfd, 0, 0, 9,
    0x50, 0x5f, 0x50, 0x52, 0x4f, 0x47, 0x52, 0x41, 0x4d]))
    "unexpected PLC hot-start request encoding"
  check (isOkEq (S7.encodePlcColdStart 12) (bytes #[
    0x32, 1, 0, 0, 0, 12, 0, 22, 0, 0,
    0x28, 0, 0, 0, 0, 0, 0, 0xfd, 0, 2, 0x43, 0x20, 9,
    0x50, 0x5f, 0x50, 0x52, 0x4f, 0x47, 0x52, 0x41, 0x4d]))
    "unexpected PLC cold-start request encoding"

def testS7AdvancedVectors : IO Unit := do
  let listBlocks := bytes #[
    0x32, 7, 0, 0, 0, 13, 0, 8, 0, 4,
    0, 1, 0x12, 4, 0x11, 0x43, 1, 0, 0x0a, 0, 0, 0]
  check (isOkEq (S7.encodeListBlocks 13) listBlocks)
    "unexpected list-blocks request encoding"
  check (isOkEq (S7.encodeUserDataContinuation 13 S7.blocksInfoGroup
    S7.listBlocksOfTypeSubfunction 7) (bytes #[
      0x32, 7, 0, 0, 0, 13, 0, 12, 0, 4,
      0, 1, 0x12, 8, 0x11, 0x43, 2, 7, 0, 0, 0, 0,
      0x0a, 0, 0, 0])) "unexpected block-list continuation encoding"
  let countsPayload := bytes #[
    0x30, 0x38, 0, 1, 0x30, 0x45, 0, 2, 0x30, 0x43, 0, 3,
    0x30, 0x41, 0, 4, 0x30, 0x42, 0, 5, 0x30, 0x44, 0, 6,
    0x30, 0x46, 0, 7]
  match S7.decodeBlockCounts countsPayload with
  | .error err => throw <| IO.userError s!"could not decode block counts: {repr err}"
  | .ok counts =>
      check (counts.organizationBlocks == 1 && counts.functionBlocks == 2 &&
        counts.functions == 3 && counts.dataBlocks == 4 && counts.systemDataBlocks == 5 &&
        counts.systemFunctions == 6 && counts.systemFunctionBlocks == 7)
        "block counts were assigned to the wrong types"
  let entries := bytes #[0, 1, 0x10, 2, 0x12, 0x34, 0x20, 3]
  match S7.decodeBlockEntries entries with
  | .error err => throw <| IO.userError s!"could not decode block entries: {repr err}"
  | .ok decoded =>
      check (decoded == #[
        { number := 1, flags := 0x10, language := 2 },
        { number := 0x1234, flags := 0x20, language := 3 }])
        "block entries were decoded incorrectly"
  check (isOkEq (S7.encodeStartUpload 14 .dataBlock 1) (bytes #[
    0x32, 1, 0, 0, 0, 14, 0, 18, 0, 0,
    0x1d, 0, 0, 0, 0, 0, 0, 0, 9, 0x5f, 0x30, 0x41,
    0x30, 0x30, 0x30, 0x30, 0x31, 0x41]))
    "unexpected start-upload encoding"
  let uploadAck := bytes #[
    0x32, 3, 0, 0, 0, 15, 0, 2, 0, 7, 0, 0,
    0x1e, 0, 0, 3, 0, 0xfb, 0xde, 0xad, 0xbe]
  match S7.decodeResponse uploadAck with
  | .error err => throw <| IO.userError s!"could not decode upload ACK: {repr err}"
  | .ok response =>
      match S7.decodeUploadFragment 15 response with
      | .error err => throw <| IO.userError s!"could not decode upload fragment: {repr err}"
      | .ok fragment =>
          check (fragment.isLast && fragment.data == bytes #[0xde, 0xad, 0xbe])
            "upload fragment was decoded incorrectly"
  let serverDownload := bytes #[
    0x32, 1, 0, 0, 0x12, 0x34, 0, 1, 0, 0, 0x1b]
  match S7.decodeJobPdu serverDownload with
  | .error err => throw <| IO.userError s!"could not decode PLC download job: {repr err}"
  | .ok job =>
      check (job.reference == 0x1234 && job.parameters == bytes #[0x1b])
        "PLC download job was decoded incorrectly"
  check (isOkEq (S7.encodeDownloadFragmentResponse 0x1234 true (bytes #[1, 2, 3])) (bytes #[
    0x32, 3, 0, 0, 0x12, 0x34, 0, 2, 0, 7, 0, 0,
    0x1b, 0, 0, 3, 0, 0xfb, 1, 2, 3]))
    "unexpected download-fragment response encoding"
  let forceSzl : S7.Szl := {
    id := 0x0025, index := 0, recordLength := 8, recordCount := 2,
    data := bytes #[0, 0x81, 0, 12, 3, 1, 0, 0, 0, 0x82, 0, 20, 7, 0, 0, 0]
  }
  check (isOkEq (S7.decodeForceTable forceSzl) #[
    { areaCode := 0x81, byteOffset := 12, bit := 3, value := true },
    { areaCode := 0x82, byteOffset := 20, bit := 7, value := false }])
    "force-table entries were decoded incorrectly"

def main : IO Unit := do
  testBinary
  testTPKTRoundTrip
  testTPKTRejectsMalformedFrames
  testTPKTIgnoresReservedInput
  testTPKTSizeBoundary
  testTPKTConformanceCorpus
  testCOTPConnectionRequest
  testCOTPDataRoundTrip
  testCOTPConformanceCorpus
  testS7SetupCommunication
  testS7ResponseDecoding
  testS7DbVectors
  testS7AreaVectors
  testValues
  testS7MultiVectors
  testS7ManagementVectors
  testS7AdvancedVectors
  IO.println "All lean-s7 tests passed."
