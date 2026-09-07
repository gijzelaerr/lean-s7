import LeanS7

open LeanS7

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

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

def testCOTPConnectionRequest : IO Unit := do
  let encoded := COTP.encodeConnectionRequest {}
  let expected := bytes #[
    0x11, 0xe0, 0x00, 0x00, 0x00, 0x01, 0x00,
    0xc1, 0x02, 0x01, 0x00,
    0xc2, 0x02, 0x01, 0x02,
    0xc0, 0x01, 0x0a]
  check (encoded == expected) "unexpected COTP connection request encoding"

def testCOTPDataRoundTrip : IO Unit := do
  let pdu : COTP.Data := { payload := bytes #[0x32, 0x01, 0x00] }
  let encoded := COTP.encodeData pdu
  check (encoded == bytes #[2, 0xf0, 0x80, 0x32, 0x01, 0x00]) "unexpected COTP data encoding"
  check (match COTP.decodeData encoded with | .ok decoded => decoded == pdu | .error _ => false)
    "COTP data round trip failed"

def testS7SetupCommunication : IO Unit := do
  let expected := bytes #[
    0x32, 0x01, 0x00, 0x00, 0x00, 0x01, 0x00, 0x08, 0x00, 0x00,
    0xf0, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01, 0xe0]
  match S7.encodeSetupCommunication 1 with
  | .error err => throw <| IO.userError s!"could not encode S7 handshake: {repr err}"
  | .ok encoded =>
      check (encoded == expected) "unexpected S7 setup-communication encoding"
      let cotp := COTP.encodeData { payload := encoded }
      match TPKT.encode { payload := cotp } with
      | .ok packet => check (packet.size == 25) "unexpected complete handshake packet size"
      | .error err => throw <| IO.userError s!"could not frame S7 handshake: {repr err}"

def testS7ResponseDecoding : IO Unit := do
  let setupAck := bytes #[
    0x32, 0x03, 0x00, 0x00, 0x00, 0x01, 0x00, 0x08, 0x00, 0x00, 0x00, 0x00,
    0xf0, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01, 0xe0]
  match S7.decodeResponse setupAck with
  | .error err => throw <| IO.userError s!"could not decode setup ACK: {repr err}"
  | .ok response =>
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

def main : IO Unit := do
  testBinary
  testTPKTRoundTrip
  testTPKTRejectsMalformedFrames
  testCOTPConnectionRequest
  testCOTPDataRoundTrip
  testS7SetupCommunication
  testS7ResponseDecoding
  testS7DbVectors
  testS7AreaVectors
  IO.println "All lean-s7 tests passed."
