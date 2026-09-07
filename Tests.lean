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

def main : IO Unit := do
  testBinary
  testTPKTRoundTrip
  testTPKTRejectsMalformedFrames
  testCOTPConnectionRequest
  testCOTPDataRoundTrip
  testS7SetupCommunication
  IO.println "All lean-s7 tests passed."
