import LeanS7.Binary

namespace LeanS7.COTP

def connectionRequestCode : UInt8 := 0xe0
def connectionConfirmCode : UInt8 := 0xd0
def disconnectRequestCode : UInt8 := 0x80
def dataCode : UInt8 := 0xf0
def pduSizeParameter : UInt8 := 0xc0
def callingTsapParameter : UInt8 := 0xc1
def calledTsapParameter : UInt8 := 0xc2

structure ConnectionRequest where
  destinationReference : UInt16 := 0
  sourceReference : UInt16 := 1
  classOption : UInt8 := 0
  callingTsap : UInt16 := 0x0100
  calledTsap : UInt16 := 0x0102
  tpduSizeExponent : UInt8 := 0x0a
  deriving Repr, BEq

/-- Encode the COTP connection request used to negotiate an ISO-on-TCP session. -/
def encodeConnectionRequest (request : ConnectionRequest) : ByteArray :=
  let fixed := bytes #[
    17, connectionRequestCode,
    UInt8.ofNat (request.destinationReference.toNat / 256), UInt8.ofNat request.destinationReference.toNat,
    UInt8.ofNat (request.sourceReference.toNat / 256), UInt8.ofNat request.sourceReference.toNat,
    request.classOption]
  let calling := bytes #[callingTsapParameter, 2] ++ uint16BE request.callingTsap
  let called := bytes #[calledTsapParameter, 2] ++ uint16BE request.calledTsap
  let size := bytes #[pduSizeParameter, 1, request.tpduSizeExponent]
  fixed ++ calling ++ called ++ size

structure ConnectionConfirm where
  destinationReference : UInt16
  sourceReference : UInt16
  classOption : UInt8
  parameters : ByteArray
  deriving BEq

structure DisconnectRequest where
  destinationReference : UInt16
  sourceReference : UInt16 := 1
  reason : UInt8 := 0
  deriving Repr, BEq

def encodeDisconnectRequest (request : DisconnectRequest) : ByteArray :=
  bytes #[6, disconnectRequestCode] ++ uint16BE request.destinationReference ++
    uint16BE request.sourceReference ++ bytes #[request.reason]

/-- Decode a COTP connection confirmation while retaining negotiation parameters. -/
def decodeConnectionConfirm (data : ByteArray) : Except DecodeError ConnectionConfirm := do
  let cursor : Cursor := { data }
  let (headerLength, cursor) ← cursor.readUInt8
  if headerLength.toNat + 1 != data.size then
    throw (.invalidField 0 "COTP header length does not match packet size")
  let (code, cursor) ← cursor.readUInt8
  if code != connectionConfirmCode then
    throw (.invalidField 1 s!"expected connection confirmation 0xd0, got {code}")
  let (destinationReference, cursor) ← cursor.readUInt16BE
  let (sourceReference, cursor) ← cursor.readUInt16BE
  let (classOption, cursor) ← cursor.readUInt8
  let (parameters, cursor) ← cursor.readBytes cursor.remaining
  cursor.finish
  return { destinationReference, sourceReference, classOption, parameters }

structure Data where
  payload : ByteArray
  endOfTransmission : Bool := true
  deriving BEq

def encodeData (pdu : Data) : ByteArray :=
  bytes #[2, dataCode, if pdu.endOfTransmission then 0x80 else 0x00] ++ pdu.payload

def decodeData (data : ByteArray) : Except DecodeError Data := do
  let cursor : Cursor := { data }
  let (headerLength, cursor) ← cursor.readUInt8
  if headerLength != 2 then
    throw (.invalidField 0 s!"expected COTP data header length 2, got {headerLength}")
  let (code, cursor) ← cursor.readUInt8
  if code != dataCode then
    throw (.invalidField 1 s!"expected COTP data TPDU 0xf0, got {code}")
  let (flags, cursor) ← cursor.readUInt8
  if flags &&& 0x7f != 0 then
    throw (.invalidField 2 s!"COTP class 0 TPDU number must be zero, got {flags &&& 0x7f}")
  let (payload, cursor) ← cursor.readBytes cursor.remaining
  cursor.finish
  return { payload, endOfTransmission := flags &&& 0x80 != 0 }

theorem encodedData_size (pdu : Data) :
    (encodeData pdu).size = 3 + pdu.payload.size := by
  rw [encodeData, ByteArray.size_append]
  change 3 + pdu.payload.size = 3 + pdu.payload.size
  rfl

/-- Encoding and then decoding a COTP data TPDU returns the original value. -/
theorem decodeData_encodeData (pdu : Data) :
    decodeData (encodeData pdu) = .ok pdu := by
  rcases pdu with ⟨payload, endOfTransmission⟩
  let flag : UInt8 := if endOfTransmission then 0x80 else 0x00
  let data := bytes #[2, dataCode, flag] ++ payload
  have hsize : data.size = 3 + payload.size := by
    dsimp only [data]
    rw [ByteArray.size_append]
    change 3 + payload.size = 3 + payload.size
    rfl
  have hread0 : Cursor.readUInt8 { data } =
      .ok (2, { data, offset := 1 }) := by
    rw [Cursor.readUInt8_of_lt _ (by dsimp; rw [hsize]; omega)]
    congr 2 <;> simp [data, bytes]
  have hread1 : Cursor.readUInt8 { data, offset := 1 } =
      .ok (dataCode, { data, offset := 2 }) := by
    rw [Cursor.readUInt8_of_lt _ (by dsimp; rw [hsize]; omega)]
    congr 2 <;> simp [data, bytes]
  have hread2 : Cursor.readUInt8 { data, offset := 2 } =
      .ok (flag, { data, offset := 3 }) := by
    rw [Cursor.readUInt8_of_lt _ (by dsimp; rw [hsize]; omega)]
    congr 2 <;> simp [data, bytes]
  have hpayloadRead : Cursor.readBytes { data, offset := 3 } payload.size =
      .ok (payload, { data, offset := 3 + payload.size }) := by
    rw [Cursor.readBytes]
    rw [if_pos (by simp [Cursor.remaining, hsize])]
    have hextract : data.extract 3 (3 + payload.size) = payload := by
      dsimp only [data]
      apply ByteArray.extract_append_eq_right
      · change 3 = (#[2, dataCode, flag] : Array UInt8).size
        simp
      · change 3 + payload.size = (#[2, dataCode, flag] : Array UInt8).size + payload.size
        simp
    change Except.ok
      (data.extract 3 (3 + payload.size),
        ({ data, offset := 3 + payload.size } : Cursor)) = _
    rw [hextract]
  have hremaining : ({ data, offset := 3 } : Cursor).remaining = payload.size := by
    simp [Cursor.remaining, hsize]
  have hfinish : Cursor.finish ({ data, offset := 3 + payload.size } : Cursor) = .ok () := by
    rw [Cursor.finish, if_pos (by dsimp; rw [hsize])]
  change decodeData data = .ok { payload, endOfTransmission }
  rw [decodeData, hread0]
  change Except.bind (Except.ok (2, ({ data, offset := 1 } : Cursor)))
    (fun headerResult => _) = _
  rw [Except.bind]
  simp
  rw [hread1]
  change Except.bind (Except.ok (dataCode, ({ data, offset := 2 } : Cursor)))
    (fun codeResult => _) = _
  rw [Except.bind]
  simp
  rw [hread2]
  change Except.bind (Except.ok (flag, ({ data, offset := 3 } : Cursor)))
    (fun flagsResult => _) = _
  rw [Except.bind]
  simp
  cases endOfTransmission
  · rw [hremaining, hpayloadRead]
    simp [flag]
    change (fun _ : Unit => ({ payload, endOfTransmission := false } : Data))
      <$> Cursor.finish ({ data, offset := 3 + payload.size } : Cursor) = _
    rw [hfinish]
    rfl
  · rw [hremaining, hpayloadRead]
    have hnumber : (0x80 : UInt8) &&& 0x7f = 0 := by native_decide
    simp [flag, hnumber]
    change (fun _ : Unit => ({ payload, endOfTransmission := true } : Data))
      <$> Cursor.finish ({ data, offset := 3 + payload.size } : Cursor) = _
    rw [hfinish]
    rfl

end LeanS7.COTP
