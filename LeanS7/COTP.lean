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

@[simp] theorem encodedConnectionRequest_size (request : ConnectionRequest) :
    (encodeConnectionRequest request).size = 18 := by
  simp [encodeConnectionRequest]

/-- One code/length/value entry from a COTP variable header. -/
structure Parameter where
  code : UInt8
  value : ByteArray
  deriving BEq

private def decodeParametersWithFuel : Nat → Cursor → Except DecodeError (List Parameter)
  | 0, cursor =>
      if cursor.remaining = 0 then
        .ok []
      else
        .error (.invalidField cursor.offset "COTP parameter decoder exhausted its input bound")
  | fuel + 1, cursor => do
      if cursor.remaining = 0 then
        return []
      let (code, cursor) ← cursor.readUInt8
      let (length, cursor) ← cursor.readUInt8
      let (value, cursor) ← cursor.readBytes length.toNat
      return { code, value } :: (← decodeParametersWithFuel fuel cursor)

/-- Decode a complete COTP variable part as bounded TLV parameters. Unknown
    codes remain available to the caller for TPDU-specific policy. -/
def decodeParameters (data : ByteArray) : Except DecodeError (List Parameter) :=
  decodeParametersWithFuel data.size { data }

/-- Locate the last occurrence of a parameter code, as required by ISO 8073
    duplicate-parameter semantics. -/
def findLastParameter (parameters : List Parameter) (code : UInt8) : Option ByteArray :=
  parameters.foldl (fun found parameter =>
    if parameter.code == code then some parameter.value else found) none

@[simp] theorem findLastParameter_nil (code : UInt8) :
    findLastParameter [] code = none := by
  rfl

/-- Appending a matching parameter makes its value authoritative. -/
theorem findLastParameter_append_match (parameters : List Parameter)
    (code : UInt8) (value : ByteArray) :
    findLastParameter (parameters ++ [{ code, value }]) code = some value := by
  simp [findLastParameter, List.foldl_append]

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

@[simp] theorem encodedDisconnectRequest_size (request : DisconnectRequest) :
    (encodeDisconnectRequest request).size = 7 := by
  simp [encodeDisconnectRequest]

/-- Strictly decode one complete COTP disconnect request. -/
def decodeDisconnectRequest (data : ByteArray) : Except DecodeError DisconnectRequest := do
  let cursor : Cursor := { data }
  let (headerLength, cursor) ← cursor.readUInt8
  if headerLength != 6 then
    throw (.invalidField 0 s!"expected COTP disconnect header length 6, got {headerLength}")
  let (code, cursor) ← cursor.readUInt8
  if code != disconnectRequestCode then
    throw (.invalidField 1 s!"expected COTP disconnect request 0x80, got {code}")
  let (destinationReference, cursor) ← cursor.readUInt16BE
  let (sourceReference, cursor) ← cursor.readUInt16BE
  let (reason, cursor) ← cursor.readUInt8
  cursor.finish
  return { destinationReference, sourceReference, reason }

/-- Encoding and then decoding a COTP disconnect request preserves both
    references and the reason code. -/
theorem decodeDisconnectRequest_encodeDisconnectRequest
    (request : DisconnectRequest) :
    decodeDisconnectRequest (encodeDisconnectRequest request) = .ok request := by
  let data := encodeDisconnectRequest request
  have hsize : data.size = 7 := by simp [data]
  have hread0 : Cursor.readUInt8 { data } =
      .ok (6, { data, offset := 1 }) := by
    rw [Cursor.readUInt8_of_lt _ (by
      dsimp only [Cursor.offset, Cursor.data]
      rw [hsize]
      omega)]
    congr 2 <;> simp [data, encodeDisconnectRequest, bytes]
  have hread1 : Cursor.readUInt8 { data, offset := 1 } =
      .ok (disconnectRequestCode, { data, offset := 2 }) := by
    rw [Cursor.readUInt8_of_lt _ (by
      dsimp only [Cursor.offset, Cursor.data]
      rw [hsize]
      omega)]
    congr 2 <;> simp [data, encodeDisconnectRequest, bytes]
  have hdestination : Cursor.readUInt16BE { data, offset := 2 } =
      .ok (request.destinationReference, { data, offset := 4 }) := by
    simpa [data, encodeDisconnectRequest, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[6, disconnectRequestCode])
        (uint16BE request.sourceReference ++ bytes #[request.reason])
        request.destinationReference
  have hsource : Cursor.readUInt16BE { data, offset := 4 } =
      .ok (request.sourceReference, { data, offset := 6 }) := by
    simpa [data, encodeDisconnectRequest, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[6, disconnectRequestCode] ++ uint16BE request.destinationReference)
        (bytes #[request.reason]) request.sourceReference
  have hreason : Cursor.readUInt8 { data, offset := 6 } =
      .ok (request.reason, { data, offset := 7 }) := by
    rw [Cursor.readUInt8_of_lt _ (by
      dsimp only [Cursor.offset, Cursor.data]
      rw [hsize]
      omega)]
    congr 2 <;> simp [data, encodeDisconnectRequest, bytes]
  change decodeDisconnectRequest data = .ok request
  rw [decodeDisconnectRequest, hread0]
  change Except.bind (Except.ok (6, ({ data, offset := 1 } : Cursor)))
    (fun headerResult => _) = _
  rw [Except.bind]
  simp
  rw [hread1]
  change Except.bind (Except.ok
      (disconnectRequestCode, ({ data, offset := 2 } : Cursor)))
    (fun codeResult => _) = _
  rw [Except.bind]
  simp
  rw [hdestination]
  change Except.bind (Except.ok
      (request.destinationReference, ({ data, offset := 4 } : Cursor)))
    (fun destinationResult => _) = _
  rw [Except.bind, hsource]
  change Except.bind (Except.ok
      (request.sourceReference, ({ data, offset := 6 } : Cursor)))
    (fun sourceResult => _) = _
  rw [Except.bind, hreason]
  change Except.bind (Except.ok
      (request.reason, ({ data, offset := 7 } : Cursor)))
    (fun reasonResult => _) = _
  rw [Except.bind]
  have hfinish : Cursor.finish ({ data, offset := 7 } : Cursor) = .ok () := by
    rw [Cursor.finish, if_pos (by
      dsimp only [Cursor.offset, Cursor.data]
      rw [hsize])]
  rw [hfinish]
  cases request
  rfl

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

/-- Validate the ISO 8073 power-of-two TPDU size codes supported by RFC 1006. -/
def validateTpduSizeExponent (exponent : UInt8) (offset : Nat) :
    Except DecodeError Unit := do
  if exponent.toNat < 7 ∨ 13 < exponent.toNat then
    throw (.invalidField offset s!"invalid COTP TPDU size exponent {exponent}")

/-- Every accepted TPDU size code denotes a standard size from 128 through
    8192 octets. -/
theorem validateTpduSizeExponent_bounds (exponent : UInt8) (offset : Nat)
    (hvalidate : validateTpduSizeExponent exponent offset = .ok ()) :
    7 ≤ exponent.toNat ∧ exponent.toNat ≤ 13 := by
  simp only [validateTpduSizeExponent] at hvalidate
  split at hvalidate <;> rename_i hbounds
  · contradiction
  · exact ⟨Nat.le_of_not_lt (not_or.mp hbounds).1,
      Nat.le_of_not_lt (not_or.mp hbounds).2⟩

/-- Validate that a connection confirmation belongs to the request and accepts
    the requested transport class. -/
def validateConnectionConfirm (request : ConnectionRequest)
    (confirmation : ConnectionConfirm) : Except DecodeError Unit := do
  if confirmation.destinationReference != request.sourceReference then
    throw (.invalidField 2
      s!"expected COTP destination reference {request.sourceReference}, got {confirmation.destinationReference}")
  if confirmation.classOption != request.classOption then
    throw (.invalidField 6
      s!"expected COTP class option {request.classOption}, got {confirmation.classOption}")
  validateTpduSizeExponent request.tpduSizeExponent 7
  let parameters ← decodeParameters confirmation.parameters
  match findLastParameter parameters pduSizeParameter with
  | none => pure ()
  | some value =>
      if value.size != 1 then
        throw (.invalidField 7 "COTP TPDU size parameter must contain one byte")
      let exponent := value[0]!
      validateTpduSizeExponent exponent 9
      if exponent > request.tpduSizeExponent then
        throw (.invalidField 9
          s!"COTP TPDU size exponent {exponent} exceeds requested {request.tpduSizeExponent}")

/-- A confirmation with the wrong destination reference is rejected. -/
theorem validateConnectionConfirm_rejects_destination (request : ConnectionRequest)
    (confirmation : ConnectionConfirm)
    (hreference : confirmation.destinationReference ≠ request.sourceReference) :
    validateConnectionConfirm request confirmation = .error (.invalidField 2
      s!"expected COTP destination reference {request.sourceReference}, got {confirmation.destinationReference}") := by
  rw [validateConnectionConfirm, if_pos (by simpa using hreference)]
  rfl

/-- A successfully validated confirmation is correlated to the initiating
    connection request. -/
theorem validateConnectionConfirm_destination_eq (request : ConnectionRequest)
    (confirmation : ConnectionConfirm)
    (h : validateConnectionConfirm request confirmation = .ok ()) :
    confirmation.destinationReference = request.sourceReference := by
  by_cases hreference : confirmation.destinationReference = request.sourceReference
  · exact hreference
  · rw [validateConnectionConfirm_rejects_destination request confirmation hreference] at h
    contradiction

/-- A successfully validated confirmation accepts the requested transport
    class. -/
theorem validateConnectionConfirm_class_eq (request : ConnectionRequest)
    (confirmation : ConnectionConfirm)
    (h : validateConnectionConfirm request confirmation = .ok ()) :
    confirmation.classOption = request.classOption := by
  by_cases hclass : confirmation.classOption = request.classOption
  · exact hclass
  · have hreference := validateConnectionConfirm_destination_eq request confirmation h
    rw [validateConnectionConfirm, if_neg (by simp [hreference]),
      if_pos (by simpa using hclass)] at h
    contradiction

/-- Return the selected TPDU size exponent after full confirmation validation.
    An omitted parameter conservatively retains the requested size. -/
def negotiatedTpduSizeExponent (request : ConnectionRequest)
    (confirmation : ConnectionConfirm) : Except DecodeError UInt8 := do
  validateConnectionConfirm request confirmation
  let parameters ← decodeParameters confirmation.parameters
  match findLastParameter parameters pduSizeParameter with
  | none => pure request.tpduSizeExponent
  | some value => pure value[0]!

def tpduSize (exponent : UInt8) : Nat :=
  2 ^ exponent.toNat

/-- Check that one unsegmented COTP data TPDU can contain an S7 PDU and its
    three-byte class-0 data header. -/
def validateDataPayloadBudget (exponent : UInt8) (payloadSize : Nat) :
    Except DecodeError Unit := do
  validateTpduSizeExponent exponent 0
  if tpduSize exponent < 3 + payloadSize then
    throw (.invalidField 0
      s!"COTP TPDU size {tpduSize exponent} cannot contain {payloadSize} payload bytes")

/-- Every accepted unsegmented data budget fits its header and complete payload
    within the negotiated TPDU size. -/
theorem validateDataPayloadBudget_fits (exponent : UInt8) (payloadSize : Nat)
    (hvalidate : validateDataPayloadBudget exponent payloadSize = .ok ()) :
    3 + payloadSize ≤ tpduSize exponent := by
  rw [validateDataPayloadBudget] at hvalidate
  cases hexponent : validateTpduSizeExponent exponent 0 with
  | error error =>
      rw [hexponent] at hvalidate
      contradiction
  | ok value =>
      have hvalue : value = () := Subsingleton.elim _ _
      subst value
      rw [hexponent] at hvalidate
      split at hvalidate <;> rename_i hsize
      · contradiction
      · exact Nat.le_of_not_lt hsize

structure Data where
  payload : ByteArray
  endOfTransmission : Bool := true
  deriving BEq

/-- Accumulated payload from one or more COTP data TPDUs. -/
structure Reassembly where
  payload : ByteArray := ByteArray.empty
  deriving BEq

/-- Append one segment and report whether it completes the TSDU. -/
def Reassembly.push (state : Reassembly) (segment : Data) : Reassembly × Bool :=
  ({ payload := state.payload ++ segment.payload }, segment.endOfTransmission)

/-- Reassembly preserves arrival order and appends every segment exactly once. -/
theorem Reassembly.push_payload (state : Reassembly) (segment : Data) :
    (state.push segment).1.payload = state.payload ++ segment.payload := by
  rfl

/-- Reassembly completes exactly on a segment carrying the EOT flag. -/
theorem Reassembly.push_complete_iff (state : Reassembly) (segment : Data) :
    (state.push segment).2 = true ↔ segment.endOfTransmission = true := by
  rfl

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
