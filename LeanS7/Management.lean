import LeanS7.S7

namespace LeanS7.S7

def userDataType : UInt8 := 0x07
def userDataRequestMethod : UInt8 := 0x11
def userDataResponseMethod : UInt8 := 0x12
def userDataRequestType : UInt8 := 0x40
def userDataResponseType : UInt8 := 0x80
def szlGroup : UInt8 := 0x04
def securityGroup : UInt8 := 0x05
def clockGroup : UInt8 := 0x07
def readSzlSubfunction : UInt8 := 0x01
def readClockSubfunction : UInt8 := 0x01
def setClockSubfunction : UInt8 := 0x02
def enterPasswordSubfunction : UInt8 := 0x01
def clearPasswordSubfunction : UInt8 := 0x02
def startFunction : UInt8 := 0x28
def stopFunction : UInt8 := 0x29

structure UserDataResponse where
  reference : UInt16
  group : UInt8
  subfunction : UInt8
  sequence : UInt8
  dataUnitReference : UInt8
  hasMoreData : Bool
  error : UInt16
  returnCode : UInt8
  transportSize : UInt8
  payload : ByteArray
  deriving BEq

/-- CPU/SZL and block USER_DATA fragments share a data-unit reference. The
    sequence byte is a PLC-issued opaque token echoed in the next request,
    not a locally incremented counter. Zero is permitted as an identity. -/
def correlateUserDataFragment (expected : Option UInt8) (response : UserDataResponse) :
    Except DecodeError UInt8 := do
  if let some previous := expected then
    if response.dataUnitReference != previous then
      throw (.invalidField 18 s!"USER_DATA data-unit reference changed from {previous} to {response.dataUnitReference}")
  return response.dataUnitReference

theorem correlateUserDataFragment_initial (response : UserDataResponse) :
    correlateUserDataFragment none response = .ok response.dataUnitReference := by
  rfl

theorem correlateUserDataFragment_success (previous actual : UInt8)
    (response : UserDataResponse)
    (h : correlateUserDataFragment (some previous) response = .ok actual) :
    response.dataUnitReference = previous ∧ actual = previous := by
  simp only [correlateUserDataFragment, pure, Except.pure] at h
  split at h
  · contradiction
  · simp_all

/-- Native Snap7 emits an empty null-data acknowledgement for these three
    mutating services. This is not a general permission to treat 0x0a as
    success for payload-bearing SZL, clock-read, or block services. -/
def supportsNullUserDataAcknowledgement (group subfunction : UInt8) : Bool :=
  (group == clockGroup && subfunction == setClockSubfunction) ||
  (group == securityGroup &&
    (subfunction == enterPasswordSubfunction || subfunction == clearPasswordSubfunction))

/-- Fixed single-response services must not expose an incomplete fragment.
    Segmented services use their separate bounded assembly paths. -/
def requireCompleteUserData (response : UserDataResponse) : Except DecodeError ByteArray :=
  if response.hasMoreData then
    .error (.invalidField 19 "unexpected USER_DATA continuation for single-response service")
  else .ok response.payload

theorem requireCompleteUserData_complete (response : UserDataResponse) (payload : ByteArray)
    (h : requireCompleteUserData response = .ok payload) :
    response.hasMoreData = false ∧ payload = response.payload := by
  unfold requireCompleteUserData at h
  split at h
  · contradiction
  · cases h
    simp_all

def encodeUserDataHeader (reference : UInt16) (parameters data : ByteArray) :
    Except EncodeError ByteArray := do
  if parameters.size > maxSectionSize then
    throw (.parametersTooLarge parameters.size maxSectionSize)
  if data.size > maxSectionSize then
    throw (.dataTooLarge data.size maxSectionSize)
  return bytes #[protocolId, userDataType, 0, 0] ++ uint16BE reference ++
    uint16BE (UInt16.ofNat parameters.size) ++ uint16BE (UInt16.ofNat data.size) ++
    parameters ++ data

/-- Every successfully encoded USER_DATA PDU has the common ten-byte header
    and the exact encoded parameter and data section sizes. -/
theorem encodedUserDataHeader_size (reference : UInt16)
    (parameters data packet : ByteArray)
    (hencode : encodeUserDataHeader reference parameters data = .ok packet) :
    packet.size = jobHeaderSize + parameters.size + data.size := by
  by_cases hp : parameters.size ≤ maxSectionSize
  · by_cases hd : data.size ≤ maxSectionSize
    · rw [encodeUserDataHeader, if_neg (Nat.not_lt.mpr hp),
        if_neg (Nat.not_lt.mpr hd)] at hencode
      injection hencode with hpacket
      subst packet
      simp [jobHeaderSize]
    · rw [encodeUserDataHeader, if_neg (Nat.not_lt.mpr hp),
        if_pos (Nat.lt_of_not_ge hd)] at hencode
      contradiction
  · rw [encodeUserDataHeader, if_pos (Nat.lt_of_not_ge hp)] at hencode
    contradiction

def userDataParameters (group subfunction sequence : UInt8)
    (continuation : Bool) : ByteArray :=
  if continuation then
    bytes #[0, 1, 0x12, 0x08, userDataResponseMethod,
      UInt8.lor userDataRequestType group, subfunction, sequence, 0, 0, 0, 0]
  else
    bytes #[0, 1, 0x12, 0x04, userDataRequestMethod,
      UInt8.lor userDataRequestType group, subfunction, sequence]

def encodeReadSzl (reference id index : UInt16) : Except EncodeError ByteArray :=
  encodeUserDataHeader reference
    (userDataParameters szlGroup readSzlSubfunction 0 false)
    (bytes #[0xff, octetTransportSize] ++ uint16BE 4 ++ uint16BE id ++ uint16BE index)

def encodeReadSzlContinuation (reference : UInt16) (sequence : UInt8) : Except EncodeError ByteArray :=
  encodeUserDataHeader reference
    (userDataParameters szlGroup readSzlSubfunction sequence true)
    (bytes #[0x0a, 0, 0, 0])

def encodeReadClock (reference : UInt16) : Except EncodeError ByteArray :=
  encodeUserDataHeader reference
    (userDataParameters clockGroup readClockSubfunction 0 false)
    (bytes #[0x0a, 0, 0, 0])

def encodeSetClock (reference : UInt16) (payload : ByteArray) : Except EncodeError ByteArray := do
  if payload.size != 10 then
    throw (.invalidPayloadSize payload.size 10)
  encodeUserDataHeader reference
    (userDataParameters clockGroup setClockSubfunction 0 false)
    (bytes #[0xff, octetTransportSize] ++ uint16BE 10 ++ payload)

def encodeSetPassword (reference : UInt16) (encodedPassword : ByteArray) : Except EncodeError ByteArray := do
  if encodedPassword.size != 8 then
    throw (.invalidPayloadSize encodedPassword.size 8)
  encodeUserDataHeader reference
    (userDataParameters securityGroup enterPasswordSubfunction 0 false)
    (bytes #[0xff, octetTransportSize] ++ uint16BE 8 ++ encodedPassword)

def encodeClearPassword (reference : UInt16) : Except EncodeError ByteArray :=
  encodeUserDataHeader reference
    (userDataParameters securityGroup clearPasswordSubfunction 0 false)
    (bytes #[0x0a, 0, 0, 0])

def decodeUserDataResponse (expectedReference : UInt16) (expectedGroup expectedSubfunction : UInt8)
    (pdu : ByteArray) : Except DecodeError UserDataResponse := do
  let cursor : Cursor := { data := pdu }
  let (actualProtocolId, cursor) ← cursor.readUInt8
  if actualProtocolId != protocolId then
    throw (.invalidField 0 s!"expected S7 protocol ID 0x32, got {actualProtocolId}")
  let (pduType, cursor) ← cursor.readUInt8
  if pduType != userDataType then
    throw (.invalidField 1 s!"expected S7 USER_DATA response, got {pduType}")
  let (_, cursor) ← cursor.readUInt16BE
  let (reference, cursor) ← cursor.readUInt16BE
  if reference != expectedReference then
    throw (.invalidField 4 s!"expected PDU reference {expectedReference}, got {reference}")
  let (parameterLength, cursor) ← cursor.readUInt16BE
  let (dataLength, cursor) ← cursor.readUInt16BE
  let expectedSize := jobHeaderSize + parameterLength.toNat + dataLength.toNat
  if pdu.size != expectedSize then
    throw (.invalidField 6 s!"S7 section lengths require {expectedSize} bytes, got {pdu.size}")
  if parameterLength != 12 then
    throw (.invalidField jobHeaderSize s!"USER_DATA response parameters must be 12 bytes, got {parameterLength}")
  let (parameters, cursor) ← cursor.readBytes parameterLength.toNat
  let (data, cursor) ← cursor.readBytes dataLength.toNat
  cursor.finish
  let parameterCursor : Cursor := { data := parameters }
  let (head, parameterCursor) ← parameterCursor.readBytes 3
  if head != bytes #[0, 1, 0x12] then
    throw (.invalidField jobHeaderSize "invalid USER_DATA parameter header")
  let (parameterDataLength, parameterCursor) ← parameterCursor.readUInt8
  if parameterDataLength != 8 then
    throw (.invalidField (jobHeaderSize + 3) "invalid USER_DATA response parameter length")
  let (method, parameterCursor) ← parameterCursor.readUInt8
  if method != userDataResponseMethod then
    throw (.invalidField (jobHeaderSize + 4) "invalid USER_DATA response method")
  let (typeGroup, parameterCursor) ← parameterCursor.readUInt8
  if UInt8.land typeGroup 0xf0 != userDataResponseType || UInt8.land typeGroup 0x0f != expectedGroup then
    throw (.invalidField (jobHeaderSize + 5) "unexpected USER_DATA type or function group")
  let (subfunction, parameterCursor) ← parameterCursor.readUInt8
  if subfunction != expectedSubfunction then
    throw (.invalidField (jobHeaderSize + 6) "unexpected USER_DATA subfunction")
  let (sequence, parameterCursor) ← parameterCursor.readUInt8
  let (dataUnitReference, parameterCursor) ← parameterCursor.readUInt8
  let (lastDataUnit, parameterCursor) ← parameterCursor.readUInt8
  if lastDataUnit != 0 && lastDataUnit != 1 then
    throw (.invalidField (jobHeaderSize + 9) "invalid USER_DATA continuation flag")
  let (error, parameterCursor) ← parameterCursor.readUInt16BE
  parameterCursor.finish
  if error != 0 then
    throw (.remoteFailure (jobHeaderSize + 10) s!"USER_DATA request failed with code {error}")
  if data.size < 4 then
    throw (.unexpectedEnd (jobHeaderSize + parameterLength.toNat) 4 data.size)
  let dataCursor : Cursor := { data }
  let (returnCode, dataCursor) ← dataCursor.readUInt8
  let (transportSize, dataCursor) ← dataCursor.readUInt8
  let (payloadLength, dataCursor) ← dataCursor.readUInt16BE
  let nullAcknowledgement := returnCode == 0x0a &&
    supportsNullUserDataAcknowledgement expectedGroup expectedSubfunction
  if returnCode != 0xff && !nullAcknowledgement then
    throw (.remoteFailure (jobHeaderSize + parameterLength.toNat)
      s!"USER_DATA item failed with code {returnCode}")
  if nullAcknowledgement then
    if transportSize != 0 || payloadLength != 0 || lastDataUnit != 0 then
      throw (.invalidField (jobHeaderSize + parameterLength.toNat)
        "USER_DATA null acknowledgement must be complete with zero transport size and payload length")
  else if transportSize != octetTransportSize then
    throw (.invalidField (jobHeaderSize + parameterLength.toNat + 1)
      s!"expected USER_DATA octet transport size {octetTransportSize}, got {transportSize}")
  let (payload, dataCursor) ← dataCursor.readBytes payloadLength.toNat
  dataCursor.finish
  return {
    reference := reference
    group := expectedGroup
    subfunction := subfunction
    sequence := sequence
    dataUnitReference := dataUnitReference
    hasMoreData := lastDataUnit != 0
    error := error
    returnCode := returnCode
    transportSize := transportSize
    payload := payload
  }

/-- The canonical bytes of a USER_DATA response: the S7 header with a zero reserved
    word, the 12-byte response parameters and the data item. The type/function-group
    byte is the response type with the group in its low nibble, and the continuation
    flag is 1 exactly when more data follows. The two-byte length fields are exact for
    payloads of up to 65531 bytes, which covers everything `decodeUserDataResponse`
    accepts. -/
def encodeUserDataResponse (response : UserDataResponse) : ByteArray :=
  bytes #[protocolId, userDataType, 0, 0] ++ uint16BE response.reference ++
    uint16BE 12 ++ uint16BE (UInt16.ofNat (4 + response.payload.size)) ++
    bytes #[0, 1, 0x12, 8, userDataResponseMethod,
      UInt8.lor userDataResponseType response.group, response.subfunction,
      response.sequence, response.dataUnitReference,
      if response.hasMoreData then 1 else 0] ++
    uint16BE response.error ++ bytes #[response.returnCode, response.transportSize] ++
    uint16BE (UInt16.ofNat response.payload.size) ++ response.payload

def decodePduReference (pdu : ByteArray) : Except DecodeError UInt16 := do
  let cursor : Cursor := { data := pdu }
  let (actualProtocolId, cursor) ← cursor.readUInt8
  if actualProtocolId != protocolId then
    throw (.invalidField 0 s!"expected S7 protocol ID 0x32, got {actualProtocolId}")
  let (_, cursor) ← cursor.readUInt8
  let (_, cursor) ← cursor.readUInt16BE
  let (reference, _) ← cursor.readUInt16BE
  return reference

/-- The lightweight correlation decoder returns the reference from every S7
    header prefix, independently of the PDU kind and following sections. -/
theorem decodePduReference_header (kind : UInt8) (reference : UInt16)
    (suffix : ByteArray) :
    decodePduReference
      (bytes #[protocolId, kind, 0, 0] ++ uint16BE reference ++ suffix) =
      .ok reference := by
  let pdu := bytes #[protocolId, kind, 0, 0] ++ uint16BE reference ++ suffix
  have hpduSize : pdu.size = 6 + suffix.size := by simp [pdu]
  have hread0 : Cursor.readUInt8 { data := pdu } =
      .ok (protocolId, { data := pdu, offset := 1 }) := by
    rw [Cursor.readUInt8_of_lt _ (by
      dsimp only [Cursor.offset]
      rw [hpduSize]
      omega)]
    congr 2 <;> simp [pdu, bytes]
  have hread1 : Cursor.readUInt8 { data := pdu, offset := 1 } =
      .ok (kind, { data := pdu, offset := 2 }) := by
    rw [Cursor.readUInt8_of_lt _ (by
      dsimp only [Cursor.offset]
      rw [hpduSize]
      omega)]
    congr 2 <;> simp [pdu, bytes]
  have hreserved : Cursor.readUInt16BE { data := pdu, offset := 2 } =
      .ok (0, { data := pdu, offset := 4 }) := by
    have hfixed : bytes #[protocolId, kind, 0, 0] =
        bytes #[protocolId, kind] ++ uint16BE 0 := by
      change ByteArray.mk #[protocolId, kind, 0, 0] =
        ByteArray.mk (#[protocolId, kind] ++ #[0, 0])
      rfl
    simpa [pdu, hfixed, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, kind]) (uint16BE reference ++ suffix) 0
  have href : Cursor.readUInt16BE { data := pdu, offset := 4 } =
      .ok (reference, { data := pdu, offset := 6 }) := by
    simpa [pdu, ByteArray.append_assoc] using
      Cursor.readUInt16BE_append_uint16BE
        (bytes #[protocolId, kind, 0, 0]) suffix reference
  change decodePduReference pdu = .ok reference
  rw [decodePduReference, hread0]
  change Except.bind (Except.ok
      (protocolId, ({ data := pdu, offset := 1 } : Cursor)))
    (fun protocolResult => _) = _
  rw [Except.bind]
  simp
  rw [hread1]
  change Except.bind (Except.ok
      (kind, ({ data := pdu, offset := 2 } : Cursor)))
    (fun kindResult => _) = _
  rw [Except.bind, hreserved]
  change Except.bind (Except.ok
      (0, ({ data := pdu, offset := 4 } : Cursor)))
    (fun reservedResult => _) = _
  rw [Except.bind, href]
  rfl

/-- Correlation extraction from every successfully encoded USER_DATA request
    returns the request's reference. -/
theorem decodePduReference_encodeUserDataHeader (reference : UInt16)
    (parameters data packet : ByteArray)
    (hparameters : parameters.size ≤ maxSectionSize)
    (hdata : data.size ≤ maxSectionSize)
    (hencode : encodeUserDataHeader reference parameters data = .ok packet) :
    decodePduReference packet = .ok reference := by
  rw [encodeUserDataHeader, if_neg (Nat.not_lt.mpr hparameters),
    if_neg (Nat.not_lt.mpr hdata)] at hencode
  injection hencode with hpacket
  subst packet
  simpa [ByteArray.append_assoc] using
    decodePduReference_header userDataType reference
      (uint16BE (UInt16.ofNat parameters.size) ++
        uint16BE (UInt16.ofNat data.size) ++ parameters ++ data)

/-- Correlation extraction from every successfully encoded S7 job returns the
    job's reference. -/
theorem decodePduReference_encodeJob (job : Job) (packet : ByteArray)
    (hparameters : job.parameters.size ≤ maxSectionSize)
    (hdata : job.data.size ≤ maxSectionSize)
    (hencode : encodeJob job = .ok packet) :
    decodePduReference packet = .ok job.reference := by
  rw [encodeJob, if_neg (Nat.not_lt.mpr hparameters),
    if_neg (Nat.not_lt.mpr hdata)] at hencode
  injection hencode with hpacket
  subst packet
  simpa [ByteArray.append_assoc] using decodePduReference_header jobType job.reference
    (uint16BE (UInt16.ofNat job.parameters.size) ++
      uint16BE (UInt16.ofNat job.data.size) ++ job.parameters ++ job.data)

/-- Correlation extraction from every successfully encoded ACK_DATA response
    returns the response reference. -/
theorem decodePduReference_encodeAckData (reference : UInt16)
    (parameters data packet : ByteArray)
    (hparameters : parameters.size ≤ maxSectionSize)
    (hdata : data.size ≤ maxSectionSize)
    (hencode : encodeAckData reference parameters data = .ok packet) :
    decodePduReference packet = .ok reference := by
  rw [encodeAckData, if_neg (Nat.not_lt.mpr hparameters),
    if_neg (Nat.not_lt.mpr hdata)] at hencode
  injection hencode with hpacket
  subst packet
  simpa [ByteArray.append_assoc] using decodePduReference_header ackDataType reference
    (uint16BE (UInt16.ofNat parameters.size) ++
      uint16BE (UInt16.ofNat data.size) ++ bytes #[0, 0] ++ parameters ++ data)

/-- What the correlation decoder reads: an accepted PDU starts with the protocol ID and
    carries the returned reference at offsets 4–5. Bytes 1–3 (the PDU kind and the
    reserved word) and everything after offset 6 are passed through unread. -/
theorem decodePduReference_canonical (pdu : ByteArray) (reference : UInt16)
    (h : decodePduReference pdu = .ok reference) :
    pdu = bytes #[protocolId] ++ pdu.extract 1 4 ++ uint16BE reference ++
      pdu.extract 6 pdu.size := by
  simp only [decodePduReference, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i xa va ea hid xb vb eb xc vc ec xd vd ed
  obtain ⟨la, da, na⟩ := Cursor.readUInt8_value _ _ _ ea
  rw [na] at eb
  obtain ⟨lb, db, nb⟩ := Cursor.readUInt8_value _ _ _ eb
  rw [nb] at ec
  obtain ⟨lc, dc, nc⟩ := Cursor.readUInt16BE_value _ _ _ ec
  rw [nc] at ed
  obtain ⟨ld, dd, nd⟩ := Cursor.readUInt16BE_value _ _ _ ed
  injection h with h
  subst h
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hid
  simp only at la lb lc ld da dd
  rw [dd, ← ByteArray.extract_two_uint16BE _ (0 + 1 + 1 + 2) (by omega), ← hid, ← da,
    show bytes #[pdu[0]] = pdu.extract 0 1 from (ByteArray.extract_one pdu 0 (by omega)).symm]
  rw [ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
    ByteArray.extract_zero_size]

inductive CpuState where
  | unknown
  | stopped
  | running
  deriving Repr, BEq

structure Szl where
  id : UInt16
  index : UInt16
  recordLength : UInt16
  recordCount : UInt16
  data : ByteArray
  deriving BEq

/-- Public typed parsers also accept caller-constructed SZLs, so they must not
    rely on the transport decoder having checked the declared record extent. -/
def validateSzlData (szl : Szl) : Except DecodeError Unit := do
  let expectedSize := szl.recordLength.toNat * szl.recordCount.toNat
  if szl.data.size != expectedSize then
    throw (.invalidField 0 s!"SZL records require {expectedSize} data bytes, got {szl.data.size}")

theorem validateSzlData_extent (szl : Szl) (h : validateSzlData szl = .ok ()) :
    szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat := by
  simp only [validateSzlData] at h
  split at h
  · contradiction
  · simp_all

def decodeSzlFirst (response : UserDataResponse) : Except DecodeError (UInt16 × UInt16 × ByteArray) := do
  let cursor : Cursor := { data := response.payload }
  let (id, cursor) ← cursor.readUInt16BE
  let (index, cursor) ← cursor.readUInt16BE
  let (payload, cursor) ← cursor.readBytes cursor.remaining
  cursor.finish
  return (id, index, payload)

def decodeSzl (id index : UInt16) (payload : ByteArray) : Except DecodeError Szl := do
  let cursor : Cursor := { data := payload }
  let (recordLength, cursor) ← cursor.readUInt16BE
  let (recordCount, cursor) ← cursor.readUInt16BE
  let (data, cursor) ← cursor.readBytes cursor.remaining
  cursor.finish
  let expectedDataSize := recordLength.toNat * recordCount.toNat
  if data.size != expectedDataSize then
    throw (.invalidField 4 s!"SZL header describes {expectedDataSize} data bytes, got {data.size}")
  return { id, index, recordLength, recordCount, data }

private def asciiField (data : ByteArray) (offset length : Nat) : Except DecodeError String := do
  let (field, _) ← ({ data, offset } : Cursor).readBytes length
  let trimmed := field.toList.reverse.dropWhile fun byte => byte == 0 || byte == 0x20
  return String.ofList <| trimmed.reverse.map fun byte => Char.ofNat byte.toNat

structure OrderCode where
  code : String
  versionMajor : UInt8
  versionMinor : UInt8
  versionPatch : UInt8
  deriving Repr, BEq

def parseOrderCode (szl : Szl) : Except DecodeError OrderCode := do
  validateSzlData szl
  if szl.id != 0x0011 then
    throw (.invalidField 0 s!"expected SZL 0x0011, got {szl.id}")
  if szl.recordLength < 26 || szl.recordCount == 0 then
    throw (.invalidField 0 "order-code SZL has no compatible records")
  let first := szl.data.extract 0 szl.recordLength.toNat
  let code ← asciiField first 2 20
  let versionOffset := szl.data.size - 3
  let cursor : Cursor := { data := szl.data, offset := versionOffset }
  let (versionMajor, cursor) ← cursor.readUInt8
  let (versionMinor, cursor) ← cursor.readUInt8
  let (versionPatch, _) ← cursor.readUInt8
  return { code, versionMajor, versionMinor, versionPatch }

structure CpuInfo where
  moduleTypeName : String
  serialNumber : String
  asName : String
  copyright : String
  moduleName : String
  deriving Repr, BEq

def parseCpuInfo (szl : Szl) : Except DecodeError CpuInfo := do
  validateSzlData szl
  if szl.id != 0x001c then
    throw (.invalidField 0 s!"expected SZL 0x001c, got {szl.id}")
  return {
    moduleTypeName := ← asciiField szl.data 172 32
    serialNumber := ← asciiField szl.data 138 24
    asName := ← asciiField szl.data 2 24
    copyright := ← asciiField szl.data 104 26
    moduleName := ← asciiField szl.data 36 24
  }

structure CpInfo where
  maxPduLength : UInt16
  maxConnections : UInt16
  maxMpiRate : UInt32
  maxBusRate : UInt32
  deriving Repr, BEq

def parseCpInfo (szl : Szl) : Except DecodeError CpInfo := do
  validateSzlData szl
  if szl.id != 0x0131 then
    throw (.invalidField 0 s!"expected SZL 0x0131, got {szl.id}")
  let cursor : Cursor := { data := szl.data, offset := 2 }
  let (maxPduLength, cursor) ← cursor.readUInt16BE
  let (maxConnections, cursor) ← cursor.readUInt16BE
  let (maxMpiRate, cursor) ← cursor.readUInt32BE
  let (maxBusRate, _) ← cursor.readUInt32BE
  return { maxPduLength, maxConnections, maxMpiRate, maxBusRate }

structure Protection where
  selectorPosition : UInt16
  passwordLevel : UInt16
  validProtectionLevel : UInt16
  modeSelector : UInt16
  startupSelector : UInt16
  deriving Repr, BEq

def parseProtection (szl : Szl) : Except DecodeError Protection := do
  validateSzlData szl
  if szl.id != 0x0232 then
    throw (.invalidField 0 s!"expected SZL 0x0232, got {szl.id}")
  let cursor : Cursor := { data := szl.data, offset := 2 }
  let (selectorPosition, cursor) ← cursor.readUInt16BE
  let (passwordLevel, cursor) ← cursor.readUInt16BE
  let (validProtectionLevel, cursor) ← cursor.readUInt16BE
  let (modeSelector, cursor) ← cursor.readUInt16BE
  let (startupSelector, _) ← cursor.readUInt16BE
  return { selectorPosition, passwordLevel, validProtectionLevel, modeSelector, startupSelector }

def parseCpuState (szl : Szl) : Except DecodeError CpuState := do
  validateSzlData szl
  if szl.id != 0x0424 then
    throw (.invalidField 0 s!"expected SZL 0x0424, got {szl.id}")
  let (status, _) ← ({ data := szl.data, offset := 3 } : Cursor).readUInt8
  return match status with
    | 0x08 => .running
    | 0x04 => .stopped
    | _ => .unknown

structure PlcDateTime where
  year : Nat
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
  millisecond : Nat := 0
  weekday : Nat
  deriving Repr, BEq

private def bcdEncode (value : Nat) : UInt8 := UInt8.ofNat ((value / 10) * 16 + value % 10)

private def bcdDecode (offset : Nat) (value : UInt8) : Except DecodeError Nat := do
  let high := value.toNat / 16
  let low := value.toNat % 16
  if high > 9 || low > 9 then
    throw (.invalidField offset s!"invalid BCD byte {value}")
  return high * 10 + low

private theorem bcdEncode_toNat (value : Nat) (h : value < 100) :
    (bcdEncode value).toNat = (value / 10) * 16 + value % 10 := by
  simp only [bcdEncode, UInt8.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

private theorem bcdDecode_encode (offset value : Nat) (h : value < 100) :
    bcdDecode offset (bcdEncode value) = .ok value := by
  have hhigh : ((value / 10) * 16 + value % 10) / 16 = value / 10 := by omega
  have hlow : ((value / 10) * 16 + value % 10) % 16 = value % 10 := by omega
  simp only [bcdDecode, bcdEncode_toNat value h, hhigh, hlow]
  have hhi : ¬value / 10 > 9 := by omega
  have hlo : ¬value % 10 > 9 := by omega
  simp [hhi, hlo]
  congr 1
  omega

private def isLeapYear (year : Nat) : Bool :=
  year % 400 == 0 || (year % 4 == 0 && year % 100 != 0)

private def daysInMonth (year month : Nat) : Nat :=
  match month with
  | 2 => if isLeapYear year then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | _ => 0

def PlcDateTime.validate (value : PlcDateTime) : Except DecodeError Unit := do
  if value.year < 1990 || value.year > 2089 then
    throw (.invalidField 0 "S7 DATE_AND_TIME year must be between 1990 and 2089")
  if value.month < 1 || value.month > 12 then
    throw (.invalidField 2 "month must be between 1 and 12")
  if value.day < 1 || value.day > daysInMonth value.year value.month then
    throw (.invalidField 3 "day is invalid for the selected month")
  if value.hour > 23 || value.minute > 59 || value.second > 59 then
    throw (.invalidField 4 "time of day is out of range")
  if value.millisecond > 999 then
    throw (.invalidField 7 "millisecond must be between 0 and 999")
  if value.weekday < 1 || value.weekday > 7 then
    throw (.invalidField 9 "weekday must be between 1 and 7")

def encodePlcDateTime (value : PlcDateTime) : Except DecodeError ByteArray := do
  value.validate
  let milliseconds := value.millisecond
  return bytes #[0, 0x19, bcdEncode (value.year % 100), bcdEncode value.month,
    bcdEncode value.day, bcdEncode value.hour, bcdEncode value.minute,
    bcdEncode value.second, bcdEncode (milliseconds / 10),
    UInt8.ofNat ((milliseconds % 10) * 16 + value.weekday)]

def decodePlcDateTime (payload : ByteArray) : Except DecodeError PlcDateTime := do
  if payload.size != 10 then
    throw (.invalidField 0 s!"clock payload must contain 10 bytes, got {payload.size}")
  let cursor : Cursor := { data := payload }
  let (_, cursor) ← cursor.readUInt8
  let (_, cursor) ← cursor.readUInt8
  let (yearByte, cursor) ← cursor.readUInt8
  let (monthByte, cursor) ← cursor.readUInt8
  let (dayByte, cursor) ← cursor.readUInt8
  let (hourByte, cursor) ← cursor.readUInt8
  let (minuteByte, cursor) ← cursor.readUInt8
  let (secondByte, cursor) ← cursor.readUInt8
  let (millisecondHigh, cursor) ← cursor.readUInt8
  let (millisecondLowAndWeekday, cursor) ← cursor.readUInt8
  cursor.finish
  if millisecondLowAndWeekday.toNat / 16 > 9 then
    throw (.invalidField 9 "invalid BCD millisecond digit")
  let yearLow ← bcdDecode 2 yearByte
  let value : PlcDateTime := {
    year := if yearLow < 90 then 2000 + yearLow else 1900 + yearLow
    month := ← bcdDecode 3 monthByte
    day := ← bcdDecode 4 dayByte
    hour := ← bcdDecode 5 hourByte
    minute := ← bcdDecode 6 minuteByte
    second := ← bcdDecode 7 secondByte
    millisecond := (← bcdDecode 8 millisecondHigh) * 10 + millisecondLowAndWeekday.toNat / 16
    weekday := millisecondLowAndWeekday.toNat % 16
  }
  value.validate
  return value

/-- Actual S7 clock codecs round trip every date accepted by calendar validation. -/
theorem decodePlcDateTime_encode (value : PlcDateTime)
    (valid : value.validate = .ok ()) :
    (encodePlcDateTime value >>= decodePlcDateTime) = .ok value := by
  have bounds : 1990 ≤ value.year ∧ value.year ≤ 2089 ∧
      1 ≤ value.month ∧ value.month ≤ 12 ∧
      1 ≤ value.day ∧ value.day ≤ daysInMonth value.year value.month ∧
      value.hour ≤ 23 ∧ value.minute ≤ 59 ∧ value.second ≤ 59 ∧
      value.millisecond ≤ 999 ∧ 1 ≤ value.weekday ∧ value.weekday ≤ 7 := by
    unfold PlcDateTime.validate at valid
    repeat first
      | split at valid
      | simp [bind, Except.bind, throw, pure, Except.pure] at valid
      | (simp only [Bool.or_eq_true, decide_eq_true_eq] at *; omega)
  have dayBound : value.day < 100 := by
    have monthBound : daysInMonth value.year value.month ≤ 31 := by
      unfold daysInMonth
      split <;> (try split) <;> omega
    omega
  have yearLow : value.year % 100 < 100 := Nat.mod_lt _ (by decide)
  have monthBound : value.month < 100 := by omega
  have hourBound : value.hour < 100 := by omega
  have minuteBound : value.minute < 100 := by omega
  have secondBound : value.second < 100 := by omega
  have milliBound : value.millisecond / 10 < 100 := by omega
  have tailBound : (value.millisecond % 10) * 16 + value.weekday < 256 := by omega
  have tailHigh : ((value.millisecond % 10) * 16 + value.weekday) / 16 =
      value.millisecond % 10 := by omega
  have tailLow : ((value.millisecond % 10) * 16 + value.weekday) % 16 =
      value.weekday := by omega
  have yearIdentity : (if value.year % 100 < 90 then 2000 + value.year % 100
      else 1900 + value.year % 100) = value.year := by split <;> omega
  have milliIdentity : (value.millisecond / 10) * 10 + value.millisecond % 10 =
      value.millisecond := by omega
  have tailDigit : ¬value.millisecond % 10 > 9 := by omega
  have weekdayBound : value.weekday < 16 := by omega
  simp only [encodePlcDateTime, valid, bind, Except.bind, pure, Except.pure]
  simp only [decodePlcDateTime, Cursor.readUInt8, Cursor.finish, bytes,
    ByteArray.size, bind, Except.bind, pure, Except.pure]
  simp [ByteArray.getElem_eq_getElem_data, -ByteArray.size_data,
    -UInt8.ofNat_add, -UInt8.ofNat_mul, Nat.mod_eq_of_lt tailBound,
    Nat.mod_eq_of_lt weekdayBound, tailHigh, tailDigit,
    bcdDecode_encode 2 _ yearLow, bcdDecode_encode 3 _ monthBound,
    bcdDecode_encode 4 _ dayBound, bcdDecode_encode 5 _ hourBound,
    bcdDecode_encode 6 _ minuteBound, bcdDecode_encode 7 _ secondBound,
    bcdDecode_encode 8 _ milliBound, yearIdentity, milliIdentity, valid]

/-- A byte `bcdDecode` accepts is the BCD encoding of the decoded value. -/
private theorem bcdDecode_canonical {offset : Nat} {value : UInt8} {n : Nat}
    (h : bcdDecode offset value = .ok n) : bcdEncode n = value ∧ n < 100 := by
  simp only [bcdDecode] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
  · rename_i hdigits
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hdigits
    have hv := value.toNat_lt
    refine ⟨?_, by omega⟩
    apply UInt8.toNat_inj.mp
    rw [bcdEncode_toNat _ (by omega)]
    omega

/-- Canonical decoding of the clock payload: every payload the decoder accepts is the
    encoding of the decoded value, except bytes 0–1. The decoder ignores those two
    bytes and the encoder writes `00 19` there. -/
theorem decodePlcDateTime_canonical (payload : ByteArray) (value : PlcDateTime)
    (h : decodePlcDateTime payload = .ok value) :
    encodePlcDateTime value = .ok (bytes #[0, 0x19] ++ payload.extract 2 10) := by
  simp only [decodePlcDateTime, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  all_goals
    rename_i hs x0 v0 e0 x1 v1 e1 x2 v2 e2 x3 v3 e3 x4 v4 e4 x5 v5 e5 x6 v6 e6 x7 v7 e7
      x8 v8 e8 x9 v9 e9 xf vf ef hms xy vy ey xm vm em xd vd ed xh vh eh xn vn en xs vs es
      xl vl el xv vv ev hyear
    obtain ⟨l0, d0, n0⟩ := Cursor.readUInt8_value _ _ _ e0
    rw [n0] at e1
    obtain ⟨l1, d1, n1⟩ := Cursor.readUInt8_value _ _ _ e1
    rw [n1] at e2
    obtain ⟨l2, d2, n2⟩ := Cursor.readUInt8_value _ _ _ e2
    rw [n2] at e3
    obtain ⟨l3, d3, n3⟩ := Cursor.readUInt8_value _ _ _ e3
    rw [n3] at e4
    obtain ⟨l4, d4, n4⟩ := Cursor.readUInt8_value _ _ _ e4
    rw [n4] at e5
    obtain ⟨l5, d5, n5⟩ := Cursor.readUInt8_value _ _ _ e5
    rw [n5] at e6
    obtain ⟨l6, d6, n6⟩ := Cursor.readUInt8_value _ _ _ e6
    rw [n6] at e7
    obtain ⟨l7, d7, n7⟩ := Cursor.readUInt8_value _ _ _ e7
    rw [n7] at e8
    obtain ⟨l8, d8, n8⟩ := Cursor.readUInt8_value _ _ _ e8
    rw [n8] at e9
    obtain ⟨l9, d9, n9⟩ := Cursor.readUInt8_value _ _ _ e9
    rw [n9] at ef
    have hfin := Cursor.finish_ok _ ef
    simp only at l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 hfin
    obtain ⟨cy, by'⟩ := bcdDecode_canonical ey
    obtain ⟨cm, bm⟩ := bcdDecode_canonical em
    obtain ⟨cd, bd⟩ := bcdDecode_canonical ed
    obtain ⟨ch, bh⟩ := bcdDecode_canonical eh
    obtain ⟨cn, bn⟩ := bcdDecode_canonical en
    obtain ⟨cs, bs⟩ := bcdDecode_canonical es
    obtain ⟨cl, bl⟩ := bcdDecode_canonical el
    injection h with h
    subst h
    have hvalid := ev
    first
      | rw [if_pos hyear] at hvalid
      | rw [if_neg hyear] at hvalid
    cases vv
    simp only [encodePlcDateTime, hvalid, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
    have hlow := v9.fst.toNat_lt
    first
      | (have hyearLow' : (2000 + vy) % 100 = vy := by omega
         rw [hyearLow'])
      | (have hyearLow' : (1900 + vy) % 100 = vy := by omega
         rw [hyearLow'])
    have hms10 : (vl * 10 + v9.fst.toNat / 16) / 10 = vl := by omega
    have hms1 : (vl * 10 + v9.fst.toNat / 16) % 10 = v9.fst.toNat / 16 := by omega
    have htail : UInt8.ofNat (v9.fst.toNat / 16 * 16 + v9.fst.toNat % 16) = v9.fst := by
      apply UInt8.toNat_inj.mp
      rw [UInt8.toNat_ofNat']
      omega
    rw [hms10, hms1, htail, cy, cm, cd, ch, cn, cs, cl, ← d2, ← d3, ← d4, ← d5, ← d6, ← d7, ← d8,
      ← d9]
    apply ByteArray.ext
    simp only [bytes, ByteArray.data_append, ByteArray.data_extract]
    apply Array.ext
    · simp; omega
    · intro i hi _
      simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
          i = 8 ∨ i = 9) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [Array.getElem_extract, ByteArray.getElem_eq_getElem_data]

def encodePassword (password : String) : Except DecodeError ByteArray := do
  let chars := password.toList
  if chars.isEmpty || chars.length > 8 then
    throw (.invalidField 0 "S7 session password must contain between 1 and 8 ASCII characters")
  let mut raw := ByteArray.mk (Array.replicate 8 0x20)
  for index in [0:chars.length] do
    let character := chars[index]!
    if character.toNat > 0x7f then
      throw (.invalidField index "S7 session password must be ASCII")
    raw := raw.set! index (UInt8.ofNat character.toNat)
  let mut encoded := ByteArray.empty
  for index in [0:8] do
    let prior := if index < 2 then 0 else encoded[index - 2]!
    encoded := encoded.push (UInt8.xor (UInt8.xor raw[index]! 0x55) prior)
  return encoded

def encodePlcStop (reference : UInt16) : Except EncodeError ByteArray :=
  encodeJob { reference, parameters := bytes #[stopFunction, 0, 0, 0, 0, 0, 9] ++
    "P_PROGRAM".toUTF8 }

def encodePlcHotStart (reference : UInt16) : Except EncodeError ByteArray :=
  encodeJob { reference, parameters := bytes #[startFunction, 0, 0, 0, 0, 0, 0, 0xfd,
    0, 0, 9] ++ "P_PROGRAM".toUTF8 }

def encodePlcColdStart (reference : UInt16) : Except EncodeError ByteArray :=
  encodeJob { reference, parameters := bytes #[startFunction, 0, 0, 0, 0, 0, 0, 0xfd,
    0, 2, 0x43, 0x20, 9] ++ "P_PROGRAM".toUTF8 }

def decodePlcControl (reference : UInt16) (function : UInt8) (response : Response) :
    Except DecodeError Unit := do
  validateResponse response reference function
  if response.parameters.size != 1 && response.parameters.size != 2 then
    throw (.invalidField responseHeaderSize "PLC control response must have one or two parameter bytes")
  if !response.data.isEmpty then
    throw (.invalidField (responseHeaderSize + response.parameters.size)
      "PLC control response must not contain data")

end LeanS7.S7
