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

def encodeUserDataHeader (reference : UInt16) (parameters data : ByteArray) :
    Except EncodeError ByteArray := do
  if parameters.size > maxSectionSize then
    throw (.parametersTooLarge parameters.size maxSectionSize)
  if data.size > maxSectionSize then
    throw (.dataTooLarge data.size maxSectionSize)
  return bytes #[protocolId, userDataType, 0, 0] ++ uint16BE reference ++
    uint16BE (UInt16.ofNat parameters.size) ++ uint16BE (UInt16.ofNat data.size) ++
    parameters ++ data

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
  let (error, parameterCursor) ← parameterCursor.readUInt16BE
  parameterCursor.finish
  if error != 0 then
    throw (.invalidField (jobHeaderSize + 10) s!"USER_DATA request failed with code {error}")
  if data.size < 4 then
    throw (.unexpectedEnd (jobHeaderSize + parameterLength.toNat) 4 data.size)
  let dataCursor : Cursor := { data }
  let (returnCode, dataCursor) ← dataCursor.readUInt8
  let (transportSize, dataCursor) ← dataCursor.readUInt8
  let (payloadLength, dataCursor) ← dataCursor.readUInt16BE
  if returnCode != 0xff then
    throw (.invalidField (jobHeaderSize + parameterLength.toNat)
      s!"USER_DATA item failed with code {returnCode}")
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
