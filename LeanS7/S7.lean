import LeanS7.Binary

namespace LeanS7.S7

def protocolId : UInt8 := 0x32
def jobType : UInt8 := 0x01
def ackType : UInt8 := 0x02
def ackDataType : UInt8 := 0x03
def readFunction : UInt8 := 0x04
def writeFunction : UInt8 := 0x05
def setupCommunicationFunction : UInt8 := 0xf0
def byteWordLength : UInt8 := 0x02
def counterWordLength : UInt8 := 0x1c
def timerWordLength : UInt8 := 0x1d
def byteTransportSize : UInt8 := 0x04
def octetTransportSize : UInt8 := 0x09
def jobHeaderSize : Nat := 10
def responseHeaderSize : Nat := 12
def maxSectionSize : Nat := 65535
def maxItemCount : Nat := 20

inductive EncodeError where
  | parametersTooLarge (size maximum : Nat)
  | dataTooLarge (size maximum : Nat)
  | invalidSize (size : Nat)
  | invalidPayloadSize (actual expected : Nat)
  | invalidDbNumber (dbNumber : UInt16)
  | misalignedAddress (start alignment : Nat)
  | addressTooLarge (start : Nat)
  deriving Repr, BEq

structure Job where
  reference : UInt16
  parameters : ByteArray
  data : ByteArray := ByteArray.empty
  deriving BEq

/-- Encode the common header and sections of an S7 job PDU. -/
def encodeJob (job : Job) : Except EncodeError ByteArray := do
  if job.parameters.size > maxSectionSize then
    throw (.parametersTooLarge job.parameters.size maxSectionSize)
  if job.data.size > maxSectionSize then
    throw (.dataTooLarge job.data.size maxSectionSize)
  let header := bytes #[protocolId, jobType, 0, 0] ++
    uint16BE job.reference ++
    uint16BE (UInt16.ofNat job.parameters.size) ++
    uint16BE (UInt16.ofNat job.data.size)
  return header ++ job.parameters ++ job.data

structure SetupCommunication where
  maxAmqCaller : UInt16 := 1
  maxAmqCallee : UInt16 := 1
  pduLength : UInt16 := 480
  deriving Repr, BEq

def encodeSetupCommunication (reference : UInt16) (setup : SetupCommunication := {}) : Except EncodeError ByteArray :=
  let parameters := bytes #[setupCommunicationFunction, 0] ++
    uint16BE setup.maxAmqCaller ++
    uint16BE setup.maxAmqCallee ++
    uint16BE setup.pduLength
  encodeJob { reference, parameters }

structure Response where
  pduType : UInt8
  reference : UInt16
  parameters : ByteArray
  data : ByteArray
  errorClass : UInt8
  errorCode : UInt8
  deriving BEq

def decodeResponse (pdu : ByteArray) : Except DecodeError Response := do
  let cursor : Cursor := { data := pdu }
  let (actualProtocolId, cursor) ← cursor.readUInt8
  if actualProtocolId != protocolId then
    throw (.invalidField 0 s!"expected S7 protocol ID 0x32, got {actualProtocolId}")
  let (pduType, cursor) ← cursor.readUInt8
  if pduType != ackType && pduType != ackDataType then
    throw (.invalidField 1 s!"expected S7 ACK or ACK_DATA, got {pduType}")
  let (_, cursor) ← cursor.readUInt16BE
  let (reference, cursor) ← cursor.readUInt16BE
  let (parameterLength, cursor) ← cursor.readUInt16BE
  let (dataLength, cursor) ← cursor.readUInt16BE
  let (errorClass, cursor) ← cursor.readUInt8
  let (errorCode, cursor) ← cursor.readUInt8
  let expected := responseHeaderSize + parameterLength.toNat + dataLength.toNat
  if expected != pdu.size then
    throw (.invalidField 6 s!"S7 section lengths require {expected} bytes, got {pdu.size}")
  let (parameters, cursor) ← cursor.readBytes parameterLength.toNat
  let (data, cursor) ← cursor.readBytes dataLength.toNat
  cursor.finish
  return { pduType, reference, parameters, data, errorClass, errorCode }

def validateResponse (response : Response) (reference : UInt16) (function : UInt8) : Except DecodeError Unit := do
  if response.reference != reference then
    throw (.invalidField 4 s!"expected PDU reference {reference}, got {response.reference}")
  if response.errorClass != 0 || response.errorCode != 0 then
    throw (.invalidField 10 s!"PLC error {response.errorClass}:{response.errorCode}")
  let (actualFunction, _) ← ({ data := response.parameters } : Cursor).readUInt8
  if actualFunction != function then
    throw (.invalidField responseHeaderSize "unexpected S7 response function")

def decodeSetupCommunication (reference : UInt16) (response : Response) : Except DecodeError SetupCommunication := do
  validateResponse response reference setupCommunicationFunction
  if response.parameters.size != 8 then
    throw (.invalidField responseHeaderSize "setup-communication parameters must be eight bytes")
  let cursor : Cursor := { data := response.parameters, offset := 2 }
  let (maxAmqCaller, cursor) ← cursor.readUInt16BE
  let (maxAmqCallee, cursor) ← cursor.readUInt16BE
  let (pduLength, cursor) ← cursor.readUInt16BE
  cursor.finish
  if pduLength < 240 then
    throw (.invalidField (responseHeaderSize + 6) s!"negotiated PDU length is too small: {pduLength}")
  return { maxAmqCaller, maxAmqCallee, pduLength }

inductive Area where
  | processInputs
  | processOutputs
  | markers
  | dataBlocks
  | counters
  | timers
  deriving Repr, BEq

def Area.code : Area → UInt8
  | .processInputs => 0x81
  | .processOutputs => 0x82
  | .markers => 0x83
  | .dataBlocks => 0x84
  | .counters => 0x1c
  | .timers => 0x1d

def Area.wordLength : Area → UInt8
  | .counters => counterWordLength
  | .timers => timerWordLength
  | _ => byteWordLength

def Area.elementSize : Area → Nat
  | .counters | .timers => 2
  | _ => 1

def Area.usesElementAddress : Area → Bool
  | .counters | .timers => true
  | _ => false

def Area.dataTransportSize : Area → UInt8
  | .counters | .timers => octetTransportSize
  | _ => byteTransportSize

/-- A memory-area range. `start` is a byte offset; timers and counters require
    two-byte alignment, while `count` is the number of timer/counter elements. -/
structure MemoryRange where
  area : Area
  dbNumber : UInt16
  start : Nat
  count : Nat
  deriving Repr, BEq

inductive ReadItemResult where
  | success (payload : ByteArray)
  | failure (returnCode : UInt8)
  deriving BEq

structure WriteItem where
  range : MemoryRange
  payload : ByteArray
  deriving BEq

inductive WriteItemResult where
  | success
  | failure (returnCode : UInt8)
  deriving Repr, BEq

def encodeMemoryAddress (range : MemoryRange) : Except EncodeError ByteArray := do
  if range.count == 0 || range.count > maxSectionSize then
    throw (.invalidSize range.count)
  if range.area != .dataBlocks && range.dbNumber != 0 then
    throw (.invalidDbNumber range.dbNumber)
  if range.area.usesElementAddress && range.start % range.area.elementSize != 0 then
    throw (.misalignedAddress range.start range.area.elementSize)
  let address := if range.area.usesElementAddress then range.start else range.start * 8
  let lastAddress := if range.area.usesElementAddress then
    range.start + (range.count - 1) * range.area.elementSize
  else
    (range.start + range.count * range.area.elementSize - 1) * 8
  if address > 0xffffff || lastAddress > 0xffffff then
    throw (.addressTooLarge range.start)
  let dbNumber := if range.area == .dataBlocks then range.dbNumber else 0
  return bytes #[0x12, 0x0a, 0x10, range.area.wordLength] ++
    uint16BE (UInt16.ofNat range.count) ++ uint16BE dbNumber ++
    bytes #[range.area.code] ++ uint24BE (UInt32.ofNat address)

def encodeAreaRead (reference : UInt16) (range : MemoryRange) : Except EncodeError ByteArray := do
  let address ← encodeMemoryAddress range
  encodeJob { reference, parameters := bytes #[readFunction, 1] ++ address }

def encodeAreaReadMany (reference : UInt16) (ranges : Array MemoryRange) : Except EncodeError ByteArray := do
  if ranges.isEmpty || ranges.size > maxItemCount then
    throw (.invalidSize ranges.size)
  let mut parameters := bytes #[readFunction, UInt8.ofNat ranges.size]
  for range in ranges do
    parameters := parameters ++ (← encodeMemoryAddress range)
  encodeJob { reference, parameters }

def encodeAreaWrite (reference : UInt16) (range : MemoryRange)
    (payload : ByteArray) : Except EncodeError ByteArray := do
  let address ← encodeMemoryAddress range
  let expectedSize := range.count * range.area.elementSize
  if payload.size != expectedSize then
    throw (.invalidPayloadSize payload.size expectedSize)
  let dataLength := if range.area.dataTransportSize == octetTransportSize then
    payload.size
  else
    payload.size * 8
  if dataLength > maxSectionSize then
    throw (.invalidSize payload.size)
  let data := bytes #[0, range.area.dataTransportSize] ++
    uint16BE (UInt16.ofNat dataLength) ++ payload
  encodeJob { reference, parameters := bytes #[writeFunction, 1] ++ address, data }

def encodeAreaWriteMany (reference : UInt16) (items : Array WriteItem) : Except EncodeError ByteArray := do
  if items.isEmpty || items.size > maxItemCount then
    throw (.invalidSize items.size)
  let mut parameters := bytes #[writeFunction, UInt8.ofNat items.size]
  let mut data := ByteArray.empty
  let mut index := 0
  for item in items do
    let address ← encodeMemoryAddress item.range
    parameters := parameters ++ address
    let expectedSize := item.range.count * item.range.area.elementSize
    if item.payload.size != expectedSize then
      throw (.invalidPayloadSize item.payload.size expectedSize)
    let dataLength := if item.range.area.dataTransportSize == octetTransportSize then
      item.payload.size
    else
      item.payload.size * 8
    if dataLength > maxSectionSize then
      throw (.invalidSize item.payload.size)
    data := data ++ bytes #[0, item.range.area.dataTransportSize] ++
      uint16BE (UInt16.ofNat dataLength) ++ item.payload
    if index + 1 < items.size && item.payload.size % 2 != 0 then
      data := data ++ bytes #[0]
    index := index + 1
  encodeJob { reference, parameters, data }

structure DbRange where
  dbNumber : UInt16
  start : Nat
  size : Nat
  deriving Repr, BEq

def encodeDbRead (reference : UInt16) (range : DbRange) : Except EncodeError ByteArray := do
  encodeAreaRead reference {
    area := .dataBlocks
    dbNumber := range.dbNumber
    start := range.start
    count := range.size
  }

def encodeDbWrite (reference : UInt16) (dbNumber : UInt16) (start : Nat)
    (payload : ByteArray) : Except EncodeError ByteArray := do
  encodeAreaWrite reference {
    area := .dataBlocks
    dbNumber
    start
    count := payload.size
  } payload

def decodeAreaRead (reference : UInt16) (area : Area) (expectedSize : Nat)
    (response : Response) : Except DecodeError ByteArray := do
  validateResponse response reference readFunction
  if response.parameters.size != 2 then
    throw (.invalidField responseHeaderSize "expected one read response item")
  let parameterCursor : Cursor := { data := response.parameters, offset := 1 }
  let (itemCount, parameterCursor) ← parameterCursor.readUInt8
  parameterCursor.finish
  if itemCount != 1 then
    throw (.invalidField (responseHeaderSize + 1) "expected one read response item")
  if response.data.size < 4 then
    throw (.unexpectedEnd (responseHeaderSize + 2) 4 response.data.size)
  let cursor : Cursor := { data := response.data }
  let (returnCode, cursor) ← cursor.readUInt8
  if returnCode != 0xff then
    throw (.invalidField (responseHeaderSize + 2) s!"read item failed with code {returnCode}")
  let (transportSize, cursor) ← cursor.readUInt8
  let compatibleByteEncoding := area.usesElementAddress && transportSize == byteTransportSize
  if transportSize != area.dataTransportSize && !compatibleByteEncoding then
    throw (.invalidField (responseHeaderSize + 3) s!"unexpected read transport size {transportSize}")
  let (encodedLength, cursor) ← cursor.readUInt16BE
  let payloadSize ← if transportSize == octetTransportSize then
    pure encodedLength.toNat
  else if encodedLength.toNat % 8 != 0 then
    throw (.invalidField (responseHeaderSize + 4) "read response bit length is not byte aligned")
  else
    pure (encodedLength.toNat / 8)
  if payloadSize != expectedSize then
    throw (.invalidField (responseHeaderSize + 4)
      s!"expected {expectedSize} response bytes, got {payloadSize}")
  let (payload, cursor) ← cursor.readBytes payloadSize
  cursor.finish
  return payload

private def validateItemParameters (response : Response) (reference : UInt16)
    (function : UInt8) (expectedCount : Nat) : Except DecodeError Unit := do
  validateResponse response reference function
  if response.parameters.size != 2 then
    throw (.invalidField responseHeaderSize "expected two-byte item response parameters")
  let cursor : Cursor := { data := response.parameters, offset := 1 }
  let (actualCount, cursor) ← cursor.readUInt8
  cursor.finish
  if actualCount.toNat != expectedCount then
    throw (.invalidField (responseHeaderSize + 1)
      s!"expected {expectedCount} response items, got {actualCount}")

private def responsePayloadSize (transportSize : UInt8) (encodedLength : UInt16)
    (offset : Nat) : Except DecodeError Nat := do
  if transportSize == octetTransportSize then
    return encodedLength.toNat
  if encodedLength.toNat % 8 != 0 then
    throw (.invalidField offset "response bit length is not byte aligned")
  return encodedLength.toNat / 8

private def decodeReadItems : List MemoryRange → Cursor → Except DecodeError (List ReadItemResult × Cursor)
  | [], cursor => pure ([], cursor)
  | range :: rest, cursor => do
      let itemOffset := responseHeaderSize + 2 + cursor.offset
      let (returnCode, cursor) ← cursor.readUInt8
      let (transportSize, cursor) ← cursor.readUInt8
      let (encodedLength, cursor) ← cursor.readUInt16BE
      let payloadSize ← responsePayloadSize transportSize encodedLength (itemOffset + 2)
      let (payload, cursor) ← cursor.readBytes payloadSize
      let cursor ← if !rest.isEmpty && payloadSize % 2 != 0 then
        let (_, cursor) ← cursor.readUInt8
        pure cursor
      else
        pure cursor
      let result ← if returnCode == 0xff then
        let compatibleByteEncoding := range.area.usesElementAddress && transportSize == byteTransportSize
        if transportSize != range.area.dataTransportSize && !compatibleByteEncoding then
          throw (.invalidField (itemOffset + 1) s!"unexpected read transport size {transportSize}")
        let expectedSize := range.count * range.area.elementSize
        if payloadSize != expectedSize then
          throw (.invalidField (itemOffset + 2)
            s!"expected {expectedSize} response bytes, got {payloadSize}")
        pure (.success payload)
      else
        pure (.failure returnCode)
      let (results, cursor) ← decodeReadItems rest cursor
      return (result :: results, cursor)

def decodeAreaReadMany (reference : UInt16) (ranges : Array MemoryRange)
    (response : Response) : Except DecodeError (Array ReadItemResult) := do
  if ranges.isEmpty || ranges.size > maxItemCount then
    throw (.invalidField responseHeaderSize s!"invalid expected item count {ranges.size}")
  validateItemParameters response reference readFunction ranges.size
  let (results, cursor) ← decodeReadItems ranges.toList { data := response.data }
  cursor.finish
  return results.toArray

private def decodeWriteItems : Nat → Cursor → Except DecodeError (List WriteItemResult × Cursor)
  | 0, cursor => pure ([], cursor)
  | count + 1, cursor => do
      let (returnCode, cursor) ← cursor.readUInt8
      let result := if returnCode == 0xff then WriteItemResult.success else .failure returnCode
      let (results, cursor) ← decodeWriteItems count cursor
      return (result :: results, cursor)

def decodeAreaWriteMany (reference : UInt16) (expectedCount : Nat)
    (response : Response) : Except DecodeError (Array WriteItemResult) := do
  if expectedCount == 0 || expectedCount > maxItemCount then
    throw (.invalidField responseHeaderSize s!"invalid expected item count {expectedCount}")
  validateItemParameters response reference writeFunction expectedCount
  let (results, cursor) ← decodeWriteItems expectedCount { data := response.data }
  cursor.finish
  return results.toArray

def decodeDbRead (reference : UInt16) (response : Response) : Except DecodeError ByteArray := do
  validateResponse response reference readFunction
  if response.data.size < 4 then
    throw (.unexpectedEnd (responseHeaderSize + 2) 4 response.data.size)
  let lengthCursor : Cursor := { data := response.data, offset := 2 }
  let (bitLength, _) ← lengthCursor.readUInt16BE
  if bitLength.toNat % 8 != 0 then
    throw (.invalidField (responseHeaderSize + 4) "read response bit length is not byte aligned")
  decodeAreaRead reference .dataBlocks (bitLength.toNat / 8) response

def decodeDbWrite (reference : UInt16) (response : Response) : Except DecodeError Unit := do
  validateResponse response reference writeFunction
  if response.parameters.size != 2 then
    throw (.invalidField responseHeaderSize "expected one write response item")
  let parameterCursor : Cursor := { data := response.parameters, offset := 1 }
  let (itemCount, parameterCursor) ← parameterCursor.readUInt8
  parameterCursor.finish
  if itemCount != 1 then
    throw (.invalidField (responseHeaderSize + 1) "expected one write response item")
  if response.data.size != 1 then
    throw (.invalidField (responseHeaderSize + 2) "write item was not acknowledged")
  let (returnCode, dataCursor) ← ({ data := response.data } : Cursor).readUInt8
  dataCursor.finish
  if returnCode != 0xff then
    throw (.invalidField (responseHeaderSize + 2) s!"write item failed with code {returnCode}")

end LeanS7.S7
