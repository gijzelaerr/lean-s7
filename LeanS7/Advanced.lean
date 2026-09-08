import LeanS7.Management

namespace LeanS7.S7

def blocksInfoGroup : UInt8 := 0x03
def listBlocksSubfunction : UInt8 := 0x01
def listBlocksOfTypeSubfunction : UInt8 := 0x02
def blockInfoSubfunction : UInt8 := 0x03
def startUploadFunction : UInt8 := 0x1d
def uploadFunction : UInt8 := 0x1e
def endUploadFunction : UInt8 := 0x1f
def requestDownloadFunction : UInt8 := 0x1a
def downloadFunction : UInt8 := 0x1b
def downloadEndedFunction : UInt8 := 0x1c

inductive BlockType where
  | organizationBlock
  | dataBlock
  | systemDataBlock
  | function
  | systemFunction
  | functionBlock
  | systemFunctionBlock
  deriving Repr, BEq

def BlockType.code : BlockType → UInt8
  | .organizationBlock => 0x38
  | .dataBlock => 0x41
  | .systemDataBlock => 0x42
  | .function => 0x43
  | .systemFunction => 0x44
  | .functionBlock => 0x45
  | .systemFunctionBlock => 0x46

def BlockType.ofCode : UInt8 → Option BlockType
  | 0x38 => some .organizationBlock
  | 0x41 => some .dataBlock
  | 0x42 => some .systemDataBlock
  | 0x43 => some .function
  | 0x44 => some .systemFunction
  | 0x45 => some .functionBlock
  | 0x46 => some .systemFunctionBlock
  | _ => none

structure BlockCounts where
  organizationBlocks : UInt16 := 0
  dataBlocks : UInt16 := 0
  systemDataBlocks : UInt16 := 0
  functions : UInt16 := 0
  systemFunctions : UInt16 := 0
  functionBlocks : UInt16 := 0
  systemFunctionBlocks : UInt16 := 0
  deriving Repr, BEq

private def decimalDigit (value divisor : Nat) : UInt8 :=
  UInt8.ofNat ((value / divisor) % 10 + 0x30)

def decimal5 (value : Nat) : Except EncodeError ByteArray := do
  if value > 99999 then throw (.invalidSize value)
  return bytes #[decimalDigit value 10000, decimalDigit value 1000,
    decimalDigit value 100, decimalDigit value 10, decimalDigit value 1]

def decimal6 (value : Nat) : Except EncodeError ByteArray := do
  if value > 999999 then throw (.invalidSize value)
  return bytes #[decimalDigit value 100000, decimalDigit value 10000,
    decimalDigit value 1000, decimalDigit value 100, decimalDigit value 10,
    decimalDigit value 1]

def encodeListBlocks (reference : UInt16) : Except EncodeError ByteArray :=
  encodeUserDataHeader reference
    (userDataParameters blocksInfoGroup listBlocksSubfunction 0 false)
    (bytes #[0x0a, 0, 0, 0])

def encodeListBlocksOfType (reference : UInt16) (blockType : BlockType) :
    Except EncodeError ByteArray :=
  encodeUserDataHeader reference
    (userDataParameters blocksInfoGroup listBlocksOfTypeSubfunction 0 false)
    (bytes #[0xff, octetTransportSize, 0, 2, 0x30, blockType.code])

def encodeUserDataContinuation (reference : UInt16) (group subfunction sequence : UInt8) :
    Except EncodeError ByteArray :=
  encodeUserDataHeader reference
    (bytes #[0, 1, 0x12, 0x08, userDataRequestMethod,
      UInt8.lor userDataRequestType group, subfunction, sequence, 0, 0, 0, 0])
    (bytes #[0x0a, 0, 0, 0])

def encodeGetBlockInfo (reference : UInt16) (blockType : BlockType) (number : Nat) :
    Except EncodeError ByteArray := do
  let numberBytes ← decimal5 number
  encodeUserDataHeader reference
    (userDataParameters blocksInfoGroup blockInfoSubfunction 0 false)
    (bytes #[0xff, octetTransportSize, 0, 8, 0x30, blockType.code, 0x41] ++ numberBytes)

def decodeBlockCounts (payload : ByteArray) : Except DecodeError BlockCounts := do
  if payload.size != 28 then
    throw (.invalidField 0 s!"block-count response must contain 28 bytes, got {payload.size}")
  let mut cursor : Cursor := { data := payload }
  let mut result : BlockCounts := {}
  for _ in [0:7] do
    let (markerPrefix, next) ← cursor.readUInt8
    cursor := next
    if markerPrefix != 0x30 then throw (.invalidField (cursor.offset - 1) "invalid block-count prefix")
    let (typeCode, next) ← cursor.readUInt8
    cursor := next
    let (count, next) ← cursor.readUInt16BE
    cursor := next
    let some blockType := BlockType.ofCode typeCode
      | throw (.invalidField (cursor.offset - 3) s!"unknown block type {typeCode}")
    result := match blockType with
      | .organizationBlock => { result with organizationBlocks := count }
      | .dataBlock => { result with dataBlocks := count }
      | .systemDataBlock => { result with systemDataBlocks := count }
      | .function => { result with functions := count }
      | .systemFunction => { result with systemFunctions := count }
      | .functionBlock => { result with functionBlocks := count }
      | .systemFunctionBlock => { result with systemFunctionBlocks := count }
  cursor.finish
  return result

structure BlockEntry where
  number : UInt16
  flags : UInt8
  language : UInt8
  deriving Repr, BEq, Inhabited

def decodeBlockEntries (payload : ByteArray) : Except DecodeError (Array BlockEntry) := do
  if payload.size % 4 != 0 then
    throw (.invalidField 0 "block-list payload is not aligned to four-byte entries")
  let mut cursor : Cursor := { data := payload }
  let mut result := #[]
  for _ in [0:payload.size / 4] do
    let (number, next) ← cursor.readUInt16BE
    cursor := next
    let (flags, next) ← cursor.readUInt8
    cursor := next
    let (language, next) ← cursor.readUInt8
    cursor := next
    result := result.push { number, flags, language }
  cursor.finish
  return result

structure BlockInfo where
  blockType : UInt8
  number : UInt16
  language : UInt8
  flags : UInt8
  mc7Size : UInt16
  loadSize : UInt32
  localDataSize : UInt16
  sbbSize : UInt16
  checksum : UInt16
  version : UInt8
  codeDateRaw : ByteArray
  interfaceDateRaw : ByteArray
  author : String
  family : String
  name : String
  deriving BEq

structure ForceEntry where
  areaCode : UInt16
  byteOffset : UInt16
  bit : UInt8
  value : Bool
  deriving Repr, BEq, Inhabited

def decodeForceTable (szl : Szl) : Except DecodeError (Array ForceEntry) := do
  if szl.id != 0x0025 then
    throw (.invalidField 0 s!"expected force-table SZL 0x0025, got {szl.id}")
  if szl.data.size % 8 != 0 then
    throw (.invalidField 0 "force-table data is not aligned to eight-byte entries")
  let mut cursor : Cursor := { data := szl.data }
  let mut result := #[]
  for _ in [0:szl.data.size / 8] do
    let (areaCode, next) ← cursor.readUInt16BE
    cursor := next
    let (byteOffset, next) ← cursor.readUInt16BE
    cursor := next
    let (bit, next) ← cursor.readUInt8
    cursor := next
    if bit > 7 then throw (.invalidField (cursor.offset - 1) "force-table bit index exceeds 7")
    let (value, next) ← cursor.readUInt8
    cursor := next
    let (_, next) ← cursor.readUInt16BE
    cursor := next
    result := result.push { areaCode, byteOffset, bit, value := value != 0 }
  cursor.finish
  return result

private def fixedAscii (data : ByteArray) (offset length : Nat) : Except DecodeError String := do
  let (field, _) ← ({ data, offset } : Cursor).readBytes length
  let trimmed := field.toList.reverse.dropWhile fun byte => byte == 0 || byte == 0x20
  return String.ofList <| trimmed.reverse.map fun byte => Char.ofNat byte.toNat

def decodeBlockInfo (payload : ByteArray) : Except DecodeError BlockInfo := do
  if payload.size < 78 then
    throw (.unexpectedEnd 0 78 payload.size)
  let byteAt (offset : Nat) := (Cursor.readUInt8 { data := payload, offset }).map Prod.fst
  let wordAt (offset : Nat) := (Cursor.readUInt16BE { data := payload, offset }).map Prod.fst
  let dwordAt (offset : Nat) := (Cursor.readUInt32BE { data := payload, offset }).map Prod.fst
  return {
    blockType := ← byteAt 1
    flags := ← byteAt 9
    language := ← byteAt 10
    number := ← wordAt 12
    loadSize := ← dwordAt 14
    sbbSize := ← wordAt 34
    localDataSize := ← wordAt 38
    mc7Size := ← wordAt 40
    codeDateRaw := payload.extract 22 28
    interfaceDateRaw := payload.extract 28 34
    author := ← fixedAscii payload 42 8
    family := ← fixedAscii payload 50 8
    name := ← fixedAscii payload 58 8
    version := ← byteAt 66
    checksum := ← wordAt 68
  }

def encodeStartUpload (reference : UInt16) (blockType : BlockType) (number : Nat) :
    Except EncodeError ByteArray := do
  let numberBytes ← decimal5 number
  encodeJob { reference, parameters :=
    (bytes #[startUploadFunction, 0, 0, 0, 0, 0, 0, 0, 9, 0x5f, 0x30, blockType.code] ++
      numberBytes ++ bytes #[0x41]) }

def encodeUpload (reference : UInt16) (uploadId : UInt8) : Except EncodeError ByteArray :=
  encodeJob { reference, parameters := bytes #[uploadFunction, 0, 0, 0, 0, 0, 0, uploadId] }

def encodeEndUpload (reference : UInt16) (uploadId : UInt8) : Except EncodeError ByteArray :=
  encodeJob { reference, parameters := bytes #[endUploadFunction, 0, 0, 0, 0, 0, 0, uploadId] }

structure StartUploadResponse where
  uploadId : UInt8
  loadSize : Option Nat
  deriving Repr, BEq

private def asciiNat (offset : Nat) (data : ByteArray) : Except DecodeError Nat := do
  let mut value := 0
  for index in [0:data.size] do
    let byte := data[index]!
    if byte < 0x30 || byte > 0x39 then
      throw (.invalidField (offset + index) "expected an ASCII decimal digit")
    value := value * 10 + byte.toNat - 0x30
  return value

def decodeStartUpload (reference : UInt16) (response : Response) : Except DecodeError StartUploadResponse := do
  validateResponse response reference startUploadFunction
  if response.parameters.size < 8 then
    throw (.unexpectedEnd responseHeaderSize 8 response.parameters.size)
  let (uploadId, _) ← ({ data := response.parameters, offset := 7 } : Cursor).readUInt8
  let loadSize ← if response.parameters.size >= 16 then
    some <$> asciiNat (responseHeaderSize + 11) (response.parameters.extract 11 16)
  else pure none
  return { uploadId, loadSize }

structure UploadFragment where
  isLast : Bool
  data : ByteArray
  deriving BEq

def decodeUploadFragment (reference : UInt16) (response : Response) : Except DecodeError UploadFragment := do
  validateResponse response reference uploadFunction
  if response.parameters.size != 2 then
    throw (.invalidField responseHeaderSize "upload response parameters must contain two bytes")
  let (endOfUpload, _) ← ({ data := response.parameters, offset := 1 } : Cursor).readUInt8
  let cursor : Cursor := { data := response.data }
  let (declaredLength, cursor) ← cursor.readUInt16BE
  let (marker, cursor) ← cursor.readUInt16BE
  if marker != 0x00fb then
    throw (.invalidField (responseHeaderSize + response.parameters.size + 2)
      "invalid upload data marker")
  if declaredLength.toNat + 4 != response.data.size then
    throw (.invalidField (responseHeaderSize + response.parameters.size)
      "upload data length does not match its section")
  let (data, cursor) ← cursor.readBytes declaredLength.toNat
  cursor.finish
  return { isLast := endOfUpload == 0, data }

def decodeEndUpload (reference : UInt16) (response : Response) : Except DecodeError Unit := do
  validateResponse response reference endUploadFunction
  if response.parameters.size != 1 || !response.data.isEmpty then
    throw (.invalidField responseHeaderSize "invalid end-upload response")

def encodeDeleteBlock (reference : UInt16) (blockType : BlockType) (number : Nat) :
    Except EncodeError ByteArray := do
  let numberBytes ← decimal5 number
  encodeJob { reference, parameters :=
    (bytes #[startFunction, 0, 0, 0, 0, 0, 0, 0xfd, 0, 10, 1, 0, 0x30, blockType.code] ++
      numberBytes ++ bytes #[0x42, 5] ++ "_DELE".toUTF8) }

def encodeInsertBlock (reference : UInt16) (blockType : BlockType) (number : Nat) :
    Except EncodeError ByteArray := do
  let numberBytes ← decimal5 number
  encodeJob { reference, parameters :=
    (bytes #[startFunction, 0, 0, 0, 0, 0, 0, 0xfd, 0, 10, 1, 0, 0x30, blockType.code] ++
      numberBytes ++ bytes #[0x50, 5] ++ "_INSE".toUTF8) }

def encodeCompress (reference : UInt16) : Except EncodeError ByteArray :=
  encodeJob { reference, parameters :=
    (bytes #[startFunction, 0, 0, 0, 0, 0, 0, 0xfd, 0, 0, 5] ++ "_GARB".toUTF8) }

def encodeCopyRamToRom (reference : UInt16) : Except EncodeError ByteArray :=
  encodeJob { reference, parameters :=
    (bytes #[startFunction, 0, 0, 0, 0, 0, 0, 0xfd, 0, 2, 0x45, 0x50, 5] ++ "_MODU".toUTF8) }

abbrev JobPdu := Job

/-- Compatibility name for the proved, strict core S7 job decoder. -/
def decodeJobPdu (pdu : ByteArray) : Except DecodeError JobPdu :=
  decodeJob pdu

def encodeRequestDownload (reference : UInt16) (blockType : BlockType) (number loadSize mc7Size : Nat) :
    Except EncodeError ByteArray := do
  let numberBytes ← decimal5 number
  let loadBytes ← decimal6 loadSize
  let mc7Bytes ← decimal6 mc7Size
  encodeJob { reference, parameters :=
    (bytes #[requestDownloadFunction, 0, 1, 0, 0, 0, 0, 0, 9, 0x5f, 0x30, blockType.code] ++
      numberBytes ++ bytes #[0x50, 0x0d, 0x31] ++ loadBytes ++ mc7Bytes) }

def encodeDownloadFragmentResponse (reference : UInt16) (isLast : Bool)
    (payload : ByteArray) : Except EncodeError ByteArray :=
  encodeAckData reference (bytes #[downloadFunction, if isLast then 0 else 1])
    (uint16BE (UInt16.ofNat payload.size) ++ bytes #[0, 0xfb] ++ payload)

def encodeDownloadEndedResponse (reference : UInt16) : Except EncodeError ByteArray :=
  encodeAckData reference (bytes #[downloadEndedFunction]) ByteArray.empty

end LeanS7.S7
