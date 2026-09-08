import LeanS7.Binary

namespace LeanS7.Value

inductive Error where
  | decode (error : DecodeError)
  | invalidBitIndex (index : Nat)
  | invalidMaximumLength (maximum limit : Nat)
  | valueTooLong (actual maximum : Nat)
  | invalidCharacter (codePoint : Nat)
  | invalidStringHeader (current maximum : Nat)
  | invalidUtf16 (offset : Nat) (message : String)
  deriving Repr, BEq

def maxStringLength : Nat := 254
def maxWStringLength : Nat := 16382

private def fromDecode (result : Except DecodeError α) : Except Error α :=
  result.mapError Error.decode

private def cursorAt (data : ByteArray) (offset : Nat) : Cursor :=
  { data, offset }

def getUInt8 (data : ByteArray) (offset : Nat := 0) : Except Error UInt8 := do
  let (value, _) ← fromDecode <| (cursorAt data offset).readUInt8
  return value

def getUInt16 (data : ByteArray) (offset : Nat := 0) : Except Error UInt16 := do
  let (value, _) ← fromDecode <| (cursorAt data offset).readUInt16BE
  return value

def getUInt32 (data : ByteArray) (offset : Nat := 0) : Except Error UInt32 := do
  let (value, _) ← fromDecode <| (cursorAt data offset).readUInt32BE
  return value

def getUInt64 (data : ByteArray) (offset : Nat := 0) : Except Error UInt64 := do
  let (value, _) ← fromDecode <| (cursorAt data offset).readUInt64BE
  return value

def getInt8 (data : ByteArray) (offset : Nat := 0) : Except Error Int8 :=
  UInt8.toInt8 <$> getUInt8 data offset

def getInt16 (data : ByteArray) (offset : Nat := 0) : Except Error Int16 :=
  UInt16.toInt16 <$> getUInt16 data offset

def getInt32 (data : ByteArray) (offset : Nat := 0) : Except Error Int32 :=
  UInt32.toInt32 <$> getUInt32 data offset

def getInt64 (data : ByteArray) (offset : Nat := 0) : Except Error Int64 :=
  UInt64.toInt64 <$> getUInt64 data offset

def getReal (data : ByteArray) (offset : Nat := 0) : Except Error Float32 :=
  Float32.ofBits <$> getUInt32 data offset

def getLReal (data : ByteArray) (offset : Nat := 0) : Except Error Float :=
  Float.ofBits <$> getUInt64 data offset

def getBit (data : ByteArray) (byteOffset bitIndex : Nat) : Except Error Bool := do
  if bitIndex >= 8 then
    throw (.invalidBitIndex bitIndex)
  let value ← getUInt8 data byteOffset
  let mask := UInt8.shiftLeft 1 (UInt8.ofNat bitIndex)
  return UInt8.land value mask != 0

def setBit (value : UInt8) (bitIndex : Nat) (enabled : Bool) : Except Error UInt8 := do
  if bitIndex >= 8 then
    throw (.invalidBitIndex bitIndex)
  let mask := UInt8.shiftLeft 1 (UInt8.ofNat bitIndex)
  return if enabled then UInt8.lor value mask else UInt8.land value mask.complement

def putUInt8 (value : UInt8) : ByteArray := bytes #[value]
def putUInt16 (value : UInt16) : ByteArray := uint16BE value
def putUInt32 (value : UInt32) : ByteArray := uint32BE value
def putUInt64 (value : UInt64) : ByteArray := uint64BE value
def putInt8 (value : Int8) : ByteArray := putUInt8 value.toUInt8
def putInt16 (value : Int16) : ByteArray := putUInt16 value.toUInt16
def putInt32 (value : Int32) : ByteArray := putUInt32 value.toUInt32
def putInt64 (value : Int64) : ByteArray := putUInt64 value.toUInt64
def putReal (value : Float32) : ByteArray := putUInt32 value.toBits
def putLReal (value : Float) : ByteArray := putUInt64 value.toBits

@[simp] theorem putUInt8_size (value : UInt8) : (putUInt8 value).size = 1 := by
  simp [putUInt8]

@[simp] theorem putUInt16_size (value : UInt16) : (putUInt16 value).size = 2 := by
  simp [putUInt16]

@[simp] theorem putUInt32_size (value : UInt32) : (putUInt32 value).size = 4 := by
  simp [putUInt32]

@[simp] theorem putUInt64_size (value : UInt64) : (putUInt64 value).size = 8 := by
  simp [putUInt64]

/-- Encoding and then reading an unsigned byte returns the original value. -/
theorem getUInt8_putUInt8 (value : UInt8) :
    getUInt8 (putUInt8 value) = .ok value := by
  have hread : Cursor.readUInt8 { data := putUInt8 value } =
      .ok (value, { data := putUInt8 value, offset := 1 }) := by
    rw [Cursor.readUInt8_of_lt _ (by simp [putUInt8])]
    congr 2 <;> simp [putUInt8, bytes]
  rw [getUInt8]
  change (do
    let result ← fromDecode (Cursor.readUInt8 { data := putUInt8 value })
    pure result.fst) = .ok value
  rw [hread]
  rfl

/-- Encoding and then reading an unsigned word returns the original value. -/
theorem getUInt16_putUInt16 (value : UInt16) :
    getUInt16 (putUInt16 value) = .ok value := by
  rw [getUInt16]
  change (do
    let result ← fromDecode (Cursor.readUInt16BE { data := uint16BE value })
    pure result.fst) = .ok value
  rw [readUInt16BE_uint16BE]
  rfl

/-- Encoding and then reading an unsigned double word returns the original
    value. -/
theorem getUInt32_putUInt32 (value : UInt32) :
    getUInt32 (putUInt32 value) = .ok value := by
  rw [getUInt32]
  change (do
    let result ← fromDecode (Cursor.readUInt32BE { data := uint32BE value })
    pure result.fst) = .ok value
  rw [readUInt32BE_uint32BE]
  rfl

/-- Encoding and then reading an unsigned quad word returns the original
    value. -/
theorem getUInt64_putUInt64 (value : UInt64) :
    getUInt64 (putUInt64 value) = .ok value := by
  rw [getUInt64]
  change (do
    let result ← fromDecode (Cursor.readUInt64BE { data := uint64BE value })
    pure result.fst) = .ok value
  rw [readUInt64BE_uint64BE]
  rfl

/-- Encoding and then reading a signed byte preserves its two's-complement
    value. -/
theorem getInt8_putInt8 (value : Int8) :
    getInt8 (putInt8 value) = .ok value := by
  rw [getInt8, putInt8, getUInt8_putUInt8]
  change Except.ok value.toUInt8.toInt8 = Except.ok value
  rw [Int8.toInt8_toUInt8]

/-- Encoding and then reading a signed word preserves its two's-complement
    value. -/
theorem getInt16_putInt16 (value : Int16) :
    getInt16 (putInt16 value) = .ok value := by
  rw [getInt16, putInt16, getUInt16_putUInt16]
  change Except.ok value.toUInt16.toInt16 = Except.ok value
  rw [Int16.toInt16_toUInt16]

/-- Encoding and then reading a signed double word preserves its
    two's-complement value. -/
theorem getInt32_putInt32 (value : Int32) :
    getInt32 (putInt32 value) = .ok value := by
  rw [getInt32, putInt32, getUInt32_putUInt32]
  change Except.ok value.toUInt32.toInt32 = Except.ok value
  rw [Int32.toInt32_toUInt32]

/-- Encoding and then reading a signed quad word preserves its two's-complement
    value. -/
theorem getInt64_putInt64 (value : Int64) :
    getInt64 (putInt64 value) = .ok value := by
  rw [getInt64, putInt64, getUInt64_putUInt64]
  change Except.ok value.toUInt64.toInt64 = Except.ok value
  rw [Int64.toInt64_toUInt64]

private def zeros (count : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate count 0)

private def encodeLatin1 : List Char → Except Error (List UInt8)
  | [] => pure []
  | character :: rest => do
      let codePoint := character.toNat
      if codePoint > 0xff then
        throw (.invalidCharacter codePoint)
      return UInt8.ofNat codePoint :: (← encodeLatin1 rest)

def encodeString (maximum : Nat) (value : String) : Except Error ByteArray := do
  if maximum > maxStringLength then
    throw (.invalidMaximumLength maximum maxStringLength)
  let encoded := List.toByteArray (← encodeLatin1 value.toList)
  if encoded.size > maximum then
    throw (.valueTooLong encoded.size maximum)
  return bytes #[UInt8.ofNat maximum, UInt8.ofNat encoded.size] ++ encoded ++
    zeros (maximum - encoded.size)

def decodeString (data : ByteArray) (offset : Nat := 0) : Except Error String := do
  let cursor := cursorAt data offset
  let (maximum, cursor) ← fromDecode cursor.readUInt8
  let (current, cursor) ← fromDecode cursor.readUInt8
  if maximum.toNat > maxStringLength then
    throw (.invalidMaximumLength maximum.toNat maxStringLength)
  if current > maximum then
    throw (.invalidStringHeader current.toNat maximum.toNat)
  let (content, _) ← fromDecode <| cursor.readBytes maximum.toNat
  return String.ofList <| (content.extract 0 current.toNat).toList.map fun byte => Char.ofNat byte.toNat

private def encodeUtf16Char (character : Char) : List UInt16 :=
  let codePoint := character.toNat
  if codePoint < 0x10000 then
    [UInt16.ofNat codePoint]
  else
    let scalar := codePoint - 0x10000
    [UInt16.ofNat (0xd800 + scalar / 0x400), UInt16.ofNat (0xdc00 + scalar % 0x400)]

private def encodeUtf16 : List Char → List UInt16
  | [] => []
  | character :: rest => encodeUtf16Char character ++ encodeUtf16 rest

private def encodeUtf16Units : List UInt16 → ByteArray
  | [] => ByteArray.empty
  | unit :: rest => uint16BE unit ++ encodeUtf16Units rest

private def decodeUtf16Units : List UInt16 → Nat → Except Error (List Char)
  | [], _ => pure []
  | unit :: rest, offset =>
      let value := unit.toNat
      if value >= 0xd800 && value <= 0xdbff then
        match rest with
        | low :: tail => do
            let lowValue := low.toNat
            if lowValue < 0xdc00 || lowValue > 0xdfff then
              throw (.invalidUtf16 offset "high surrogate is not followed by a low surrogate")
            let codePoint := 0x10000 + (value - 0xd800) * 0x400 + (lowValue - 0xdc00)
            return Char.ofNat codePoint :: (← decodeUtf16Units tail (offset + 2))
        | [] => throw (.invalidUtf16 offset "trailing high surrogate")
      else if value >= 0xdc00 && value <= 0xdfff then
        throw (.invalidUtf16 offset "unpaired low surrogate")
      else
        return Char.ofNat value :: (← decodeUtf16Units rest (offset + 1))

private def readUtf16Units : Nat → Cursor → Except Error (List UInt16)
  | 0, _ => pure []
  | count + 1, cursor => do
      let (unit, cursor) ← fromDecode cursor.readUInt16BE
      return unit :: (← readUtf16Units count cursor)

def encodeWString (maximum : Nat) (value : String) : Except Error ByteArray := do
  if maximum > maxWStringLength then
    throw (.invalidMaximumLength maximum maxWStringLength)
  let units := encodeUtf16 value.toList
  if units.length > maximum then
    throw (.valueTooLong units.length maximum)
  return uint16BE (UInt16.ofNat maximum) ++ uint16BE (UInt16.ofNat units.length) ++
    encodeUtf16Units units ++ zeros ((maximum - units.length) * 2)

def decodeWString (data : ByteArray) (offset : Nat := 0) : Except Error String := do
  let cursor := cursorAt data offset
  let (maximum, cursor) ← fromDecode cursor.readUInt16BE
  let (current, cursor) ← fromDecode cursor.readUInt16BE
  if maximum.toNat > maxWStringLength then
    throw (.invalidMaximumLength maximum.toNat maxWStringLength)
  if current > maximum then
    throw (.invalidStringHeader current.toNat maximum.toNat)
  let units ← readUtf16Units current.toNat cursor
  let _ ← fromDecode <| cursor.readBytes (maximum.toNat * 2)
  return String.ofList (← decodeUtf16Units units 0)

end LeanS7.Value
