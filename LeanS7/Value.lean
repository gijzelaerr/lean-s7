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

/-- Successful STRING encoding reserves its entire declared capacity. -/
theorem encodeString_size (maximum : Nat) (value : String) (encoded : ByteArray)
    (h : encodeString maximum value = .ok encoded) : encoded.size = maximum + 2 := by
  unfold encodeString at h
  split at h
  · contradiction
  · cases he : encodeLatin1 value.toList with
    | error error => simp [he, bind, Except.bind] at h
    | ok characters =>
      simp only [he, bind, Except.bind, pure, Except.pure] at h
      split at h
      · contradiction
      · cases h
        simp only [ByteArray.size_append, bytes_size]
        change 2 + characters.toByteArray.size +
          (zeros (maximum - characters.toByteArray.size)).size = maximum + 2
        have hz (n : Nat) : (zeros n).size = n := by simp [zeros, ByteArray.size]
        rw [hz]
        omega

private theorem encodeUtf16Units_size (units : List UInt16) :
    (encodeUtf16Units units).size = units.length * 2 := by
  induction units with
  | nil => rfl
  | cons unit rest ih => simp [encodeUtf16Units, ih]; omega

/-- WSTRING reserves two bytes per declared UTF-16 code unit, including padding. -/
theorem encodeWString_size (maximum : Nat) (value : String) (encoded : ByteArray)
    (h : encodeWString maximum value = .ok encoded) : encoded.size = maximum * 2 + 4 := by
  unfold encodeWString at h
  split at h
  · contradiction
  · dsimp at h
    split at h
    · contradiction
    · simp only [pure, Except.pure] at h
      cases h
      simp only [ByteArray.size_append, uint16BE_size, encodeUtf16Units_size]
      have hz (n : Nat) : (zeros n).size = n := by simp [zeros, ByteArray.size]
      rw [hz]
      omega

theorem encodeString_capacity_bound (maximum : Nat) (value : String) (encoded : ByteArray)
    (h : encodeString maximum value = .ok encoded) : maximum ≤ maxStringLength := by
  unfold encodeString at h
  split at h
  · contradiction
  · omega

theorem encodeWString_capacity_bound (maximum : Nat) (value : String) (encoded : ByteArray)
    (h : encodeWString maximum value = .ok encoded) : maximum ≤ maxWStringLength := by
  unfold encodeWString at h
  split at h
  · contradiction
  · omega

/-- Empty STRING values ignore unused reserved bytes but still require their
    declared capacity to be present. -/
theorem decodeString_empty_surrounded (pre storage suffix : ByteArray) (maximum : UInt8)
    (hmax : maximum.toNat ≤ maxStringLength) (hstorage : maximum.toNat ≤ storage.size) :
    decodeString (pre ++ (putUInt8 maximum ++ (putUInt8 0 ++ (storage ++ suffix))))
      pre.size = .ok "" := by
  unfold decodeString
  simp only [cursorAt, putUInt8]
  rw [Cursor.readUInt8_append_byte]
  simp only [fromDecode, Except.mapError, bind, Except.bind]
  have hsecond := Cursor.readUInt8_append_byte (pre ++ bytes #[maximum]) (storage ++ suffix) 0
  simp only [ByteArray.size_append, bytes_size] at hsecond
  change Cursor.readUInt8 {
    data := (pre ++ bytes #[maximum]) ++ (bytes #[0] ++ (storage ++ suffix))
    offset := pre.size + 1 } = _ at hsecond
  rw [ByteArray.append_assoc] at hsecond
  rw [hsecond]
  have hcapacity : ¬ maxStringLength < maximum.toNat := by omega
  have havailable : maximum.toNat ≤
      pre.size + (1 + (1 + (storage.size + suffix.size))) - (pre.size + 1 + 1) := by omega
  simp [hcapacity, Cursor.readBytes, Cursor.remaining, havailable,
    pure, Except.pure, String.ofList_nil]

/-- The entire active STRING content is interpreted independently of bytes
    outside its declared storage, for arbitrary (including nonempty) content. -/
theorem decodeString_surrounded_content (pre content suffix : ByteArray) (maximum current : UInt8)
    (hmax : maximum.toNat ≤ maxStringLength) (hcurrent : current ≤ maximum)
    (hsize : content.size = maximum.toNat) :
    decodeString (pre ++ (putUInt8 maximum ++ (putUInt8 current ++ (content ++ suffix))))
      pre.size = .ok (String.ofList <|
        (content.extract 0 current.toNat).toList.map fun byte => Char.ofNat byte.toNat) := by
  unfold decodeString
  simp only [cursorAt, putUInt8]
  rw [Cursor.readUInt8_append_byte]
  simp only [fromDecode, Except.mapError, bind, Except.bind]
  have hsecond := Cursor.readUInt8_append_byte (pre ++ bytes #[maximum]) (content ++ suffix) current
  simp only [ByteArray.size_append, bytes_size] at hsecond
  change Cursor.readUInt8 {
    data := (pre ++ bytes #[maximum]) ++ (bytes #[current] ++ (content ++ suffix))
    offset := pre.size + 1 } = _ at hsecond
  rw [ByteArray.append_assoc] at hsecond
  rw [hsecond]
  have hcapacity : ¬ maximum.toNat > maxStringLength := by omega
  have hactive : ¬ current > maximum := by
    simp only [UInt8.le_iff_toNat_le] at hcurrent
    simp only [UInt8.lt_iff_toNat_lt]
    omega
  have hsingle : (#[maximum] : Array UInt8).size = 1 := rfl
  simp only [hsingle]
  simp only [hcapacity, hactive, if_false]
  have hread := Cursor.readBytes_append ((pre ++ bytes #[maximum]) ++ bytes #[current]) content suffix
  simp only [ByteArray.size_append, bytes_size] at hread
  change Cursor.readBytes {
    data := ((pre ++ bytes #[maximum]) ++ bytes #[current]) ++ (content ++ suffix)
    offset := pre.size + 1 + 1 } content.size = _ at hread
  simp only [ByteArray.append_assoc] at hread
  rw [hsize] at hread
  rw [hread]
  rfl

/-- An empty WSTRING decodes independently of arbitrary unused storage and
    surrounding DB bytes. The capacity is in UTF-16 units, not characters. -/
theorem decodeWString_empty_surrounded (pre storage suffix : ByteArray) (maximum : UInt16)
    (hmax : maximum.toNat ≤ maxWStringLength) (hstorage : maximum.toNat * 2 ≤ storage.size) :
    decodeWString (pre ++ (uint16BE maximum ++ (uint16BE 0 ++ (storage ++ suffix))))
      pre.size = .ok "" := by
  unfold decodeWString
  simp only [cursorAt]
  rw [Cursor.readUInt16BE_append_uint16BE]
  simp only [fromDecode, Except.mapError, bind, Except.bind]
  have hsecond := Cursor.readUInt16BE_append_uint16BE (pre ++ uint16BE maximum)
    (storage ++ suffix) 0
  simp only [ByteArray.size_append, uint16BE_size] at hsecond
  rw [ByteArray.append_assoc] at hsecond
  rw [hsecond]
  have hcapacity : ¬ maxWStringLength < maximum.toNat := by omega
  have havailable : maximum.toNat * 2 ≤
      pre.size + (2 + (2 + (storage.size + suffix.size))) - (pre.size + 2 + 2) := by omega
  simp [hcapacity, readUtf16Units, Cursor.readBytes, Cursor.remaining, havailable,
    decodeUtf16Units, pure, Except.pure, String.ofList_nil]

/-- Actual empty STRING encoder/decoder composition, at arbitrary DB offsets. -/
theorem decodeString_encodeString_empty_surrounded (pre suffix : ByteArray) (maximum : Nat)
    (hmax : maximum ≤ maxStringLength) :
    (encodeString maximum "" >>= fun encoded =>
      decodeString (pre ++ (encoded ++ suffix)) pre.size) = .ok "" := by
  have hcapacity : ¬ maximum > maxStringLength := by omega
  have hencoded : encodeString maximum "" =
      .ok (putUInt8 (UInt8.ofNat maximum) ++ (putUInt8 0 ++ zeros maximum)) := by
    simp [encodeString, hcapacity, encodeLatin1, bind, Except.bind, pure, Except.pure]
    rfl
  rw [hencoded]
  simp only [bind, Except.bind]
  rw [ByteArray.append_assoc, ByteArray.append_assoc]
  apply decodeString_empty_surrounded
  · simp only [UInt8.toNat_ofNat']
    unfold maxStringLength at *
    omega
  · simp [zeros, ByteArray.size, UInt8.toNat_ofNat']
    omega

/-- Empty WSTRING round trips for every legal code-unit capacity. -/
theorem decodeWString_encodeWString_empty_surrounded (pre suffix : ByteArray) (maximum : Nat)
    (hmax : maximum ≤ maxWStringLength) :
    (encodeWString maximum "" >>= fun encoded =>
      decodeWString (pre ++ (encoded ++ suffix)) pre.size) = .ok "" := by
  have hcapacity : ¬ maximum > maxWStringLength := by omega
  have hencoded : encodeWString maximum "" =
      .ok (uint16BE (UInt16.ofNat maximum) ++ (uint16BE 0 ++ zeros (maximum * 2))) := by
    simp [encodeWString, hcapacity, encodeUtf16, encodeUtf16Units,
      pure, Except.pure, ByteArray.append_assoc]
  rw [hencoded]
  simp only [bind, Except.bind]
  rw [ByteArray.append_assoc, ByteArray.append_assoc]
  apply decodeWString_empty_surrounded
  · simp only [UInt16.toNat_ofNat']
    unfold maxWStringLength at *
    omega
  · simp [zeros, ByteArray.size, UInt16.toNat_ofNat']
    omega

private theorem encodeLatin1_valid (characters : List Char)
    (hvalid : ∀ character ∈ characters, character.toNat ≤ 255) :
    encodeLatin1 characters = .ok (characters.map (fun character => UInt8.ofNat character.toNat)) := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
    have hcharacter := hvalid character (by simp)
    have hrest : ∀ character ∈ rest, character.toNat ≤ 255 := by
      intro character h
      exact hvalid character (by simp [h])
    simp [encodeLatin1, show ¬ character.toNat > 255 by omega, ih hrest,
      bind, Except.bind, pure, Except.pure]

private theorem latin1_characters (characters : List Char)
    (hvalid : ∀ character ∈ characters, character.toNat ≤ 255) :
    (characters.map (fun character => UInt8.ofNat character.toNat)).map
      (fun byte => Char.ofNat byte.toNat) = characters := by
  rw [List.map_map]
  calc
    _ = characters.map id := by
      apply List.map_congr_left
      intro character h
      have hc := hvalid character h
      simp only [Function.comp_apply, UInt8.toNat_ofNat']
      rw [Nat.mod_eq_of_lt (by omega), Char.ofNat_toNat]
      rfl
    _ = characters := List.map_id _

/-- Every supported Latin-1 STRING, including nonempty values, round trips at
    arbitrary DB offsets and legal reserved capacities. -/
theorem decodeString_encodeString_surrounded (pre suffix : ByteArray) (maximum : Nat)
    (value : String) (hmax : maximum ≤ maxStringLength)
    (hfits : value.toList.length ≤ maximum)
    (hvalid : ∀ character ∈ value.toList, character.toNat ≤ 255) :
    (encodeString maximum value >>= fun encoded =>
      decodeString (pre ++ (encoded ++ suffix)) pre.size) = .ok value := by
  let content := (value.toList.map (fun character => UInt8.ofNat character.toNat)).toByteArray
  have hcontent : content.size = value.toList.length := by simp [content]
  have hcapacity : ¬ maximum > maxStringLength := by omega
  have hlength : ¬ content.size > maximum := by omega
  have hencoded : encodeString maximum value = .ok
      (putUInt8 (UInt8.ofNat maximum) ++ (putUInt8 (UInt8.ofNat content.size) ++
        (content ++ zeros (maximum - content.size)))) := by
    simp only [encodeString, hcapacity, if_false, encodeLatin1_valid _ hvalid,
      bind, Except.bind]
    change (if content.size > maximum then _ else _) = _
    rw [if_neg hlength]
    simp only [pure, Except.pure, putUInt8, bytes]
    congr 1
  have hm : (UInt8.ofNat maximum).toNat = maximum := by
    simp only [UInt8.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    unfold maxStringLength at hmax
    omega
  have hc : (UInt8.ofNat content.size).toNat = content.size := by
    simp only [UInt8.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    unfold maxStringLength at hmax
    omega
  rw [hencoded]
  simp only [bind, Except.bind]
  simp only [ByteArray.append_assoc]
  rw [← ByteArray.append_assoc (a := content)]
  rw [decodeString_surrounded_content pre (content ++ zeros (maximum - content.size)) suffix
    (UInt8.ofNat maximum) (UInt8.ofNat content.size) (by simpa [hm] using hmax)
    (by simp only [UInt8.le_iff_toNat_le, hm, hc]; omega)
    (by have hz : (zeros (maximum - content.size)).size = maximum - content.size := by
          simp only [zeros, ByteArray.size, Array.size_replicate]
        rw [ByteArray.size_append, hz, hm]
        omega)]
  rw [hc, ByteArray.extract_append_eq_left rfl]
  change Except.ok (String.ofList (content.toList.map (fun byte => Char.ofNat byte.toNat))) = _
  have hl : content.toList = value.toList.map (fun character => UInt8.ofNat character.toNat) := by
    rw [byteArray_toList_data]
    exact List.toList_data_toByteArray
  rw [hl, latin1_characters _ hvalid, String.ofList_toList]

private theorem decodeUtf16Units_encodeUtf16 (characters : List Char) (offset : Nat) :
    decodeUtf16Units (encodeUtf16 characters) offset = .ok characters := by
  induction characters generalizing offset with
  | nil => rfl
  | cons character rest ih =>
    have hvalid := character.valid
    simp only [UInt32.isValidChar, Char.toNat_val] at hvalid
    simp only [encodeUtf16, encodeUtf16Char]
    split
    · rename_i hsmall
      have hm : (UInt16.ofNat character.toNat).toNat = character.toNat := by
        rw [UInt16.toNat_ofNat', Nat.mod_eq_of_lt hsmall]
      have hhigh : ¬ (character.toNat ≥ 0xd800 ∧ character.toNat ≤ 0xdbff) := by omega
      have hlow : ¬ (character.toNat ≥ 0xdc00 ∧ character.toNat ≤ 0xdfff) := by omega
      simp only [List.singleton_append]
      rw [decodeUtf16Units.eq_def]
      simp only [hm]
      simp [hhigh, hlow, ih, Char.ofNat_toNat,
        bind, Except.bind, pure, Except.pure]
    · rename_i hlarge
      have hupper : character.toNat < 0x110000 := by omega
      have hhi : (UInt16.ofNat (0xd800 + (character.toNat - 0x10000) / 0x400)).toNat =
          0xd800 + (character.toNat - 0x10000) / 0x400 := by
        rw [UInt16.toNat_ofNat']
        apply Nat.mod_eq_of_lt
        omega
      have hlo : (UInt16.ofNat (0xdc00 + (character.toNat - 0x10000) % 0x400)).toNat =
          0xdc00 + (character.toNat - 0x10000) % 0x400 := by
        rw [UInt16.toNat_ofNat']
        apply Nat.mod_eq_of_lt
        omega
      have hhigh : 0xd800 ≤ 0xd800 + (character.toNat - 0x10000) / 0x400 ∧
          0xd800 + (character.toNat - 0x10000) / 0x400 ≤ 0xdbff := by omega
      have hlow : ¬ (0xdc00 + (character.toNat - 0x10000) % 0x400 < 0xdc00 ∨
          0xdc00 + (character.toNat - 0x10000) % 0x400 > 0xdfff) := by omega
      have hpoint : 0x10000 + (character.toNat - 0x10000) / 0x400 * 0x400 +
          (character.toNat - 0x10000) % 0x400 = character.toNat := by omega
      simp only [List.cons_append, List.nil_append]
      rw [decodeUtf16Units]
      simp only [hhi, hlo]
      simp [hhigh, hlow, hpoint, ih, Char.ofNat_toNat,
        bind, Except.bind, pure, Except.pure]

private theorem readUtf16Units_encodeUtf16Units (units : List UInt16) (pre suffix : ByteArray) :
    readUtf16Units units.length {
      data := pre ++ (encodeUtf16Units units ++ suffix), offset := pre.size } = .ok units := by
  induction units generalizing pre with
  | nil => rfl
  | cons unit rest ih =>
    simp only [List.length_cons, readUtf16Units, encodeUtf16Units, ByteArray.append_assoc]
    rw [Cursor.readUInt16BE_append_uint16BE]
    simp only [fromDecode, Except.mapError, bind, Except.bind]
    have hrest := ih (pre ++ uint16BE unit)
    simp only [ByteArray.size_append, uint16BE_size, ByteArray.append_assoc] at hrest
    rw [hrest]
    rfl

/-- WSTRING capacity counts UTF-16 code units: supplementary characters use two. -/
def utf16Length (value : String) : Nat := (encodeUtf16 value.toList).length

/-- Actual WSTRING encoder/decoder composition for all Unicode scalar values,
    including supplementary-plane surrogate pairs, at arbitrary DB offsets. -/
theorem decodeWString_encodeWString_surrounded (pre suffix : ByteArray) (maximum : Nat)
    (value : String) (hmax : maximum ≤ maxWStringLength)
    (hfits : utf16Length value ≤ maximum) :
    (encodeWString maximum value >>= fun encoded =>
      decodeWString (pre ++ (encoded ++ suffix)) pre.size) = .ok value := by
  let units := encodeUtf16 value.toList
  have hcapacity : ¬ maximum > maxWStringLength := by omega
  have hlength : ¬ units.length > maximum := by
    change units.length ≤ maximum at hfits
    omega
  have hm : (UInt16.ofNat maximum).toNat = maximum := by
    rw [UInt16.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    unfold maxWStringLength at hmax
    omega
  have hc : (UInt16.ofNat units.length).toNat = units.length := by
    rw [UInt16.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    unfold maxWStringLength at hmax
    omega
  have hencoded : encodeWString maximum value = .ok
      (uint16BE (UInt16.ofNat maximum) ++ (uint16BE (UInt16.ofNat units.length) ++
        (encodeUtf16Units units ++ zeros ((maximum - units.length) * 2)))) := by
    simp only [encodeWString, hcapacity, if_false]
    change (if units.length > maximum then _ else _) = _
    rw [if_neg hlength]
    simp only [pure, Except.pure, ByteArray.append_assoc]
    rfl
  rw [hencoded]
  simp only [bind, Except.bind, ByteArray.append_assoc]
  unfold decodeWString
  simp only [cursorAt]
  rw [Cursor.readUInt16BE_append_uint16BE]
  simp only [fromDecode, Except.mapError, bind, Except.bind]
  have hsecond := Cursor.readUInt16BE_append_uint16BE
    (pre ++ uint16BE (UInt16.ofNat maximum))
    (encodeUtf16Units units ++ (zeros ((maximum - units.length) * 2) ++ suffix))
    (UInt16.ofNat units.length)
  simp only [ByteArray.size_append, uint16BE_size, ByteArray.append_assoc] at hsecond
  rw [hsecond]
  have hactive : ¬ UInt16.ofNat units.length > UInt16.ofNat maximum := by
    simp only [UInt16.lt_iff_toNat_lt, hc, hm]
    omega
  simp only [hm, hcapacity, hactive, if_false, hc]
  have hread := readUtf16Units_encodeUtf16Units units
    ((pre ++ uint16BE (UInt16.ofNat maximum)) ++ uint16BE (UInt16.ofNat units.length))
    (zeros ((maximum - units.length) * 2) ++ suffix)
  simp only [ByteArray.size_append, uint16BE_size, ByteArray.append_assoc] at hread
  rw [hread]
  have hz : (zeros ((maximum - units.length) * 2)).size = (maximum - units.length) * 2 := by
    simp only [zeros, ByteArray.size, Array.size_replicate]
  have havailable : maximum * 2 ≤
      (pre ++ (uint16BE (UInt16.ofNat maximum) ++ (uint16BE (UInt16.ofNat units.length) ++
        (encodeUtf16Units units ++ (zeros ((maximum - units.length) * 2) ++ suffix))))).size -
          (pre.size + 2 + 2) := by
    simp only [ByteArray.size_append, uint16BE_size, encodeUtf16Units_size, hz]
    omega
  simp only [Cursor.readBytes, Cursor.remaining, havailable, if_true]
  rw [decodeUtf16Units_encodeUtf16]
  simp only [pure, Except.pure, String.ofList_toList]

end LeanS7.Value
