namespace LeanS7

/-- A decoding failure with the byte offset at which it was detected. -/
inductive DecodeError where
  | unexpectedEnd (offset needed available : Nat)
  | invalidField (offset : Nat) (message : String)
  | trailingBytes (offset count : Nat)
  deriving Repr, BEq

/-- A cursor into immutable packet data. Reads advance by returning a new cursor. -/
structure Cursor where
  data : ByteArray
  offset : Nat := 0

namespace Cursor

def remaining (cursor : Cursor) : Nat :=
  cursor.data.size - cursor.offset

def readUInt8 (cursor : Cursor) : Except DecodeError (UInt8 × Cursor) :=
  if h : cursor.offset < cursor.data.size then
    let value := cursor.data[cursor.offset]'h
    .ok (value, { cursor with offset := cursor.offset + 1 })
  else
    .error (.unexpectedEnd cursor.offset 1 cursor.remaining)

def readUInt16BE (cursor : Cursor) : Except DecodeError (UInt16 × Cursor) := do
  let (high, cursor) ← cursor.readUInt8
  let (low, cursor) ← cursor.readUInt8
  return (UInt16.ofNat (high.toNat * 256 + low.toNat), cursor)

def readUInt24BE (cursor : Cursor) : Except DecodeError (UInt32 × Cursor) := do
  let (a, cursor) ← cursor.readUInt8
  let (b, cursor) ← cursor.readUInt8
  let (c, cursor) ← cursor.readUInt8
  return (UInt32.ofNat (a.toNat * 65536 + b.toNat * 256 + c.toNat), cursor)

def readUInt32BE (cursor : Cursor) : Except DecodeError (UInt32 × Cursor) := do
  let (high, cursor) ← cursor.readUInt16BE
  let (low, cursor) ← cursor.readUInt16BE
  return (UInt32.ofNat (high.toNat * 65536 + low.toNat), cursor)

def readUInt64BE (cursor : Cursor) : Except DecodeError (UInt64 × Cursor) := do
  let (high, cursor) ← cursor.readUInt32BE
  let (low, cursor) ← cursor.readUInt32BE
  return (UInt64.ofNat (high.toNat * 4294967296 + low.toNat), cursor)

def readBytes (cursor : Cursor) (count : Nat) : Except DecodeError (ByteArray × Cursor) :=
  if count ≤ cursor.remaining then
    let next := cursor.offset + count
    .ok (cursor.data.extract cursor.offset next, { cursor with offset := next })
  else
    .error (.unexpectedEnd cursor.offset count cursor.remaining)

def finish (cursor : Cursor) : Except DecodeError Unit :=
  if cursor.offset = cursor.data.size then
    .ok ()
  else
    .error (.trailingBytes cursor.offset cursor.remaining)

/-- A byte read succeeds when the cursor points inside the input. -/
theorem readUInt8_of_lt (cursor : Cursor) (h : cursor.offset < cursor.data.size) :
    cursor.readUInt8 = .ok (cursor.data[cursor.offset],
      { cursor with offset := cursor.offset + 1 }) := by
  simp [readUInt8, h]

/-- Two available bytes decode as a big-endian word and advance the cursor twice. -/
theorem readUInt16BE_of_available (cursor : Cursor)
    (h : cursor.offset + 2 ≤ cursor.data.size) :
    cursor.readUInt16BE = .ok (
      UInt16.ofNat (
        cursor.data[cursor.offset].toNat * 256 +
          cursor.data[cursor.offset + 1].toNat),
      { cursor with offset := cursor.offset + 2 }) := by
  rw [readUInt16BE, readUInt8_of_lt cursor (by omega)]
  change (do
    let result ← readUInt8 { cursor with offset := cursor.offset + 1 }
    pure (UInt16.ofNat (
      cursor.data[cursor.offset].toNat * 256 + result.fst.toNat), result.snd)) = _
  rw [readUInt8_of_lt _ (by simp; omega)]
  rfl

/-- Four available bytes decode as a big-endian double word and advance the
    cursor four positions. -/
theorem readUInt32BE_of_available (cursor : Cursor)
    (h : cursor.offset + 4 ≤ cursor.data.size) :
    cursor.readUInt32BE = .ok (
      UInt32.ofNat (
        (UInt16.ofNat (
          cursor.data[cursor.offset].toNat * 256 +
            cursor.data[cursor.offset + 1].toNat)).toNat * 65536 +
        (UInt16.ofNat (
          cursor.data[cursor.offset + 2].toNat * 256 +
            cursor.data[cursor.offset + 3].toNat)).toNat),
      { cursor with offset := cursor.offset + 4 }) := by
  rw [readUInt32BE, readUInt16BE_of_available cursor (by omega)]
  change (do
    let result ← readUInt16BE { cursor with offset := cursor.offset + 2 }
    pure (UInt32.ofNat (
      (UInt16.ofNat (
        cursor.data[cursor.offset].toNat * 256 +
          cursor.data[cursor.offset + 1].toNat)).toNat * 65536 +
        result.fst.toNat), result.snd)) = _
  rw [readUInt16BE_of_available _ (by simp; omega)]
  rfl

/-- Eight available bytes decode as a big-endian quad word and advance the
    cursor eight positions. -/
theorem readUInt64BE_of_available (cursor : Cursor)
    (h : cursor.offset + 8 ≤ cursor.data.size) :
    cursor.readUInt64BE = .ok (
      UInt64.ofNat (
        (UInt32.ofNat (
          (UInt16.ofNat (
            cursor.data[cursor.offset].toNat * 256 +
              cursor.data[cursor.offset + 1].toNat)).toNat * 65536 +
          (UInt16.ofNat (
            cursor.data[cursor.offset + 2].toNat * 256 +
              cursor.data[cursor.offset + 3].toNat)).toNat)).toNat * 4294967296 +
        (UInt32.ofNat (
          (UInt16.ofNat (
            cursor.data[cursor.offset + 4].toNat * 256 +
              cursor.data[cursor.offset + 5].toNat)).toNat * 65536 +
          (UInt16.ofNat (
            cursor.data[cursor.offset + 6].toNat * 256 +
              cursor.data[cursor.offset + 7].toNat)).toNat)).toNat),
      { cursor with offset := cursor.offset + 8 }) := by
  rw [readUInt64BE, readUInt32BE_of_available cursor (by omega)]
  change (do
    let result ← readUInt32BE { cursor with offset := cursor.offset + 4 }
    pure (UInt64.ofNat (
      (UInt32.ofNat (
        (UInt16.ofNat (
          cursor.data[cursor.offset].toNat * 256 +
            cursor.data[cursor.offset + 1].toNat)).toNat * 65536 +
        (UInt16.ofNat (
          cursor.data[cursor.offset + 2].toNat * 256 +
            cursor.data[cursor.offset + 3].toNat)).toNat)).toNat * 4294967296 +
        result.fst.toNat), result.snd)) = _
  rw [readUInt32BE_of_available _ (by simp; omega)]
  rfl

end Cursor

def uint16BE (value : UInt16) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[UInt8.ofNat (n / 256), UInt8.ofNat n]

@[simp] theorem uint16BE_size (value : UInt16) : (uint16BE value).size = 2 := by
  rfl

/-- Encoding then reading a big-endian word returns the original value. -/
theorem readUInt16BE_uint16BE (value : UInt16) :
    Cursor.readUInt16BE { data := uint16BE value } =
      .ok (value, { data := uint16BE value, offset := 2 }) := by
  rw [Cursor.readUInt16BE_of_available _ (by
    change 2 ≤ (#[UInt8.ofNat (value.toNat / 256), UInt8.ofNat value.toNat] : Array UInt8).size
    simp)]
  change Except.ok (UInt16.ofNat (
    (UInt8.ofNat (value.toNat / 256)).toNat * 256 +
      (UInt8.ofNat value.toNat).toNat),
    ({ data := uint16BE value, offset := 2 } : Cursor)) =
    Except.ok (value, ({ data := uint16BE value, offset := 2 } : Cursor))
  congr 2
  apply UInt16.toNat_inj.mp
  simp [UInt16.toNat_add, UInt16.toNat_mul, UInt8.toNat_ofNat']
  have h := UInt16.toNat_lt value
  omega

/-- A big-endian word can be read at the boundary between an arbitrary prefix
    and suffix. This is the compositional form used by protocol codec proofs. -/
theorem Cursor.readUInt16BE_append_uint16BE (pre suffix : ByteArray)
    (value : UInt16) :
    Cursor.readUInt16BE {
      data := pre ++ (uint16BE value ++ suffix)
      offset := pre.size
    } = .ok (value, {
      data := pre ++ (uint16BE value ++ suffix)
      offset := pre.size + 2
    }) := by
  let data := pre ++ (uint16BE value ++ suffix)
  rw [Cursor.readUInt16BE_of_available (cursor := { data, offset := pre.size }) (by
    dsimp only [data]
    rw [ByteArray.size_append, ByteArray.size_append]
    change pre.size + 2 ≤ pre.size + (2 + suffix.size)
    omega)]
  congr 2
  have hdata0 : pre.size < data.size := by
    dsimp only [data]
    rw [ByteArray.size_append, ByteArray.size_append]
    change pre.size < pre.size + (2 + suffix.size)
    omega
  have hdata1 : pre.size + 1 < data.size := by
    dsimp only [data]
    rw [ByteArray.size_append, ByteArray.size_append]
    change pre.size + 1 < pre.size + (2 + suffix.size)
    omega
  have hword0 : 0 < (uint16BE value).size := by
    change 0 < (#[UInt8.ofNat (value.toNat / 256), UInt8.ofNat value.toNat] : Array UInt8).size
    simp
  have hword1 : 1 < (uint16BE value).size := by
    change 1 < (#[UInt8.ofNat (value.toNat / 256), UInt8.ofNat value.toNat] : Array UInt8).size
    simp
  have hget0 : data[pre.size]'hdata0 = (uint16BE value)[0]'hword0 := by
    dsimp only [data]
    rw [ByteArray.getElem_append_right (by omega)]
    simp only [Nat.sub_self]
    rw [ByteArray.getElem_append_left hword0]
  have hget1 : data[pre.size + 1]'hdata1 = (uint16BE value)[1]'hword1 := by
    dsimp only [data]
    rw [ByteArray.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [ByteArray.getElem_append_left hword1]
  rw [hget0, hget1]
  have hround := readUInt16BE_uint16BE value
  rw [Cursor.readUInt16BE_of_available _ (by
    change 2 ≤ (#[UInt8.ofNat (value.toNat / 256), UInt8.ofNat value.toNat] : Array UInt8).size
    simp)] at hround
  injection hround with hpair
  injection hpair with hvalue

/-- Reading the next complete byte segment returns that segment and leaves the
    cursor at the following boundary. -/
theorem Cursor.readBytes_append (pre value suffix : ByteArray) :
    Cursor.readBytes {
      data := pre ++ (value ++ suffix)
      offset := pre.size
    } value.size = .ok (value, {
      data := pre ++ (value ++ suffix)
      offset := pre.size + value.size
    }) := by
  let data := pre ++ (value ++ suffix)
  rw [Cursor.readBytes, if_pos (by simp [Cursor.remaining])]
  have hextract : data.extract pre.size (pre.size + value.size) = value := by
    dsimp only [data]
    rw [show (pre ++ (value ++ suffix)).extract pre.size
        (pre.size + value.size) = (value ++ suffix).extract 0 value.size by
      simpa using (ByteArray.extract_append_size_add
        (a := pre) (b := value ++ suffix) (i := 0) (j := value.size))]
    exact ByteArray.extract_append_eq_left rfl
  change Except.ok
    (data.extract pre.size (pre.size + value.size),
      ({ data, offset := pre.size + value.size } : Cursor)) = _
  rw [hextract]

def uint24BE (value : UInt32) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256), UInt8.ofNat n]

@[simp] theorem uint24BE_size (value : UInt32) : (uint24BE value).size = 3 := by
  rfl

def uint32BE (value : UInt32) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[
    UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536),
    UInt8.ofNat (n / 256), UInt8.ofNat n]

@[simp] theorem uint32BE_size (value : UInt32) : (uint32BE value).size = 4 := by
  rfl

/-- Encoding then reading a big-endian double word returns the original value. -/
theorem readUInt32BE_uint32BE (value : UInt32) :
    Cursor.readUInt32BE { data := uint32BE value } =
      .ok (value, { data := uint32BE value, offset := 4 }) := by
  rw [Cursor.readUInt32BE_of_available _ (by simp)]
  congr 2
  apply UInt32.toNat_inj.mp
  simp only [uint32BE, ByteArray.getElem_eq_getElem_data]
  simp [UInt32.toNat_ofNat', UInt16.toNat_ofNat', UInt8.toNat_ofNat']
  have h := UInt32.toNat_lt value
  omega

def uint64BE (value : UInt64) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[
    UInt8.ofNat (n / 72057594037927936), UInt8.ofNat (n / 281474976710656),
    UInt8.ofNat (n / 1099511627776), UInt8.ofNat (n / 4294967296),
    UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536),
    UInt8.ofNat (n / 256), UInt8.ofNat n]

@[simp] theorem uint64BE_size (value : UInt64) : (uint64BE value).size = 8 := by
  rfl

set_option maxHeartbeats 800000 in
/-- Encoding then reading a big-endian quad word returns the original value. -/
theorem readUInt64BE_uint64BE (value : UInt64) :
    Cursor.readUInt64BE { data := uint64BE value } =
      .ok (value, { data := uint64BE value, offset := 8 }) := by
  rw [Cursor.readUInt64BE_of_available _ (by simp)]
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [uint64BE, ByteArray.getElem_eq_getElem_data]
  simp [UInt64.toNat_ofNat', UInt32.toNat_ofNat', UInt16.toNat_ofNat',
    UInt8.toNat_ofNat']
  have h := UInt64.toNat_lt value
  omega

def bytes (values : Array UInt8) : ByteArray :=
  ByteArray.mk values

@[simp] theorem bytes_size (values : Array UInt8) : (bytes values).size = values.size := by
  rfl

end LeanS7
