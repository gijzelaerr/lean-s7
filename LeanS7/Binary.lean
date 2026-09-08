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

end Cursor

def uint16BE (value : UInt16) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[UInt8.ofNat (n / 256), UInt8.ofNat n]

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

def uint24BE (value : UInt32) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[UInt8.ofNat (n / 65536), UInt8.ofNat (n / 256), UInt8.ofNat n]

def uint32BE (value : UInt32) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[
    UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536),
    UInt8.ofNat (n / 256), UInt8.ofNat n]

def uint64BE (value : UInt64) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[
    UInt8.ofNat (n / 72057594037927936), UInt8.ofNat (n / 281474976710656),
    UInt8.ofNat (n / 1099511627776), UInt8.ofNat (n / 4294967296),
    UInt8.ofNat (n / 16777216), UInt8.ofNat (n / 65536),
    UInt8.ofNat (n / 256), UInt8.ofNat n]

def bytes (values : Array UInt8) : ByteArray :=
  ByteArray.mk values

end LeanS7
