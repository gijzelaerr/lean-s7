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

end Cursor

def uint16BE (value : UInt16) : ByteArray :=
  let n := value.toNat
  ByteArray.mk #[UInt8.ofNat (n / 256), UInt8.ofNat n]

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
