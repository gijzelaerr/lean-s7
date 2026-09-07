import LeanS7.Binary

namespace LeanS7.TPKT

def version : UInt8 := 3
def headerSize : Nat := 4
def maxFrameSize : Nat := 65535

structure Frame where
  payload : ByteArray
  deriving BEq

inductive EncodeError where
  | frameTooLarge (size maximum : Nat)
  deriving Repr, BEq

/-- Encode an RFC 1006 TPKT frame. -/
def encode (frame : Frame) : Except EncodeError ByteArray :=
  let length := headerSize + frame.payload.size
  if length ≤ maxFrameSize then
    let header := bytes #[version, 0] ++ uint16BE (UInt16.ofNat length)
    .ok (header ++ frame.payload)
  else
    .error (.frameTooLarge length maxFrameSize)

/-- Decode exactly one RFC 1006 TPKT frame. Trailing or truncated data is rejected. -/
def decode (data : ByteArray) : Except DecodeError Frame := do
  let cursor : Cursor := { data }
  let (actualVersion, cursor) ← cursor.readUInt8
  if actualVersion != version then
    throw (.invalidField 0 s!"unsupported TPKT version {actualVersion}")
  let (reserved, cursor) ← cursor.readUInt8
  if reserved != 0 then
    throw (.invalidField 1 "TPKT reserved byte must be zero")
  let (declaredLength, cursor) ← cursor.readUInt16BE
  let declaredLength := declaredLength.toNat
  if declaredLength < headerSize then
    throw (.invalidField 2 s!"invalid TPKT length {declaredLength}")
  if declaredLength != data.size then
    throw (.invalidField 2 s!"declared length {declaredLength} does not match {data.size} bytes")
  let (payload, cursor) ← cursor.readBytes (declaredLength - headerSize)
  cursor.finish
  return { payload }

theorem encoded_size (frame : Frame) (packet : ByteArray)
    (h : encode frame = .ok packet) : packet.size = headerSize + frame.payload.size := by
  by_cases hsize : headerSize + frame.payload.size ≤ maxFrameSize
  · simp [encode, hsize] at h
    subst packet
    simp [bytes, uint16BE, headerSize]
    change 2 + 2 = 4
    rfl
  · simp [encode, hsize] at h

end LeanS7.TPKT
