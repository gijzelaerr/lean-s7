import LeanS7.Binary

namespace LeanS7.TPKT

def version : UInt8 := 3
def headerSize : Nat := 4
def minFrameSize : Nat := 7
def maxFrameSize : Nat := 65535

structure Frame where
  payload : ByteArray
  deriving BEq

inductive EncodeError where
  | frameTooSmall (size minimum : Nat)
  | frameTooLarge (size maximum : Nat)
  deriving Repr, BEq

/-- Encode an RFC 1006 TPKT frame. -/
def encode (frame : Frame) : Except EncodeError ByteArray :=
  let length := headerSize + frame.payload.size
  if minFrameSize ≤ length then
    if length ≤ maxFrameSize then
      let header := bytes #[version, 0] ++ uint16BE (UInt16.ofNat length)
      .ok (header ++ frame.payload)
    else
      .error (.frameTooLarge length maxFrameSize)
  else
    .error (.frameTooSmall length minFrameSize)

/-- Decode exactly one RFC 1006 TPKT frame. Trailing or truncated data is rejected. -/
def decode (data : ByteArray) : Except DecodeError Frame := do
  let cursor : Cursor := { data }
  let versionResult ← cursor.readUInt8
  let actualVersion := versionResult.fst
  let cursor := versionResult.snd
  if actualVersion != version then
    throw (.invalidField 0 s!"unsupported TPKT version {actualVersion}")
  let reservedResult ← cursor.readUInt8
  let cursor := reservedResult.snd
  let lengthResult ← cursor.readUInt16BE
  let declaredLength := lengthResult.fst.toNat
  let cursor := lengthResult.snd
  if declaredLength < minFrameSize then
    throw (.invalidField 2 s!"invalid TPKT length {declaredLength}")
  if declaredLength != data.size then
    throw (.invalidField 2 s!"declared length {declaredLength} does not match {data.size} bytes")
  let payloadResult ← cursor.readBytes (declaredLength - headerSize)
  let payload := payloadResult.fst
  let cursor := payloadResult.snd
  cursor.finish
  return { payload }

theorem encode_succeeds_of_size (frame : Frame)
    (hmin : minFrameSize ≤ headerSize + frame.payload.size)
    (hmax : headerSize + frame.payload.size ≤ maxFrameSize) :
    ∃ packet, encode frame = .ok packet := by
  simp [encode, hmin, hmax]

theorem encode_rejects_undersize (frame : Frame)
    (h : headerSize + frame.payload.size < minFrameSize) :
    encode frame = .error (.frameTooSmall
      (headerSize + frame.payload.size) minFrameSize) := by
  simp [encode, Nat.not_le_of_gt h]

theorem encode_rejects_oversize (frame : Frame)
    (h : maxFrameSize < headerSize + frame.payload.size) :
    encode frame = .error (.frameTooLarge
      (headerSize + frame.payload.size) maxFrameSize) := by
  have hmin : minFrameSize ≤ headerSize + frame.payload.size := by
    simp [maxFrameSize, headerSize] at h
    simp [minFrameSize, headerSize]
    omega
  simp [encode, hmin, Nat.not_le_of_gt h]

theorem encoded_size (frame : Frame) (packet : ByteArray)
    (h : encode frame = .ok packet) : packet.size = headerSize + frame.payload.size := by
  by_cases hsize : headerSize + frame.payload.size ≤ maxFrameSize
  · by_cases hmin : minFrameSize ≤ headerSize + frame.payload.size
    · simp [encode, hmin, hsize] at h
      subst packet
      simp [bytes, uint16BE, headerSize]
      change 2 + 2 = 4
      rfl
    · simp [encode, hmin] at h
  · by_cases hmin : minFrameSize ≤ headerSize + frame.payload.size
    · simp [encode, hmin, hsize] at h
    · simp [encode, hmin] at h

/-- Encoding and then decoding a frame returns the original frame. -/
theorem decode_encode (frame : Frame) (packet : ByteArray)
    (hmin : minFrameSize ≤ headerSize + frame.payload.size)
    (hsize : headerSize + frame.payload.size ≤ maxFrameSize)
    (hencode : encode frame = .ok packet) :
    decode packet = .ok frame := by
  let data := bytes #[version, 0] ++
    uint16BE (UInt16.ofNat (headerSize + frame.payload.size)) ++ frame.payload
  have hpacket : packet = data := by
    simpa [encode, hmin, hsize, data] using hencode.symm
  rw [hpacket]
  have hversionRead : Cursor.readUInt8 { data } =
      .ok (version, { data, offset := 1 }) := by
    rw [Cursor.readUInt8_of_lt _ (by
      dsimp only [Cursor.offset, Cursor.data]
      rw [ByteArray.size_append, ByteArray.size_append]
      change 0 < 2 + 2 + frame.payload.size
      omega)]
    congr 2
  have hreservedRead : Cursor.readUInt8 { data, offset := 1 } =
      .ok (0, { data, offset := 2 }) := by
    rw [Cursor.readUInt8_of_lt _ (by
      dsimp only [Cursor.offset, Cursor.data]
      rw [ByteArray.size_append, ByteArray.size_append]
      change 1 < 2 + 2 + frame.payload.size
      omega)]
    congr 2
  have hlengthRead : Cursor.readUInt16BE { data, offset := 2 } =
      .ok (UInt16.ofNat (headerSize + frame.payload.size),
        { data, offset := 4 }) := by
    rw [Cursor.readUInt16BE_of_available _ (by
      dsimp only [Cursor.offset, Cursor.data]
      rw [ByteArray.size_append, ByteArray.size_append]
      change 2 + 2 ≤ 2 + 2 + frame.payload.size
      omega)]
    congr 2
    dsimp only [Cursor.data, Cursor.offset]
    rw [ByteArray.getElem_append_left (i := 2) (by
      rw [ByteArray.size_append]
      change 2 < 2 + 2
      omega)]
    rw [ByteArray.getElem_append_left (i := 3) (by
      rw [ByteArray.size_append]
      change 3 < 2 + 2
      omega)]
    rw [ByteArray.getElem_append_right (i := 2) (by
      change 2 ≤ 2
      omega)]
    rw [ByteArray.getElem_append_right (i := 3) (by
      change 2 ≤ 3
      omega)]
    have hround := readUInt16BE_uint16BE
      (UInt16.ofNat (headerSize + frame.payload.size))
    rw [Cursor.readUInt16BE_of_available _ (by
      change 2 ≤ 2
      omega)] at hround
    injection hround with hpair
    injection hpair with hvalue
  have hlengthLt : headerSize + frame.payload.size < 65536 := by
    simpa [maxFrameSize] using Nat.lt_succ_of_le hsize
  have hlengthLt4 : 4 + frame.payload.size < 65536 := by
    simpa [headerSize] using hlengthLt
  have hdataSize : data.size = headerSize + frame.payload.size := by
    dsimp only [data]
    rw [ByteArray.size_append, ByteArray.size_append]
    change 2 + 2 + frame.payload.size = 4 + frame.payload.size
    omega
  have hpayloadRead : Cursor.readBytes { data, offset := 4 }
      frame.payload.size = .ok
        (frame.payload, { data, offset := 4 + frame.payload.size }) := by
    have hextract : data.extract 4 (4 + frame.payload.size) =
        frame.payload := by
      dsimp only [data]
      apply ByteArray.extract_append_eq_right
      · rw [ByteArray.size_append]
        change 4 = 2 + 2
        omega
      · rw [ByteArray.size_append]
        change 4 + frame.payload.size = 2 + 2 + frame.payload.size
        omega
    rw [Cursor.readBytes]
    rw [if_pos (by simp [Cursor.remaining, hdataSize, headerSize])]
    change Except.ok
      (data.extract 4 (4 + frame.payload.size),
        ({ data, offset := 4 + frame.payload.size } : Cursor)) =
      Except.ok
        (frame.payload, { data, offset := 4 + frame.payload.size })
    rw [hextract]
  rw [decode, hversionRead]
  change Except.bind (Except.ok (version, ({ data, offset := 1 } : Cursor)))
    (fun versionResult => _) = .ok frame
  rw [Except.bind]
  simp
  rw [hreservedRead]
  change Except.bind (Except.ok (0, ({ data, offset := 2 } : Cursor)))
    (fun reservedResult => _) = .ok frame
  rw [Except.bind]
  simp
  rw [hlengthRead]
  change Except.bind (Except.ok
      (UInt16.ofNat (headerSize + frame.payload.size),
        ({ data, offset := 4 } : Cursor)))
    (fun lengthResult => _) = .ok frame
  rw [Except.bind]
  simp [hdataSize, Nat.mod_eq_of_lt hlengthLt4, headerSize,
    minFrameSize]
  rw [if_neg (by simpa [headerSize, minFrameSize] using Nat.not_lt.mpr hmin)]
  rw [hpayloadRead]
  change Except.bind (Except.ok
      (frame.payload, ({ data, offset := 4 + frame.payload.size } : Cursor)))
    (fun payloadResult => _) = .ok frame
  rw [Except.bind]
  simp [Cursor.finish, hdataSize, headerSize]
  change Except.ok { payload := frame.payload } = Except.ok frame
  cases frame
  rfl

end LeanS7.TPKT
