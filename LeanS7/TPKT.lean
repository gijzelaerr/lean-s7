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

/-- Where an accepted frame sits in its input: the payload is everything after the
    four-byte header, the length field encodes the input size, and that size is
    within the TPKT bounds. -/
theorem decode_layout (data : ByteArray) (frame : Frame)
    (h : decode data = .ok frame) :
    frame.payload = data.extract headerSize data.size ∧
      data.extract 2 4 = uint16BE (UInt16.ofNat data.size) ∧
      minFrameSize ≤ data.size ∧ data.size ≤ maxFrameSize := by
  simp only [decode, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i x5 v5 e5 hver x4 v4 e4 x3 v3 e3 hmin hlen x2 v2 e2 x1 v1 e1
  obtain ⟨l5, d5, n5⟩ := Cursor.readUInt8_value _ _ _ e5
  rw [n5] at e4
  obtain ⟨l4, d4, n4⟩ := Cursor.readUInt8_value _ _ _ e4
  rw [n4] at e3
  obtain ⟨l3, d3, n3⟩ := Cursor.readUInt16BE_value _ _ _ e3
  rw [n3] at e2
  obtain ⟨p2, n2⟩ := Cursor.readBytes_value _ _ _ _ e2
  rw [n2] at e1
  have hfin := Cursor.finish_ok _ e1
  injection h with h
  subst h
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hver hlen
  simp only at l5 l4 l3 d5 d4 d3 hfin p2
  have hbound := v3.fst.toNat_lt
  simp only [minFrameSize, headerSize] at hmin hfin p2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show v2.fst = data.extract 4 data.size
    rw [p2]; congr 1 <;> omega
  · rw [← hlen, UInt16.ofNat_toNat, d3, ByteArray.extract_two_uint16BE data 2 (by omega)]
  · rw [minFrameSize]; omega
  · rw [maxFrameSize]; omega

/-- Canonical decoding: re-encoding an accepted frame reproduces the input with
    its reserved byte (offset 1) cleared. That byte is the only input `decode`
    ignores; every other byte, the length field included, is reproduced exactly. -/
theorem decode_canonical (data : ByteArray) (frame : Frame)
    (h : decode data = .ok frame) :
    encode frame = .ok (bytes #[version, 0] ++ data.extract 2 data.size) := by
  obtain ⟨hpayload, hword, hmin, hmax⟩ := decode_layout data frame h
  have hlength : headerSize + frame.payload.size = data.size := by
    rw [hpayload, ByteArray.size_extract]
    simp only [headerSize, minFrameSize, Nat.min_self] at hmin ⊢
    omega
  simp only [encode]
  rw [if_pos (by rw [hlength]; exact hmin), if_pos (by rw [hlength]; exact hmax),
    hlength, ← hword, hpayload, ByteArray.append_assoc, headerSize,
    ByteArray.extract_append_extract_of_le data (by omega)
      (by simp only [minFrameSize] at hmin; omega)]

end LeanS7.TPKT
