import LeanS7.ResponseDecoderAssurance

/-! Canonical form of the request-context response decoders.

These decoders read an already-framed `Response` (see `S7.decodeResponse_canonical`)
in the context of the request that produced it. Each theorem pins the response's
reference, error bytes, and exact parameter and data bytes as a function of the
decoded value and the request context. Together with `S7.decodeResponse_canonical`,
that fixes every byte of an accepted response except the reserved header word, the
PDU type (`validateResponse` accepts ACK and ACK_DATA alike) and any choice a
theorem states explicitly. -/

namespace LeanS7.S7

/-- A one-byte input is the byte it holds. -/
private theorem eq_bytes_one (data : ByteArray) (h : data.size = 1) :
    data = bytes #[data[0]'(by omega)] := by
  conv => lhs; rw [← ByteArray.extract_zero_size (b := data), h]
  exact ByteArray.extract_one data 0 (by omega)

/-- A two-byte input is the two bytes it holds. -/
private theorem eq_bytes_two (data : ByteArray) (h : data.size = 2) :
    data = bytes #[data[0]'(by omega), data[1]'(by omega)] := by
  conv => lhs; rw [← ByteArray.extract_zero_size (b := data), h]
  exact ByteArray.extract_two data 0 (by omega)

/-- Canonical form of a DB-write acknowledgement: the only accepted sections are
    the write function with one item, and a single success return code. -/
theorem decodeDbWrite_canonical (reference : UInt16) (response : Response)
    (h : decodeDbWrite reference response = .ok ()) :
    response.reference = reference ∧ response.errorClass = 0 ∧ response.errorCode = 0 ∧
      response.parameters = bytes #[writeFunction, 1] ∧ response.data = bytes #[0xff] := by
  simp only [decodeDbWrite, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i xv vv ev hpsize xc vc ec xf vf ef hcount hdsize xr vr er xg vg eg hcode
  obtain ⟨href, hclass, hcode', _, hfun⟩ := validateResponse_exact _ _ _ ev
  obtain ⟨_, hcountByte, _⟩ := Cursor.readUInt8_value _ _ _ ec
  obtain ⟨_, hcodeByte, _⟩ := Cursor.readUInt8_value _ _ _ er
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hpsize hcount hdsize hcode
  refine ⟨href, hclass, hcode', ?_, ?_⟩
  · rw [eq_bytes_two _ hpsize]
    simp only [← hcount, hfun, ← hcountByte]
  · rw [eq_bytes_one _ hdsize]
    simp only [← hcode, ← hcodeByte]

/-- Canonical form of a setup-communication acknowledgement: its eight parameter
    bytes are the canonical `SetupCommunication.parameters` of the decoded result,
    except byte 1, which the decoder ignores. The data section is not read. -/
theorem decodeSetupCommunication_canonical (reference : UInt16) (response : Response)
    (result : SetupCommunication)
    (h : decodeSetupCommunication reference response = .ok result) :
    response.reference = reference ∧ response.errorClass = 0 ∧ response.errorCode = 0 ∧
      response.parameters.size = 8 ∧
      response.parameters.extract 0 1 = bytes #[setupCommunicationFunction] ∧
      bytes #[setupCommunicationFunction, 0] ++ response.parameters.extract 2 8 =
        result.parameters := by
  simp only [decodeSetupCommunication, bind, Except.bind, pure, Except.pure] at h
  repeat' (split at h)
  all_goals first
    | (exfalso; simp [throw, throwThe, MonadExceptOf.throw] at ‹throw _ = _›; done)
    | (simp at h; done)
    | skip
  rename_i xv vv ev hpsize xa va ea xb vb eb xc vc ec xf vf ef xl vl el
  obtain ⟨href, hclass, hcode, hp0, hfun⟩ := validateResponse_exact _ _ _ ev
  obtain ⟨la, da, na⟩ := Cursor.readUInt16BE_value _ _ _ ea
  rw [na] at eb
  obtain ⟨lb, db, nb⟩ := Cursor.readUInt16BE_value _ _ _ eb
  rw [nb] at ec
  obtain ⟨lc, dc, nc⟩ := Cursor.readUInt16BE_value _ _ _ ec
  injection h with h
  subst h
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hpsize
  simp only at la lb lc da db dc
  refine ⟨href, hclass, hcode, hpsize, ?_, ?_⟩
  · rw [ByteArray.extract_one _ 0 hp0, hfun]
    rfl
  · simp only [SetupCommunication.parameters, ByteArray.append_assoc]
    rw [da, db, dc, ← ByteArray.extract_two_uint16BE _ 2 (by omega),
      ← ByteArray.extract_two_uint16BE _ (2 + 2) (by omega),
      ← ByteArray.extract_two_uint16BE _ (2 + 2 + 2) (by omega),
      ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
      ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]

/-- A read item that a cursor walk consumes completely is its return code, its
    transport size, its length word and its payload, in that order. -/
private theorem readItem_layout (data : ByteArray) (code size : UInt8 × Cursor)
    (length : UInt16 × Cursor) (payload : ByteArray × Cursor) (count : Nat) (done : Unit)
    (ecode : ({ data } : Cursor).readUInt8 = .ok code) (esize : code.snd.readUInt8 = .ok size)
    (elength : size.snd.readUInt16BE = .ok length)
    (epayload : length.snd.readBytes count = .ok payload) (efinish : payload.snd.finish = .ok done) :
    data = bytes #[code.fst, size.fst] ++ uint16BE length.fst ++ payload.fst ∧
      payload.fst.size = count := by
  obtain ⟨lc, dc, nc⟩ := Cursor.readUInt8_value _ _ _ ecode
  rw [nc] at esize
  obtain ⟨ls, ds, ns⟩ := Cursor.readUInt8_value _ _ _ esize
  rw [ns] at elength
  obtain ⟨ll, dl, nl⟩ := Cursor.readUInt16BE_value _ _ _ elength
  rw [nl] at epayload
  obtain ⟨pp, np⟩ := Cursor.readBytes_value _ _ _ _ epayload
  rw [np] at efinish
  have hfin := Cursor.finish_ok _ (by cases done; exact efinish)
  simp only at lc ls ll dc ds dl hfin pp
  refine ⟨?_, ?_⟩
  · rw [pp, dl, ← dc, ← ds, ← ByteArray.extract_two_uint16BE _ (0 + 1 + 1) (by omega),
      show bytes #[data[0], data[0 + 1]] = data.extract 0 2 from
        (ByteArray.extract_two data 0 (by omega)).symm,
      ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
      ByteArray.extract_append_extract_of_le _ (by omega) (by omega), hfin,
      ByteArray.extract_zero_size]
  · rw [pp, ByteArray.size_extract]; omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Canonical form of a single-item read response: the parameter section is the
    read function with one item, and the data section is a success return code,
    the transport size, the length field and exactly the returned payload. The
    only choice is the transport size: the area's own, or for counters and timers
    also the byte transport size. -/
theorem decodeAreaRead_canonical (reference : UInt16) (area : Area) (expectedSize : Nat)
    (response : Response) (payload : ByteArray)
    (h : decodeAreaRead reference area expectedSize response = .ok payload) :
    response.reference = reference ∧ response.errorClass = 0 ∧ response.errorCode = 0 ∧
      response.parameters = bytes #[readFunction, 1] ∧ payload.size = expectedSize ∧
      ∃ transportSize : UInt8,
        (transportSize = area.dataTransportSize ∨
          (area.usesElementAddress = true ∧ transportSize = byteTransportSize)) ∧
        response.data = bytes #[0xff, transportSize] ++
          uint16BE (UInt16.ofNat (readItemLength transportSize payload.size)) ++ payload := by
  unfold decodeAreaRead at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  · -- Octet transport size: the length field counts bytes.
    rename_i xv vv ev hpsize xc vc ec xf vf ef hcount hdsize xr vr er hret xt vt et hts
      xl vl el hoct hexp xp vp ep xd vd ed
    obtain ⟨href, hclass, hcode, _, hfun⟩ := validateResponse_exact _ _ _ ev
    obtain ⟨_, hcountByte, _⟩ := Cursor.readUInt8_value _ _ _ ec
    obtain ⟨hdata, hsize⟩ := readItem_layout _ _ _ _ _ _ _ er et el ep ed
    injection h with h
    subst h
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hpsize hcount hret hexp
    simp only [beq_iff_eq] at hoct
    refine ⟨href, hclass, hcode, ?_, by omega, vt.fst, ?_, ?_⟩
    · rw [eq_bytes_two _ hpsize]
      simp only [← hcount, hfun, ← hcountByte]
    · simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', Bool.and_eq_false_iff] at hts
      by_cases hc : vt.fst = area.dataTransportSize
      · exact .inl hc
      · right; simpa [hc] using hts
    · rw [hdata, hret, readItemLength, hoct, hsize]
      simp [UInt16.ofNat_toNat]
  · -- Byte transport size: the length field counts bits.
    rename_i xv vv ev hpsize xc vc ec xf vf ef hcount hdsize xr vr er hret xt vt et hts
      xl vl el hoct hmod hexp xp vp ep xd vd ed
    obtain ⟨href, hclass, hcode, _, hfun⟩ := validateResponse_exact _ _ _ ev
    obtain ⟨_, hcountByte, _⟩ := Cursor.readUInt8_value _ _ _ ec
    obtain ⟨hdata, hsize⟩ := readItem_layout _ _ _ _ _ _ _ er et el ep ed
    injection h with h
    subst h
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hpsize hcount hret hexp hmod
    simp only [beq_iff_eq] at hoct
    refine ⟨href, hclass, hcode, ?_, by omega, vt.fst, ?_, ?_⟩
    · rw [eq_bytes_two _ hpsize]
      simp only [← hcount, hfun, ← hcountByte]
    · simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', Bool.and_eq_false_iff] at hts
      by_cases hc : vt.fst = area.dataTransportSize
      · exact .inl hc
      · right; simpa [hc] using hts
    · rw [hdata, hret, readItemLength, if_neg (by simpa using hoct), hsize,
        Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod), UInt16.ofNat_toNat]

/-- Canonical form of a DB read response: data blocks have a single transport size,
    so the accepted response is fully determined by the returned payload. The length
    field counts bits. -/
theorem decodeDbRead_canonical (reference : UInt16) (response : Response) (payload : ByteArray)
    (h : decodeDbRead reference response = .ok payload) :
    response.reference = reference ∧ response.errorClass = 0 ∧ response.errorCode = 0 ∧
      response.parameters = bytes #[readFunction, 1] ∧
      response.data = bytes #[0xff, byteTransportSize] ++
        uint16BE (UInt16.ofNat (payload.size * 8)) ++ payload := by
  obtain ⟨size, hread⟩ := decodeDbRead_reduces _ _ _ h
  obtain ⟨href, hclass, hcode, hparams, _, transportSize, hts, hdata⟩ :=
    decodeAreaRead_canonical _ _ _ _ _ hread
  have hbyte : transportSize = byteTransportSize := by
    rcases hts with hts | ⟨helement, _⟩
    · exact hts
    · cases helement
  refine ⟨href, hclass, hcode, hparams, ?_⟩
  rw [hdata, hbyte, readItemLength]
  rfl

end LeanS7.S7
