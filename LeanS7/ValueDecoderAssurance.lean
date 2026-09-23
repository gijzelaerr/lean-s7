import LeanS7.Value

namespace LeanS7.Value

/-- A successful byte read cannot leave the input or move by an unexpected amount. -/
private theorem byte_read_bounds (cursor next : Cursor) (value : UInt8)
    (h : cursor.readUInt8 = .ok (value, next)) :
    cursor.offset < cursor.data.size ∧ next.data = cursor.data ∧
      next.offset = cursor.offset + 1 := by
  unfold Cursor.readUInt8 at h
  split at h
  · cases h
    exact ⟨by assumption, rfl, rfl⟩
  · contradiction

/-- A successful word read has two bytes available and advances exactly twice. -/
private theorem word_read_bounds (cursor next : Cursor) (value : UInt16)
    (h : cursor.readUInt16BE = .ok (value, next)) :
    cursor.offset + 2 ≤ cursor.data.size ∧ next.data = cursor.data ∧
      next.offset = cursor.offset + 2 := by
  unfold Cursor.readUInt16BE at h
  cases hfirst : cursor.readUInt8 with
  | error error => simp [hfirst, bind, Except.bind] at h
  | ok pair =>
    rcases pair with ⟨high, middle⟩
    cases hsecond : middle.readUInt8 with
    | error error => simp [hfirst, hsecond, bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨low, final⟩
      simp only [hfirst, hsecond, bind, Except.bind, pure, Except.pure] at h
      have ha := byte_read_bounds cursor middle high hfirst
      have hb := byte_read_bounds middle final low hsecond
      cases h
      rw [ha.2.1] at hb
      exact ⟨by omega, hb.2.1, by omega⟩

theorem decodeString_invalid_capacity (pre body : ByteArray) (maximum current : UInt8)
    (hmax : maxStringLength < maximum.toNat) :
    decodeString (pre ++ (putUInt8 maximum ++ (putUInt8 current ++ body))) pre.size =
      .error (.invalidMaximumLength maximum.toNat maxStringLength) := by
  unfold decodeString
  simp only [putUInt8]
  change ((Cursor.readUInt8 { data := pre ++ (bytes #[maximum] ++ (bytes #[current] ++ body)), offset := pre.size }).mapError Error.decode >>= _) = _
  rw [Cursor.readUInt8_append_byte]
  simp only [Except.mapError, bind, Except.bind]
  have hsecond := Cursor.readUInt8_append_byte (pre ++ bytes #[maximum]) body current
  simp only [ByteArray.size_append, bytes_size, ByteArray.append_assoc] at hsecond
  have hsingle : (#[maximum] : Array UInt8).size = 1 := rfl
  rw [hsingle] at hsecond
  rw [hsecond]
  change (if maximum.toNat > maxStringLength then _ else _) = _
  rw [if_pos hmax]
  rfl

theorem decodeString_invalid_current (pre body : ByteArray) (maximum current : UInt8)
    (hmax : maximum.toNat ≤ maxStringLength) (hcurrent : maximum < current) :
    decodeString (pre ++ (putUInt8 maximum ++ (putUInt8 current ++ body))) pre.size =
      .error (.invalidStringHeader current.toNat maximum.toNat) := by
  unfold decodeString
  simp only [putUInt8]
  change ((Cursor.readUInt8 { data := pre ++ (bytes #[maximum] ++ (bytes #[current] ++ body)), offset := pre.size }).mapError Error.decode >>= _) = _
  rw [Cursor.readUInt8_append_byte]
  simp only [Except.mapError, bind, Except.bind]
  have hsecond := Cursor.readUInt8_append_byte (pre ++ bytes #[maximum]) body current
  simp only [ByteArray.size_append, bytes_size, ByteArray.append_assoc] at hsecond
  have hsingle : (#[maximum] : Array UInt8).size = 1 := rfl
  rw [hsingle] at hsecond
  rw [hsecond]
  change (if maximum.toNat > maxStringLength then _ else _) = _
  rw [if_neg (by omega)]
  change (if current > maximum then _ else _) = _
  rw [if_pos hcurrent]
  rfl

theorem decodeWString_invalid_capacity (pre body : ByteArray) (maximum current : UInt16)
    (hmax : maxWStringLength < maximum.toNat) :
    decodeWString (pre ++ (uint16BE maximum ++ (uint16BE current ++ body))) pre.size =
      .error (.invalidMaximumLength maximum.toNat maxWStringLength) := by
  unfold decodeWString
  change ((Cursor.readUInt16BE { data := pre ++ (uint16BE maximum ++ (uint16BE current ++ body)), offset := pre.size }).mapError Error.decode >>= _) = _
  rw [Cursor.readUInt16BE_append_uint16BE]
  simp only [Except.mapError, bind, Except.bind]
  have hsecond := Cursor.readUInt16BE_append_uint16BE (pre ++ uint16BE maximum) body current
  simp only [ByteArray.size_append, uint16BE_size, ByteArray.append_assoc] at hsecond
  rw [hsecond]
  change (if maximum.toNat > maxWStringLength then _ else _) = _
  rw [if_pos hmax]
  rfl

theorem decodeWString_invalid_current (pre body : ByteArray) (maximum current : UInt16)
    (hmax : maximum.toNat ≤ maxWStringLength) (hcurrent : maximum < current) :
    decodeWString (pre ++ (uint16BE maximum ++ (uint16BE current ++ body))) pre.size =
      .error (.invalidStringHeader current.toNat maximum.toNat) := by
  unfold decodeWString
  change ((Cursor.readUInt16BE { data := pre ++ (uint16BE maximum ++ (uint16BE current ++ body)), offset := pre.size }).mapError Error.decode >>= _) = _
  rw [Cursor.readUInt16BE_append_uint16BE]
  simp only [Except.mapError, bind, Except.bind]
  have hsecond := Cursor.readUInt16BE_append_uint16BE (pre ++ uint16BE maximum) body current
  simp only [ByteArray.size_append, uint16BE_size, ByteArray.append_assoc] at hsecond
  rw [hsecond]
  change (if maximum.toNat > maxWStringLength then _ else _) = _
  rw [if_neg (by omega)]
  change (if current > maximum then _ else _) = _
  rw [if_pos hcurrent]
  rfl

/-- Acceptance of arbitrary untrusted STRING data implies valid header values
    and the entire allocation (not just active bytes) is inside the input. -/
theorem decodeString_success_valid (data : ByteArray) (offset : Nat) (value : String)
    (h : decodeString data offset = .ok value) :
    ∃ maximum current : UInt8,
      getUInt8 data offset = .ok maximum ∧ getUInt8 data (offset + 1) = .ok current ∧
      maximum.toNat ≤ maxStringLength ∧ current ≤ maximum ∧
      offset + 2 + maximum.toNat ≤ data.size := by
  unfold decodeString at h
  change ((Cursor.readUInt8 { data, offset }).mapError Error.decode >>= _) = _ at h
  cases hfirst : (Cursor.readUInt8 { data, offset }) with
  | error error => simp [hfirst, Except.mapError, bind, Except.bind] at h
  | ok pair =>
    rcases pair with ⟨maximum, middle⟩
    have ha := byte_read_bounds { data, offset } middle maximum hfirst
    simp only [hfirst, Except.mapError, bind, Except.bind] at h
    change (middle.readUInt8.mapError Error.decode >>= _) = _ at h
    cases hsecond : middle.readUInt8 with
    | error error => simp [hsecond, Except.mapError, bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨current, contentCursor⟩
      have hb := byte_read_bounds middle contentCursor current hsecond
      simp only [hsecond, Except.mapError, bind, Except.bind] at h
      change (if maximum.toNat > maxStringLength then _ else _) = _ at h
      split at h
      · contradiction
      · rename_i hmax
        change (if current > maximum then _ else _) = _ at h
        split at h
        · contradiction
        · rename_i hcurrent
          change ((contentCursor.readBytes maximum.toNat).mapError Error.decode >>= _) = _ at h
          unfold Cursor.readBytes at h
          split at h
          · rename_i havailable
            have hreadCurrent : getUInt8 data (offset + 1) = .ok current := by
              unfold getUInt8
              change ((Cursor.readUInt8 { data, offset := offset + 1 }).mapError Error.decode >>= _) = _
              have hmiddle : middle = { data, offset := offset + 1 } := by
                cases middle
                simp_all
              rw [← hmiddle, hsecond]
              rfl
            refine ⟨maximum, current, ?_, hreadCurrent, by omega, ?_, ?_⟩
            · unfold getUInt8
              change ((Cursor.readUInt8 { data, offset }).mapError Error.decode >>= _) = _
              rw [hfirst]
              rfl
            · simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] at *
              omega
            · simp only [Cursor.remaining] at havailable
              simp only at ha hb
              rw [ha.2.1] at hb
              rw [hb.2.1] at havailable
              omega
          · contradiction

/-- WSTRING acceptance bounds both UTF-16 header counts and all reserved bytes.
    This does not assume that the data came from the encoder. -/
theorem decodeWString_success_valid (data : ByteArray) (offset : Nat) (value : String)
    (h : decodeWString data offset = .ok value) :
    ∃ maximum current : UInt16,
      getUInt16 data offset = .ok maximum ∧ getUInt16 data (offset + 2) = .ok current ∧
      maximum.toNat ≤ maxWStringLength ∧ current ≤ maximum ∧
      offset + 4 + maximum.toNat * 2 ≤ data.size := by
  unfold decodeWString at h
  change ((Cursor.readUInt16BE { data, offset }).mapError Error.decode >>= _) = _ at h
  cases hfirst : (Cursor.readUInt16BE { data, offset }) with
  | error error => simp [hfirst, Except.mapError, bind, Except.bind] at h
  | ok pair =>
    rcases pair with ⟨maximum, middle⟩
    have ha := word_read_bounds { data, offset } middle maximum hfirst
    simp only [hfirst, Except.mapError, bind, Except.bind] at h
    change (middle.readUInt16BE.mapError Error.decode >>= _) = _ at h
    cases hsecond : middle.readUInt16BE with
    | error error => simp [hsecond, Except.mapError, bind, Except.bind] at h
    | ok pair =>
      rcases pair with ⟨current, contentCursor⟩
      have hb := word_read_bounds middle contentCursor current hsecond
      simp only [hsecond, Except.mapError, bind, Except.bind] at h
      change (if maximum.toNat > maxWStringLength then _ else _) = _ at h
      split at h
      · contradiction
      · rename_i hmax
        change (if current > maximum then _ else _) = _ at h
        split at h
        · contradiction
        · rename_i hcurrent
          split at h
          · contradiction
          · change ((contentCursor.readBytes (maximum.toNat * 2)).mapError Error.decode >>= _) = _ at h
            unfold Cursor.readBytes at h
            split at h
            · rename_i havailable
              have hreadCurrent : getUInt16 data (offset + 2) = .ok current := by
                unfold getUInt16
                change ((Cursor.readUInt16BE { data, offset := offset + 2 }).mapError Error.decode >>= _) = _
                have hmiddle : middle = { data, offset := offset + 2 } := by
                  cases middle
                  simp_all
                rw [← hmiddle, hsecond]
                rfl
              refine ⟨maximum, current, ?_, hreadCurrent, by omega, ?_, ?_⟩
              · unfold getUInt16
                change ((Cursor.readUInt16BE { data, offset }).mapError Error.decode >>= _) = _
                rw [hfirst]
                rfl
              · simp only [UInt16.le_iff_toNat_le, UInt16.lt_iff_toNat_lt] at *
                omega
              · simp only [Cursor.remaining] at havailable
                simp only at ha hb
                rw [ha.2.1] at hb
                rw [hb.2.1] at havailable
                omega
            · contradiction

/-- Incomplete headers never decode, at any offset, even beyond the input. -/
theorem decodeString_incomplete_header (data : ByteArray) (offset : Nat) (value : String)
    (hshort : data.size < offset + 2) : decodeString data offset ≠ .ok value := by
  intro h
  obtain ⟨maximum, current, _, _, _, _, hsize⟩ := decodeString_success_valid data offset value h
  omega

theorem decodeWString_incomplete_header (data : ByteArray) (offset : Nat) (value : String)
    (hshort : data.size < offset + 4) : decodeWString data offset ≠ .ok value := by
  intro h
  obtain ⟨maximum, current, _, _, _, _, hsize⟩ := decodeWString_success_valid data offset value h
  omega

/-- STRING refuses a short allocation even when its active content would fit. -/
theorem decodeString_incomplete_allocation (pre body : ByteArray) (maximum current : UInt8)
    (hmax : maximum.toNat ≤ maxStringLength) (hcurrent : current ≤ maximum)
    (hshort : body.size < maximum.toNat) :
    decodeString (pre ++ (putUInt8 maximum ++ (putUInt8 current ++ body))) pre.size =
      .error (.decode (.unexpectedEnd (pre.size + 2) maximum.toNat body.size)) := by
  unfold decodeString
  simp only [putUInt8]
  change ((Cursor.readUInt8 { data := pre ++ (bytes #[maximum] ++ (bytes #[current] ++ body)), offset := pre.size }).mapError Error.decode >>= _) = _
  rw [Cursor.readUInt8_append_byte]
  simp only [Except.mapError, bind, Except.bind]
  have hsecond := Cursor.readUInt8_append_byte (pre ++ bytes #[maximum]) body current
  simp only [ByteArray.size_append, bytes_size, ByteArray.append_assoc] at hsecond
  have hsingle : (#[maximum] : Array UInt8).size = 1 := rfl
  rw [hsingle] at hsecond
  rw [hsecond]
  change (if maximum.toNat > maxStringLength then _ else _) = _
  rw [if_neg (by omega)]
  change (if current > maximum then _ else _) = _
  have hactive : ¬ current > maximum := by
    simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] at *
    omega
  rw [if_neg hactive]
  change ((Cursor.readBytes { data := pre ++ (bytes #[maximum] ++ (bytes #[current] ++ body)), offset := pre.size + 1 + 1 } maximum.toNat).mapError Error.decode >>= _) = _
  have hremaining : Cursor.remaining { data := pre ++ (bytes #[maximum] ++ (bytes #[current] ++ body)), offset := pre.size + 1 + 1 } = body.size := by
    simp only [Cursor.remaining, ByteArray.size_append, bytes_size]
    change pre.size + (1 + (1 + body.size)) - (pre.size + 1 + 1) = body.size
    omega
  rw [Cursor.readBytes, hremaining, if_neg (by omega)]
  have hoffset : pre.size + 1 + 1 = pre.size + 2 := by omega
  rw [hoffset]
  rfl

/-- No WSTRING with an incomplete declared allocation can be accepted. Active
    reads can fail earlier, so this specifies rejection, not one error offset. -/
theorem decodeWString_incomplete_allocation (pre body : ByteArray) (maximum current : UInt16)
    (value : String) (hshort : body.size < maximum.toNat * 2) :
    decodeWString (pre ++ (uint16BE maximum ++ (uint16BE current ++ body))) pre.size ≠
      .ok value := by
  intro h
  obtain ⟨decodedMaximum, decodedCurrent, hheader, _, _, _, hsize⟩ :=
    decodeWString_success_valid _ _ value h
  have hgetter : getUInt16 (pre ++ (uint16BE maximum ++ (uint16BE current ++ body)))
      pre.size = .ok maximum := by
    unfold getUInt16
    change ((Cursor.readUInt16BE { data := pre ++ (uint16BE maximum ++ (uint16BE current ++ body)), offset := pre.size }).mapError Error.decode >>= _) = _
    rw [Cursor.readUInt16BE_append_uint16BE]
    rfl
  rw [hgetter] at hheader
  cases hheader
  simp only [ByteArray.size_append, uint16BE_size] at hsize
  omega

end LeanS7.Value
