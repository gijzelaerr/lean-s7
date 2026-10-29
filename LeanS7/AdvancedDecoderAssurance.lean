import LeanS7.Advanced

namespace LeanS7.S7

/-- Every supported block type has an unambiguous wire discriminator. -/
theorem BlockType.ofCode_code (blockType : BlockType) :
    BlockType.ofCode blockType.code = some blockType := by
  cases blockType <;> rfl

/-- Supported block-type discriminators are injective. -/
theorem BlockType.code_injective (left right : BlockType)
    (h : left.code = right.code) : left = right := by
  have := congrArg BlockType.ofCode h
  simpa only [BlockType.ofCode_code, Option.some.injEq] using this

/-- The supported correlated-client number profile fits the response field. -/
theorem validateBlockInfoNumber_bound (number : Nat)
    (h : validateBlockInfoNumber number = .ok ()) : number ≤ 65535 := by
  by_cases hn : number > 65535
  · simp [validateBlockInfoNumber, hn, throw] at h
  · omega

/-- Successful correlation never aliases a large requested number by truncation. -/
theorem correlateBlockInfo_number (number : Nat) (info result : BlockInfo)
    (h : correlateBlockInfo number info = .ok result) : result.number.toNat = number := by
  by_cases hn : info.number.toNat = number
  · simp [correlateBlockInfo, hn, pure, Except.pure] at h
    subst result
    exact hn
  · simp [correlateBlockInfo, hn, bind, Except.bind, throw] at h

/-- Numeric correlation does not normalize or erase either type field. -/
theorem correlateBlockInfo_identity (number : Nat) (info result : BlockInfo)
    (h : correlateBlockInfo number info = .ok result) : result = info := by
  unfold correlateBlockInfo at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · contradiction
  · exact (Except.ok.inj h).symm

/-- Successful decoding of arbitrary count payloads requires seven complete
    four-byte records. This theorem is not restricted to encoded fixtures. -/
theorem decodeBlockCounts_extent (payload : ByteArray) (result : BlockCounts)
    (h : decodeBlockCounts payload = .ok result) : payload.size = 28 := by
  by_cases hn : payload.size = 28
  · exact hn
  · simp [decodeBlockCounts, hn, bind, Except.bind, throw] at h

/-- A successful block-list payload has no incomplete trailing record. -/
theorem decodeBlockEntries_alignment (payload : ByteArray) (result : Array BlockEntry)
    (h : decodeBlockEntries payload = .ok result) : payload.size % 4 = 0 := by
  by_cases hn : payload.size % 4 = 0
  · exact hn
  · simp [decodeBlockEntries, hn, bind, Except.bind, throw] at h

/-- Block metadata success requires the entire exact 78-byte structure, not
    merely enough bytes to read its exposed fields. -/
theorem decodeBlockInfo_extent (payload : ByteArray) (result : BlockInfo)
    (h : decodeBlockInfo payload = .ok result) : payload.size = 78 := by
  by_cases hs : payload.size < 78
  · simp [decodeBlockInfo, hs, bind, Except.bind, throw] at h
  · by_cases hl : payload.size > 78
    · simp [decodeBlockInfo, hs, hl, bind, Except.bind, throw] at h
    · omega

set_option maxRecDepth 4096 in
/-- The two raw timestamp fields always retain their exact wire positions. -/
theorem decodeBlockInfo_date_order (payload : ByteArray) (result : BlockInfo)
    (h : decodeBlockInfo payload = .ok result) :
    result.codeDateRaw = payload.extract 22 28 ∧
      result.interfaceDateRaw = payload.extract 28 34 := by
  unfold decodeBlockInfo at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  repeat' (first | contradiction | split at h)
  simp only [Except.ok.injEq] at h
  subst result
  exact ⟨rfl, rfl⟩

/-- Every accepted block metadata packet exposes both complete six-byte dates. -/
theorem decodeBlockInfo_date_sizes (payload : ByteArray) (result : BlockInfo)
    (h : decodeBlockInfo payload = .ok result) :
    result.codeDateRaw.size = 6 ∧ result.interfaceDateRaw.size = 6 := by
  have hs := decodeBlockInfo_extent payload result h
  have ho := decodeBlockInfo_date_order payload result h
  rw [ho.1, ho.2]
  simp [ByteArray.size_extract, hs]

/-- Force-table decoding never accepts a different SZL discriminator. -/
theorem decodeForceTable_id (szl : Szl) (result : Array ForceEntry)
    (h : decodeForceTable szl = .ok result) : szl.id = 0x0025 := by
  by_cases hn : szl.id = 0x0025
  · exact hn
  · simp [decodeForceTable, validateSzlData, hn, bind, Except.bind, throw] at h
    split at h <;> contradiction

/-- Every successful force table contains complete eight-byte records. -/
theorem decodeForceTable_alignment (szl : Szl) (result : Array ForceEntry)
    (h : decodeForceTable szl = .ok result) : szl.data.size % 8 = 0 := by
  by_cases hi : szl.id = 0x0025
  · by_cases hn : szl.data.size % 8 = 0
    · exact hn
    · simp [decodeForceTable, validateSzlData, hi, hn, bind, Except.bind, throw] at h
      split at h <;> contradiction
  · simp [decodeForceTable, validateSzlData, hi, bind, Except.bind, throw] at h
    split at h <;> contradiction

/-- Public force-table decoding cannot bypass the SZL header/data extent. -/
theorem decodeForceTable_extent (szl : Szl) (result : Array ForceEntry)
    (h : decodeForceTable szl = .ok result) :
    szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat := by
  by_cases he : szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat
  · exact he
  · simp [decodeForceTable, validateSzlData, he, bind, Except.bind, throw] at h

/-- Typed parsers validate the public `Szl` structure even when callers do not
    obtain it through the transport-facing SZL decoder. -/
theorem parseOrderCode_extent (szl : Szl) (result : OrderCode)
    (h : parseOrderCode szl = .ok result) :
    szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat := by
  by_cases he : szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat
  · exact he
  · simp [parseOrderCode, validateSzlData, he, bind, Except.bind, throw] at h

theorem parseCpuInfo_extent (szl : Szl) (result : CpuInfo)
    (h : parseCpuInfo szl = .ok result) :
    szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat := by
  by_cases he : szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat
  · exact he
  · simp [parseCpuInfo, validateSzlData, he, bind, Except.bind, throw] at h

theorem parseCpInfo_extent (szl : Szl) (result : CpInfo)
    (h : parseCpInfo szl = .ok result) :
    szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat := by
  by_cases he : szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat
  · exact he
  · simp [parseCpInfo, validateSzlData, he, bind, Except.bind, throw] at h

theorem parseProtection_extent (szl : Szl) (result : Protection)
    (h : parseProtection szl = .ok result) :
    szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat := by
  by_cases he : szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat
  · exact he
  · simp [parseProtection, validateSzlData, he, bind, Except.bind, throw] at h

theorem parseCpuState_extent (szl : Szl) (result : CpuState)
    (h : parseCpuState szl = .ok result) :
    szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat := by
  by_cases he : szl.data.size = szl.recordLength.toNat * szl.recordCount.toNat
  · exact he
  · simp [parseCpuState, validateSzlData, he, bind, Except.bind, throw] at h

/-- What one eight-byte force-table entry at `start` pins down: bytes 0–4 are exactly the
    area code, byte offset and bit index, and byte 5 is zero exactly when the entry's
    value is false. Bytes 6–7 are not read. -/
def ForceEntryBytes (data : ByteArray) (start : Nat) (entry : ForceEntry) : Prop :=
  start + 8 ≤ data.size ∧
    data.extract start (start + 5) =
      uint16BE entry.areaCode ++ uint16BE entry.byteOffset ++ bytes #[entry.bit] ∧
    ∃ valueByte : UInt8, data.extract (start + 5) (start + 6) = bytes #[valueByte] ∧
      entry.value = (valueByte != 0)

/-- Canonical form of the force table: the SZL data holds exactly one eight-byte entry
    per decoded entry, in order, and each decoded entry is what its entry bytes say. -/
theorem decodeForceTable_canonical (szl : Szl) (entries : Array ForceEntry)
    (h : decodeForceTable szl = .ok entries) :
    szl.data.size = 8 * entries.size ∧
      ∀ i (hi : i < entries.size), ForceEntryBytes szl.data (8 * i) entries[i] := by
  unfold decodeForceTable at h
  simp only [validateSzlData, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw, Std.Legacy.Range.forIn_eq_forIn_range'] at h
  repeat' (first | contradiction | split at h)
  rename_i x0 v0 e0 hid halign x1 v1 hloop x2 v2 hfin
  injection h with h
  subst h
  generalize hl : List.range' _ _ _ = l at hloop
  generalize hc0 : ({ data := szl.data } : Cursor) = c0 at hloop
  generalize hr0 : (#[] : Array ForceEntry) = r0 at hloop
  -- The loop invariant: each iteration consumes eight bytes and appends their entry.
  have inv : v1.fst.data = c0.data ∧ v1.fst.offset = c0.offset + 8 * l.length ∧
      ∃ added : Array ForceEntry, v1.snd = r0 ++ added ∧ added.size = l.length ∧
        ∀ j (hj : j < added.size), ForceEntryBytes c0.data (c0.offset + 8 * j) added[j] := by
    clear hc0 hr0 hl hfin
    induction l generalizing c0 r0 with
    | nil =>
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hloop
      subst hloop
      exact ⟨rfl, by simp, #[], by simp, rfl, by simp⟩
    | cons index rest ih =>
      simp only [List.forIn_cons, bind, Except.bind] at hloop
      repeat' (first | contradiction | split at hloop)
      all_goals
        rename_i step result hbody
        repeat' (first | contradiction | split at hbody)
      all_goals first
        | (simp at hbody; done)
        | skip
      rename_i xa va ea xb vb eb xc vc ec hbit xd vd ed xf vf ef
      injection hbody with hb
      injection hb with hb
      subst hb
      obtain ⟨la, da, na⟩ := Cursor.readUInt16BE_value _ _ _ ea
      rw [na] at eb
      obtain ⟨lb, db, nb⟩ := Cursor.readUInt16BE_value _ _ _ eb
      rw [nb] at ec
      obtain ⟨lc, dc, nc⟩ := Cursor.readUInt8_value _ _ _ ec
      rw [nc] at ed
      obtain ⟨ld, dd, nd⟩ := Cursor.readUInt8_value _ _ _ ed
      rw [nd] at ef
      obtain ⟨lf, -, nf⟩ := Cursor.readUInt16BE_value _ _ _ ef
      rw [nf] at hloop
      obtain ⟨ihd, iho, added, hadd, hsize, hentries⟩ := ih _ _ hloop
      simp only at la lb lc ld lf da db dc dd ihd iho hentries
      refine ⟨ihd, by simp only [List.length_cons]; omega,
        #[{ areaCode := va.fst, byteOffset := vb.fst, bit := vc.fst, value := vd.fst != 0 }] ++ added,
        ?_, ?_, ?_⟩
      · rw [hadd, Array.push_eq_append, Array.append_assoc]
      · simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil, hsize]
        omega
      · intro j hj
        cases j with
        | zero =>
          simp only [Nat.mul_zero, Nat.add_zero]
          rw [Array.getElem_append_left (by simp)]
          simp only [List.getElem_toArray, List.getElem_cons_zero]
          refine ⟨by omega, ?_, vd.fst, ?_, rfl⟩
          · rw [da, db, ← dc, ← ByteArray.extract_two_uint16BE _ _ (by omega),
              ← ByteArray.extract_two_uint16BE _ _ (by omega),
              show bytes #[c0.data[c0.offset + 2 + 2]] = c0.data.extract (c0.offset + 4) (c0.offset + 5)
                from (ByteArray.extract_one c0.data (c0.offset + 4) (by omega)).symm,
              ByteArray.extract_append_extract_of_le _ (by omega) (by omega),
              ByteArray.extract_append_extract_of_le _ (by omega) (by omega)]
          · rw [← dd]
            exact ByteArray.extract_one c0.data (c0.offset + 5) (by omega)
        | succ j =>
          have hj' : j < added.size := by simp at hj; omega
          have hentry := hentries j hj'
          rw [Array.getElem_append_right (by simp)]
          simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.add_sub_cancel]
          rw [show c0.offset + 8 * (j + 1) = c0.offset + 1 + 1 + 1 + 1 + 2 + 2 + 8 * j by omega]
          simpa using hentry
  obtain ⟨hd, ho, added, hadd, hsize, hentries⟩ := inv
  subst hc0 hr0
  have hfin' := Cursor.finish_ok _ hfin
  have hlen : l.length = szl.data.size / 8 := by
    rw [← hl, List.length_range']
    simp [Std.Legacy.Range.size]
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at halign
  simp only at ho hentries
  rw [hadd, Array.empty_append]
  refine ⟨by omega, fun i hi => ?_⟩
  simpa using hentries i hi

end LeanS7.S7
