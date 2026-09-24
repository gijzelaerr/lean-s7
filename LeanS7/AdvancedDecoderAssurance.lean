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

end LeanS7.S7
