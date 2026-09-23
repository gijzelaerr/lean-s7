import LeanS7.Value

namespace LeanS7.Value

private theorem bit_set_true (value index : UInt8) (h : index < 8) :
    (UInt8.land (UInt8.lor value (UInt8.shiftLeft 1 index)) (UInt8.shiftLeft 1 index) != 0) = true := by
  have hn : UInt8.land (UInt8.lor value (UInt8.shiftLeft 1 index)) (UInt8.shiftLeft 1 index) ≠ 0 := by
    intro hz
    have hb := congrArg (fun v : UInt8 => v.toBitVec.getLsbD index.toNat) hz
    have hi : index.toNat < 8 := h
    simp [UInt8.land, UInt8.lor, UInt8.shiftLeft, UInt8.mod,
      BitVec.shiftLeft_eq', Nat.mod_eq_of_lt hi] at hb
    exact Nat.not_le_of_lt hi (hb (.inr hi))
  simpa using hn

private theorem bit_set_false (value index : UInt8) (_h : index < 8) :
    (UInt8.land (UInt8.land value (UInt8.shiftLeft 1 index).complement) (UInt8.shiftLeft 1 index) != 0) = false := by
  have hz : UInt8.land (UInt8.land value (UInt8.shiftLeft 1 index).complement) (UInt8.shiftLeft 1 index) = 0 := by
    apply UInt8.eq_of_toBitVec_eq
    ext i
    simp [UInt8.land, UInt8.complement, Bool.and_assoc]
  simp [hz]

private theorem bit_preserved_true (value index other : UInt8)
    (hi : index < 8) (ho : other < 8) (hne : index ≠ other) :
    UInt8.land (UInt8.lor value (UInt8.shiftLeft 1 index)) (UInt8.shiftLeft 1 other) =
      UInt8.land value (UInt8.shiftLeft 1 other) := by
  apply UInt8.eq_of_toBitVec_eq
  ext i
  have hin : index.toNat < 8 := hi
  have hon : other.toNat < 8 := ho
  have hnen : index.toNat ≠ other.toNat := fun heq => hne (UInt8.toNat_inj.mp heq)
  simp [UInt8.land, UInt8.lor, UInt8.shiftLeft, UInt8.mod, BitVec.shiftLeft_eq',
    Nat.mod_eq_of_lt hin, Nat.mod_eq_of_lt hon]
  by_cases hei : i = index.toNat <;> by_cases heo : i = other.toNat
  all_goals grind

private theorem bit_preserved_false (value index other : UInt8)
    (hi : index < 8) (ho : other < 8) (hne : index ≠ other) :
    UInt8.land (UInt8.land value (UInt8.shiftLeft 1 index).complement) (UInt8.shiftLeft 1 other) =
      UInt8.land value (UInt8.shiftLeft 1 other) := by
  apply UInt8.eq_of_toBitVec_eq
  ext i
  have hin : index.toNat < 8 := hi
  have hon : other.toNat < 8 := ho
  have hnen : index.toNat ≠ other.toNat := fun heq => hne (UInt8.toNat_inj.mp heq)
  simp [UInt8.land, UInt8.complement, UInt8.shiftLeft, UInt8.mod, BitVec.shiftLeft_eq',
    Nat.mod_eq_of_lt hin, Nat.mod_eq_of_lt hon]
  by_cases hei : i = index.toNat <;> by_cases heo : i = other.toNat
  all_goals grind

private theorem bit_update_idempotent (value mask : UInt8) :
    UInt8.lor (UInt8.lor value mask) mask = UInt8.lor value mask ∧
    UInt8.land (UInt8.land value mask.complement) mask.complement = UInt8.land value mask.complement := by
  constructor <;> apply UInt8.eq_of_toBitVec_eq <;> ext i <;>
    simp [UInt8.land, UInt8.lor, UInt8.complement]

private theorem bit_update_overwrite (value mask : UInt8) :
    UInt8.land (UInt8.lor value mask) mask.complement = UInt8.land value mask.complement ∧
    UInt8.lor (UInt8.land value mask.complement) mask = UInt8.lor value mask := by
  constructor <;> apply UInt8.eq_of_toBitVec_eq <;> ext i <;>
    simp [UInt8.land, UInt8.lor, UInt8.complement]
  all_goals cases mask.toBitVec[i] <;> simp

private theorem bitIndex_toUInt8_lt {index : Nat} (h : index < 8) :
    UInt8.ofNat index < 8 := by
  rw [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat_of_lt' (by change index < 256; omega)]
  exact h

/-- A bit reader observes the selected byte independently of all surrounding DB bytes. -/
theorem getBit_putUInt8_surrounded (pre suffix : ByteArray) (value : UInt8)
    (index : Nat) (h : index < 8) :
    getBit (pre ++ (putUInt8 value ++ suffix)) pre.size index =
      .ok (UInt8.land value (UInt8.shiftLeft 1 (UInt8.ofNat index)) != 0) := by
  have hr : getUInt8 (pre ++ (putUInt8 value ++ suffix)) pre.size = .ok value := by
    unfold getUInt8
    change ((Cursor.readUInt8 { data := pre ++ (bytes #[value] ++ suffix), offset := pre.size }).mapError
      Error.decode >>= (fun pair => pure pair.1)) = _
    rw [Cursor.readUInt8_append_byte]
    rfl
  simp only [getBit, Nat.not_le_of_lt h, ↓reduceIte, hr]
  rfl

/-- Updating a valid bit and reading that bit returns the requested Boolean. -/
theorem getBit_setBit_surrounded (pre suffix : ByteArray) (value : UInt8)
    (index : Nat) (enabled : Bool) (h : index < 8) :
    (setBit value index enabled >>= fun updated =>
      getBit (pre ++ (putUInt8 updated ++ suffix)) pre.size index) = .ok enabled := by
  cases enabled <;> simp only [setBit, Nat.not_le_of_lt h, ↓reduceIte]
  · change getBit (pre ++ (putUInt8 (UInt8.land value (UInt8.shiftLeft 1 (UInt8.ofNat index)).complement) ++ suffix))
      pre.size index = _
    rw [getBit_putUInt8_surrounded _ _ _ _ h, bit_set_false _ _ (bitIndex_toUInt8_lt h)]
  · change getBit (pre ++ (putUInt8 (UInt8.lor value (UInt8.shiftLeft 1 (UInt8.ofNat index))) ++ suffix))
      pre.size index = _
    rw [getBit_putUInt8_surrounded _ _ _ _ h, bit_set_true _ _ (bitIndex_toUInt8_lt h)]

/-- Changing one valid bit preserves every different valid bit, even in a surrounded DB byte. -/
theorem getBit_setBit_preserves_other_surrounded (pre suffix : ByteArray) (value : UInt8)
    (index other : Nat) (enabled : Bool) (hi : index < 8) (ho : other < 8)
    (hne : index ≠ other) :
    (setBit value index enabled >>= fun updated =>
      getBit (pre ++ (putUInt8 updated ++ suffix)) pre.size other) =
      getBit (pre ++ (putUInt8 value ++ suffix)) pre.size other := by
  have hne8 : UInt8.ofNat index ≠ UInt8.ofNat other := by
    intro heq
    have heqNat := congrArg UInt8.toNat heq
    rw [UInt8.toNat_ofNat_of_lt' (by change index < 256; omega),
      UInt8.toNat_ofNat_of_lt' (by change other < 256; omega)] at heqNat
    exact hne heqNat
  cases enabled <;> simp only [setBit, Nat.not_le_of_lt hi, ↓reduceIte]
  · change getBit (pre ++ (putUInt8 (UInt8.land value (UInt8.shiftLeft 1 (UInt8.ofNat index)).complement) ++ suffix))
      pre.size other = _
    rw [getBit_putUInt8_surrounded _ _ _ _ ho, getBit_putUInt8_surrounded _ _ _ _ ho,
      bit_preserved_false _ _ _ (bitIndex_toUInt8_lt hi) (bitIndex_toUInt8_lt ho) hne8]
  · change getBit (pre ++ (putUInt8 (UInt8.lor value (UInt8.shiftLeft 1 (UInt8.ofNat index))) ++ suffix))
      pre.size other = _
    rw [getBit_putUInt8_surrounded _ _ _ _ ho, getBit_putUInt8_surrounded _ _ _ _ ho,
      bit_preserved_true _ _ _ (bitIndex_toUInt8_lt hi) (bitIndex_toUInt8_lt ho) hne8]

/-- Reapplying the same valid bit update cannot change the byte again. -/
theorem setBit_idempotent (value : UInt8) (index : Nat) (enabled : Bool) (h : index < 8) :
    (setBit value index enabled >>= fun updated => setBit updated index enabled) =
      setBit value index enabled := by
  cases enabled <;> simp only [setBit, Nat.not_le_of_lt h, ↓reduceIte]
  · change Except.ok (UInt8.land (UInt8.land value (UInt8.shiftLeft 1 (UInt8.ofNat index)).complement)
      (UInt8.shiftLeft 1 (UInt8.ofNat index)).complement) = _
    rw [(bit_update_idempotent _ _).2]
    rfl
  · change Except.ok (UInt8.lor (UInt8.lor value (UInt8.shiftLeft 1 (UInt8.ofNat index)))
      (UInt8.shiftLeft 1 (UInt8.ofNat index))) = _
    rw [(bit_update_idempotent _ _).1]
    rfl

/-- The last Boolean written to a valid bit wins, independently of its prior update. -/
theorem setBit_overwrite (value : UInt8) (index : Nat) (first last : Bool) (h : index < 8) :
    (setBit value index first >>= fun updated => setBit updated index last) =
      setBit value index last := by
  cases first <;> cases last <;> simp only [setBit, Nat.not_le_of_lt h, ↓reduceIte]
  · change Except.ok (UInt8.land (UInt8.land value (UInt8.shiftLeft 1 (UInt8.ofNat index)).complement)
      (UInt8.shiftLeft 1 (UInt8.ofNat index)).complement) = _
    rw [(bit_update_idempotent _ _).2]
    rfl
  · change Except.ok (UInt8.lor (UInt8.land value (UInt8.shiftLeft 1 (UInt8.ofNat index)).complement)
      (UInt8.shiftLeft 1 (UInt8.ofNat index))) = _
    rw [(bit_update_overwrite _ _).2]
    rfl
  · change Except.ok (UInt8.land (UInt8.lor value (UInt8.shiftLeft 1 (UInt8.ofNat index)))
      (UInt8.shiftLeft 1 (UInt8.ofNat index)).complement) = _
    rw [(bit_update_overwrite _ _).1]
    rfl
  · change Except.ok (UInt8.lor (UInt8.lor value (UInt8.shiftLeft 1 (UInt8.ofNat index)))
      (UInt8.shiftLeft 1 (UInt8.ofNat index))) = _
    rw [(bit_update_idempotent _ _).1]
    rfl

/-- Every invalid Nat index is rejected before performing a bit update. -/
theorem setBit_invalid_index (value : UInt8) (index : Nat) (enabled : Bool) (h : 8 ≤ index) :
    setBit value index enabled = .error (.invalidBitIndex index) := by
  simp only [setBit, h, ↓reduceIte]
  rfl

/-- An invalid bit index is rejected even when the byte offset is itself out of bounds. -/
theorem getBit_invalid_index (data : ByteArray) (byteOffset index : Nat) (h : 8 ≤ index) :
    getBit data byteOffset index = .error (.invalidBitIndex index) := by
  simp only [getBit, h, ↓reduceIte]
  rfl

end LeanS7.Value
