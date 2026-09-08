namespace LeanS7.Chunking

/-- Split an element count into full chunks followed by at most one remainder.
    A zero maximum has no valid plan. -/
def counts (total maximum : Nat) : List Nat :=
  if maximum = 0 then
    []
  else
    List.replicate (total / maximum) maximum ++
      if total % maximum = 0 then [] else [total % maximum]

/-- Every positive-capacity chunk plan covers the requested element count
    exactly. Sequential consumers therefore have neither gaps nor overlap. -/
theorem counts_sum (total maximum : Nat) (hmaximum : maximum ≠ 0) :
    (counts total maximum).sum = total := by
  rw [counts, if_neg hmaximum, List.sum_append]
  by_cases hremainder : total % maximum = 0
  · rw [if_pos hremainder]
    simpa [hremainder, Nat.mul_comm] using Nat.div_add_mod total maximum
  · rw [if_neg hremainder]
    simp
    simpa [Nat.mul_comm] using Nat.div_add_mod total maximum

/-- Every generated chunk is nonempty and no larger than the configured
    maximum. -/
theorem counts_bounds (total maximum chunk : Nat) (hmaximum : maximum ≠ 0)
    (hchunk : chunk ∈ counts total maximum) :
    0 < chunk ∧ chunk ≤ maximum := by
  rw [counts, if_neg hmaximum] at hchunk
  simp only [List.mem_append, List.mem_replicate] at hchunk
  rcases hchunk with hfull | hremainder
  · rcases hfull with ⟨_, hchunkEq⟩
    rw [hchunkEq]
    exact ⟨Nat.pos_of_ne_zero hmaximum, Nat.le_refl maximum⟩
  · by_cases hzero : total % maximum = 0
    · simp [hzero] at hremainder
    · simp [hzero] at hremainder
      subst chunk
      exact ⟨Nat.pos_of_ne_zero hzero,
        Nat.le_of_lt (Nat.mod_lt total (Nat.pos_of_ne_zero hmaximum))⟩

private theorem sum_map_mul (values : List Nat) (factor : Nat) :
    (values.map fun value => value * factor).sum = values.sum * factor := by
  induction values with
  | nil => simp
  | cons value rest ih => simp [ih, Nat.add_mul]

/-- Scaling chunks by an element width covers exactly the corresponding byte
    range, which is the invariant used by both read starts and write slices. -/
theorem counts_byte_sum (total maximum elementSize : Nat)
    (hmaximum : maximum ≠ 0) :
    ((counts total maximum).map fun count => count * elementSize).sum =
      total * elementSize := by
  rw [sum_map_mul, counts_sum total maximum hmaximum]

/-- The empty request has an empty chunk plan. -/
@[simp] theorem counts_zero (maximum : Nat) : counts 0 maximum = [] := by
  by_cases hmaximum : maximum = 0
  · simp [counts, hmaximum]
  · simp [counts, hmaximum]

end LeanS7.Chunking
