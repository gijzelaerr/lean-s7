import LeanS7.Binary

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

/-- The read loop carries the exact number of assembled elements in its type. -/
structure ReadAssembly (elementSize consumed : Nat) where
  data : ByteArray
  size_eq : data.size = consumed * elementSize

namespace ReadAssembly

def empty (elementSize : Nat) : ReadAssembly elementSize 0 :=
  ⟨ByteArray.empty, by simp⟩

def nextStart (state : ReadAssembly elementSize consumed) (start : Nat) : Nat :=
  start + state.data.size

/-- The next request begins immediately after the assembled prefix. -/
theorem nextStart_eq (state : ReadAssembly elementSize consumed) (start : Nat) :
    state.nextStart start = start + consumed * elementSize := by
  simp [nextStart, state.size_eq]

def append (state : ReadAssembly elementSize consumed)
    (chunk : { data : ByteArray // data.size = count * elementSize }) :
    ReadAssembly elementSize (consumed + count) :=
  ⟨state.data ++ chunk.val, by simp [state.size_eq, chunk.property, Nat.add_mul]⟩

/-- Assembly retains the previous bytes followed by the new response, in order. -/
theorem append_data (state : ReadAssembly elementSize consumed)
    (chunk : { data : ByteArray // data.size = count * elementSize }) :
    (state.append chunk).data = state.data ++ chunk.val := rfl

theorem append_nextStart (state : ReadAssembly elementSize consumed)
    (chunk : { data : ByteArray // data.size = count * elementSize }) (start : Nat) :
    (state.append chunk).nextStart start = state.nextStart start + count * elementSize := by
  simp [nextStart, append, chunk.property, Nat.add_assoc]

/-- Completing the generated plan yields exactly the requested byte count. -/
theorem complete_size (total maximum elementSize : Nat) (hmaximum : maximum ≠ 0)
    (state : ReadAssembly elementSize (0 + (counts total maximum).sum)) :
    state.data.size = total * elementSize := by
  simpa [counts_sum total maximum hmaximum] using state.size_eq

end ReadAssembly

/-- A bounded write slice cannot silently truncate at the end of the payload. -/
def writeSlice (payload : ByteArray) (offset count elementSize : Nat)
    (hbound : offset + count * elementSize ≤ payload.size) :
    { data : ByteArray // data.size = count * elementSize } :=
  ⟨payload.extract offset (offset + count * elementSize), by
    simp only [ByteArray.size_extract, Nat.min_eq_left hbound]
    omega⟩

/-- The bytes presented to sequential write requests, in request order. -/
def writeSlices (payload : ByteArray) (elementSize offset : Nat) : List Nat → ByteArray
  | [] => ByteArray.empty
  | count :: rest => payload.extract offset (offset + count * elementSize) ++
      writeSlices payload elementSize (offset + count * elementSize) rest

theorem writeSlices_eq_extract (payload : ByteArray) (elementSize offset : Nat)
    (chunks : List Nat) :
    writeSlices payload elementSize offset chunks =
      payload.extract offset (offset + chunks.sum * elementSize) := by
  induction chunks generalizing offset with
  | nil => simp [writeSlices]
  | cons count rest ih =>
      rw [writeSlices, ih]
      rw [ByteArray.extract_append_extract]
      simp [Nat.add_mul, Nat.add_assoc]

/-- An aligned payload is exactly reconstructed by its generated write slices. -/
theorem writeSlices_complete (payload : ByteArray) (elementSize maximum : Nat)
    (haligned : payload.size % elementSize = 0) (hmaximum : maximum ≠ 0) :
    writeSlices payload elementSize 0 (counts (payload.size / elementSize) maximum) =
      payload := by
  rw [writeSlices_eq_extract, counts_sum _ _ hmaximum]
  have hsize : payload.size / elementSize * elementSize = payload.size := by
    have := Nat.div_add_mod payload.size elementSize
    simpa [haligned, Nat.mul_comm] using this
  simp [hsize]

end LeanS7.Chunking
