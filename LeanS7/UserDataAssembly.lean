import LeanS7.Binary

namespace LeanS7.UserDataAssembly

/-- Byte and fragment bounds are checked before allocating accumulated payloads.
    Empty fragments are legal: metadata-only continuations still consume a slot. -/
structure State (maximum fragments : Nat) where
  data : ByteArray
  count : Nat
  complete : Bool
  bounded : data.size ≤ maximum
  countBounded : count ≤ fragments

def empty (maximum fragments : Nat) : State maximum fragments :=
  ⟨ByteArray.empty, 0, false, Nat.zero_le _, Nat.zero_le _⟩

structure Step (before : State maximum fragments) (chunk : ByteArray) (more : Bool) where
  after : State maximum fragments
  order : after.data = before.data ++ chunk
  count : after.count = before.count + 1
  completion : after.complete = !more
  continuationRoom : more = true → after.count < fragments

def accept (state : State maximum fragments) (chunk : ByteArray) (more : Bool) :
    Except DecodeError (Step state chunk more) :=
  if state.complete then
    .error (.invalidField 0 "USER_DATA fragment received after completion")
  else if hcount : state.count + 1 ≤ fragments then
    if hlast : more = true ∧ state.count + 1 = fragments then
      .error (.invalidField 0 s!"USER_DATA response exceeded the {fragments}-fragment safety limit")
    else if hsize : state.data.size + chunk.size ≤ maximum then
      .ok {
        after := ⟨state.data ++ chunk, state.count + 1, !more, by simpa using hsize, hcount⟩
        order := rfl
        count := rfl
        completion := rfl
        continuationRoom := by
          intro hmore
          have hne : state.count + 1 ≠ fragments := fun heq => hlast ⟨hmore, heq⟩
          change state.count + 1 < fragments
          omega
      }
    else .error (.invalidField 0 s!"USER_DATA response exceeded the {maximum}-byte safety limit")
  else .error (.invalidField 0 s!"USER_DATA response exceeded the {fragments}-fragment safety limit")

theorem accepted_order (step : Step state chunk more) :
    step.after.data = state.data ++ chunk := step.order

theorem accepted_size (step : Step state chunk more) :
    step.after.data.size = state.data.size + chunk.size := by rw [step.order]; simp

theorem accepted_bounds {state : State maximum fragments} (step : Step state chunk more) :
    step.after.data.size ≤ maximum ∧ step.after.count ≤ fragments :=
  ⟨step.after.bounded, step.after.countBounded⟩

theorem accepted_progress (step : Step state chunk more) :
    state.count < step.after.count := by rw [step.count]; omega

theorem rejects_byte_overflow (state : State maximum fragments) (chunk : ByteArray)
    (more : Bool) (hoverflow : maximum < state.data.size + chunk.size) :
    ∀ step, accept state chunk more ≠ .ok step := by
  intro step
  simp only [accept]
  split
  · simp
  · split
    · split
      · simp
      · simp [Nat.not_le.mpr hoverflow]
    · simp

theorem rejects_fragment_overflow (state : State maximum fragments) (chunk : ByteArray)
    (more : Bool) (hoverflow : fragments < state.count + 1) :
    ∀ step, accept state chunk more ≠ .ok step := by
  intro step
  simp only [accept]
  split
  · simp
  · simp [Nat.not_le.mpr hoverflow]

end LeanS7.UserDataAssembly
