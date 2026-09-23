import LeanS7.Advanced

namespace LeanS7.Upload

/-- A bounded accumulator. The size guard runs before allocating the append. -/
structure Assembly (maximum : Nat) where
  data : ByteArray
  bounded : data.size ≤ maximum

def Assembly.empty (maximum : Nat) : Assembly maximum :=
  ⟨ByteArray.empty, Nat.zero_le _⟩

def Assembly.append (state : Assembly maximum) (chunk : ByteArray) :
    Except DecodeError (Assembly maximum) :=
  if hbound : state.data.size + chunk.size ≤ maximum then
    .ok ⟨state.data ++ chunk, by simpa using hbound⟩
  else
    .error (.invalidField 0 s!"block upload exceeds its {maximum}-byte safety limit")

theorem Assembly.append_order (state after : Assembly maximum) (chunk : ByteArray)
    (happend : state.append chunk = .ok after) :
    after.data = state.data ++ chunk := by
  unfold append at happend
  split at happend
  · cases happend
    rfl
  · contradiction

theorem Assembly.append_size (state after : Assembly maximum) (chunk : ByteArray)
    (happend : state.append chunk = .ok after) :
    after.data.size = state.data.size + chunk.size := by
  rw [append_order state after chunk happend]
  simp

theorem Assembly.rejects_overflow (state : Assembly maximum) (chunk : ByteArray)
    (hoverflow : maximum < state.data.size + chunk.size) :
    state.append chunk = .error
      (.invalidField 0 s!"block upload exceeds its {maximum}-byte safety limit") := by
  simp [append, Nat.not_le.mpr hoverflow]

inductive Phase where
  | receiving
  | awaitingEnd
  | complete
  deriving Repr, BEq, DecidableEq

structure State (maximum : Nat) where
  phase : Phase
  expected : Option Nat
  assembly : Assembly maximum

def start (maximum : Nat) (expected : Option Nat) : Except DecodeError (State maximum) := do
  if let some size := expected then
    if size > maximum then
      throw (.invalidField 0 "declared upload length exceeds the safety limit")
  return { phase := .receiving, expected, assembly := Assembly.empty maximum }

/-- An accepted fragment retains the preceding bytes in their original order. -/
structure Step (state : State maximum) (fragment : S7.UploadFragment) where
  after : State maximum
  data_eq : after.assembly.data = state.assembly.data ++ fragment.data
  phase_eq : after.phase = if fragment.isLast then .awaitingEnd else .receiving
  progress : fragment.isLast = false → state.assembly.data.size < after.assembly.data.size

def accept (state : State maximum) (fragment : S7.UploadFragment) :
    Except DecodeError (Step state fragment) := do
  if state.phase != .receiving then
    throw (.invalidField 0 "upload fragment received after the final fragment")
  if hnoProgress : fragment.isLast = false ∧ fragment.data.size = 0 then
    throw (.invalidField 0 "upload continuation fragment made no progress")
  else
    let nextSize := state.assembly.data.size + fragment.data.size
    if let some expected := state.expected then
      if nextSize > expected then
        throw (.invalidField 0 "upload fragment exceeds the declared block length")
      if fragment.isLast && nextSize != expected then
        throw (.invalidField 0 "final upload fragment does not match the declared block length")
      if !fragment.isLast && nextSize == expected then
        throw (.invalidField 0 "upload continuation reached the declared block length")
    match happend : state.assembly.append fragment.data with
    | .error error => throw error
    | .ok assembly =>
        return {
          after := {
            assembly := assembly
            expected := state.expected
            phase := if fragment.isLast then .awaitingEnd else .receiving
          }
          data_eq := Assembly.append_order state.assembly assembly fragment.data happend
          phase_eq := rfl
          progress := by
            intro hmore
            have hnonempty : fragment.data.size ≠ 0 := fun hzero => hnoProgress ⟨hmore, hzero⟩
            change state.assembly.data.size < assembly.data.size
            rw [Assembly.append_size state.assembly assembly fragment.data happend]
            omega
        }

/-- Called only after a valid END_UPLOAD acknowledgement, before returning data. -/
def finish (state : State maximum) : Except DecodeError (State maximum) :=
  match state.phase with
  | .awaitingEnd =>
      if let some expected := state.expected then
        if state.assembly.data.size != expected then
          .error (.invalidField 0 "completed upload does not match the declared block length")
        else .ok { state with phase := .complete }
      else .ok { state with phase := .complete }
  | _ => .error (.invalidField 0 "upload cannot complete before the final fragment")

theorem finish_phase (state after : State maximum)
    (hfinish : finish state = .ok after) :
    state.phase = .awaitingEnd ∧ after.phase = .complete := by
  cases hphase : state.phase <;> simp [finish, hphase] at hfinish
  split at hfinish
  · split at hfinish <;> simp_all
    cases hfinish
    rfl
  · cases hfinish; exact ⟨rfl, rfl⟩

theorem finish_exact (state after : State maximum) (expected : Nat)
    (hexpected : state.expected = some expected)
    (hfinish : finish state = .ok after) :
    after.assembly.data.size = expected := by
  cases hphase : state.phase <;> simp [finish, hphase, hexpected] at hfinish
  split at hfinish <;> simp_all
  cases hfinish
  assumption

end LeanS7.Upload
