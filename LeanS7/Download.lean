import LeanS7.Advanced

namespace LeanS7.Download

/-- The client may send a block fragment only after the PLC acknowledges the
    download request, and may finish only after the complete block was sent. -/
inductive Phase where
  | awaitingAck
  | awaitingFragment
  | awaitingEnd
  | complete
  deriving Repr, BEq, DecidableEq

/-- `offset` is the length of the exact prefix already sent to the PLC. -/
structure State (payload : ByteArray) where
  phase : Phase
  offset : Nat
  offset_le : offset ≤ payload.size

def start (payload : ByteArray) : State payload :=
  { phase := .awaitingAck, offset := 0, offset_le := Nat.zero_le _ }

def acknowledge (state : State payload) : Option (State payload) :=
  match state.phase with
  | .awaitingAck => some { state with phase := .awaitingFragment }
  | _ => none

theorem acknowledge_transition (payload : ByteArray) (state after : State payload)
    (hack : acknowledge state = some after) :
    state.phase = .awaitingAck ∧ after.phase = .awaitingFragment ∧
      after.offset = state.offset := by
  cases hphase : state.phase <;> simp [acknowledge, hphase] at hack
  cases hack
  exact ⟨rfl, rfl, rfl⟩

/-- A fragment carries the next contiguous slice of the original block. -/
structure Fragment (payload : ByteArray) (before : State payload) (maximum : Nat) where
  chunk : ByteArray
  after : State payload
  chunk_eq : chunk = payload.extract before.offset after.offset
  after_eq : after.offset = min payload.size (before.offset + maximum)
  phase_eq : after.phase = if after.offset == payload.size then .awaitingEnd else .awaitingFragment
  progress : before.offset < after.offset
  bounded : chunk.size ≤ maximum

def nextFragment (payload : ByteArray) (state : State payload) (maximum : Nat) :
    Option (Fragment payload state maximum) :=
  if hphase : state.phase = .awaitingFragment then
    if hmax : 0 < maximum then
      if hremaining : state.offset < payload.size then
        let nextOffset := min payload.size (state.offset + maximum)
        let chunk := payload.extract state.offset nextOffset
        let after : State payload := {
          phase := if nextOffset == payload.size then .awaitingEnd else .awaitingFragment
          offset := nextOffset
          offset_le := Nat.min_le_left _ _
        }
        some {
          chunk
          after
          chunk_eq := rfl
          after_eq := rfl
          phase_eq := rfl
          progress := by dsimp [after, nextOffset]; omega
          bounded := by simp [chunk, ByteArray.size_extract]; omega
        }
      else none
    else none
  else none

def finish (payload : ByteArray) (state : State payload) : Option (State payload) :=
  if state.phase == .awaitingEnd && state.offset == payload.size then
    some { state with phase := .complete }
  else none

/-- Each accepted request extends the sent prefix in order, with no gaps or overlap. -/
theorem fragment_prefix (payload : ByteArray) (state : State payload)
    (maximum : Nat) (fragment : Fragment payload state maximum) :
    payload.extract 0 fragment.after.offset =
      payload.extract 0 state.offset ++ fragment.chunk := by
  rw [fragment.chunk_eq]
  exact ByteArray.extract_eq_extract_append_extract state.offset
    (Nat.zero_le _) (Nat.le_of_lt fragment.progress)

/-- A final fragment is exactly the one that reaches the end of the block. -/
theorem fragment_last_iff_complete (payload : ByteArray) (state : State payload)
    (maximum : Nat) (fragment : Fragment payload state maximum) :
    fragment.after.phase = .awaitingEnd ↔ fragment.after.offset = payload.size := by
  rw [fragment.phase_eq]
  by_cases h : fragment.after.offset = payload.size <;> simp [h]

/-- The exact encoded response for a planned fragment fits the negotiated S7
    PDU when `maximum` is the PDU budget minus the 18-byte response overhead. -/
theorem encoded_fragment_fits (payload : ByteArray) (state : State payload)
    (maximum : Nat) (fragment : Fragment payload state maximum)
    (reference : UInt16) (isLast : Bool) (packet : ByteArray)
    (hencode : S7.encodeDownloadFragmentResponse reference isLast fragment.chunk = .ok packet) :
    packet.size ≤ maximum + 18 := by
  have hsize := S7.encodedDownloadFragmentResponse_size reference isLast
    fragment.chunk packet hencode
  have hbound := fragment.bounded
  simp only [S7.responseHeaderSize] at hsize
  omega

/-- The state machine cannot yield block bytes before the initial acknowledgement. -/
theorem no_fragment_before_ack (payload : ByteArray) (maximum : Nat) :
    nextFragment payload (start payload) maximum = none := by
  simp [nextFragment, start]

theorem no_finish_before_ack (payload : ByteArray) :
    finish payload (start payload) = none := by
  rfl

theorem no_finish_before_complete (payload : ByteArray) (state : State payload)
    (hincomplete : state.offset < payload.size) :
    finish payload state = none := by
  simp [finish, Nat.ne_of_lt hincomplete]

/-- A successful final transition means the entire original block was sent. -/
theorem finish_complete (payload : ByteArray) (state after : State payload)
    (hfinish : finish payload state = some after) :
    state.offset = payload.size ∧ after.phase = .complete := by
  unfold finish at hfinish
  split at hfinish
  · rename_i hcondition
    simp at hcondition
    obtain ⟨_, hsize⟩ := hcondition
    cases hfinish
    exact ⟨hsize, rfl⟩
  · contradiction

end LeanS7.Download
