namespace LeanS7.Lifecycle

inductive State where
  | connected
  | disconnected
  | closed
  deriving Repr, BEq, DecidableEq

inductive Event where
  | transportClosed
  | reconnected
  | disconnect
  deriving Repr, BEq, DecidableEq

/-- The complete legal client lifecycle transition relation. -/
def transition : State → Event → Option State
  | .connected, .transportClosed => some .disconnected
  | .disconnected, .transportClosed => some .disconnected
  | .closed, .transportClosed => some .closed
  | .disconnected, .reconnected => some .connected
  | .connected, .disconnect => some .closed
  | .disconnected, .disconnect => some .closed
  | .closed, .disconnect => some .closed
  | _, _ => none

/-- Explicit disconnect is total and always reaches the terminal state. -/
theorem transition_disconnect (state : State) :
    transition state .disconnect = some .closed := by
  cases state <;> rfl

/-- No accepted event can move a closed client back to a live state. -/
theorem closed_is_terminal (event : Event) (next : State)
    (htransition : transition .closed event = some next) :
    next = .closed := by
  cases event <;> simp [transition] at htransition
  · exact htransition.symm
  · exact htransition.symm

/-- A successful reconnect is legal only from the disconnected state and its
    result is connected. -/
theorem reconnect_transition (state next : State)
    (htransition : transition state .reconnected = some next) :
    state = .disconnected ∧ next = .connected := by
  cases state <;> simp [transition] at htransition
  exact ⟨rfl, htransition.symm⟩

/-- Closing a transport can never create a connected client. -/
theorem transportClosed_not_connected (state next : State)
    (htransition : transition state .transportClosed = some next) :
    next ≠ .connected := by
  cases state <;> simp [transition] at htransition
  all_goals subst next <;> decide

end LeanS7.Lifecycle
