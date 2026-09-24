import LeanS7.SessionConformance

namespace LeanS7.Conformance.Sessions

/-- The actual pure model consumes allowance or preserves it on any failure. -/
theorem failure_remaining_le (config : Config) (state : State) (kind : ClientErrorKind) :
    (failure config state kind).1.remaining ≤ state.remaining := by
  unfold failure
  split
  · rename_i remaining decision
    have decreased := retryBudgetAfter_decreases _ _ _ _ _ _ decision
    simp only
    omega
  · exact Nat.le_refl _

/-- A failure event never itself sends a packet. -/
theorem failure_sends (config : Config) (state : State) (kind : ClientErrorKind) :
    (failure config state kind).1.sends = state.sends := by
  unfold failure
  split <;> rfl

/-- Failure during reconnect does not create, complete, or reclassify a write
    attempt. This is equality of the actual stored progress, not only a count. -/
theorem failure_reconnect_progress (config : Config) (state : State) (kind : ClientErrorKind)
    (hphase : state.phase ≠ .awaiting) :
    (failure config state kind).1.progress = state.progress := by
  unfold failure
  split <;> simp [hphase, beq_iff_eq]

theorem failure_closed (config : Config) (state : State) (kind : ClientErrorKind)
    (hclosed : state.lifecycle = .closed) :
    (failure config state kind).1.lifecycle = .closed := by
  have hbeq : (Lifecycle.State.closed == Lifecycle.State.closed) = true := rfl
  simp [failure, hclosed, hbeq, retryBudgetAfter_closed]

/-- An already active logical request cannot replenish its allowance through
    any event in the actual transition function. -/
theorem step_active_remaining_le (config : Config) (state : State) (event : Event)
    (hactive : state.active.isSome = true) :
    (step config state event).1.remaining ≤ state.remaining := by
  cases event with
  | begin => simp [step, hactive]; split <;> exact Nat.le_refl _
  | send =>
    cases hp : sentProgress config state <;> simp [step, hp] <;> split <;> exact Nat.le_refl _
  | reconnectSetup => simp [step]; split <;> exact Nat.le_refl _
  | reconnected => simp [step]; split <;> exact Nat.le_refl _
  | disconnect => simp [step]
  | failure kind =>
    simp only [step, Id.run, pure]
    split
    · exact Nat.le_refl _
    · exact failure_remaining_le _ _ _
  | response packet =>
    cases hd : decodeResults config packet with
    | error error =>
      simp only [step, Id.run, pure]
      split
      · exact Nat.le_refl _
      · simp only [hd]
        exact failure_remaining_le _ _ _
    | ok results =>
      cases hp : acknowledgedProgress config state results <;> simp [step, hd, hp] <;>
        split <;> exact Nat.le_refl _

/-- No event can resurrect even an inconsistent, manually constructed closed
    model state. This property is about the actual `step`, not a side relation. -/
theorem step_closed (config : Config) (state : State) (event : Event)
    (hclosed : state.lifecycle = .closed) :
    (step config state event).1.lifecycle = .closed := by
  have hconnected : (Lifecycle.State.closed != Lifecycle.State.connected) = true := rfl
  have hdisconnected : (Lifecycle.State.closed != Lifecycle.State.disconnected) = true := rfl
  cases event with
  | begin => simp [step, hclosed, hconnected]
  | send => simp [step, hclosed, hconnected]
  | response packet => simp [step, hclosed, hconnected]
  | reconnectSetup => simp [step]; split <;> exact hclosed
  | reconnected => simp [step, hclosed, hdisconnected]
  | disconnect => rfl
  | failure kind =>
    simp only [step, Id.run, pure]
    split
    · exact hclosed
    · exact failure_closed _ _ _ hclosed

/-- Actual reconnect failures neither send nor alter write progress. Already
    classified replay uncertainty remains exactly as it was before reconnect. -/
theorem step_reconnect_failure_no_attempt (config : Config) (state : State)
    (kind : ClientErrorKind)
    (hphase : state.phase = .reconnectCotp ∨ state.phase = .reconnectSetup) :
    (step config state (.failure kind)).1.sends = state.sends ∧
    (step config state (.failure kind)).1.progress = state.progress := by
  have hnot : state.phase ≠ .awaiting := by rcases hphase with h | h <;> simp [h]
  simp only [step, Id.run, pure]
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨failure_sends _ _ _, failure_reconnect_progress _ _ _ hnot⟩

/-- A history records successive *actual* model transitions while the logical
    request is active before each event. Completion may be its final event. -/
inductive ActiveHistory (config : Config) : State → State → Prop where
  | nil (state : State) : ActiveHistory config state state
  | next {before after final : State} {event : Event}
      (active : before.active.isSome = true)
      (transition : (step config before event).1 = after)
      (rest : ActiveHistory config after final) : ActiveHistory config before final

theorem ActiveHistory.remaining_le {config : Config} {before after : State}
    (history : ActiveHistory config before after) : after.remaining ≤ before.remaining := by
  induction history with
  | nil state => exact Nat.le_refl _
  | @next before after final event active transition rest ih =>
    have bounded := step_active_remaining_le config before event active
    rw [transition] at bounded
    exact Nat.le_trans ih bounded

end LeanS7.Conformance.Sessions
