import LeanS7.ClientError

namespace LeanS7

/-- Replay safety belongs to the operation, not to the transport error.
    Unknown/raw requests are conservatively treated as potentially mutating. -/
inductive RetrySafety where
  | readOnly
  | potentiallyMutating
  deriving BEq, Repr

def retryPermitted (safety : RetrySafety) (allowPotentiallyMutating : Bool) : Bool :=
  safety == .readOnly || allowPotentiallyMutating

theorem unknown_not_replayed : retryPermitted .potentiallyMutating false = false := rfl
theorem read_replay_permitted : retryPermitted .readOnly false = true := rfl

/-- One retry decision, shared by both live exchange paths and the portable
    primitive model. A successful decision consumes exactly one allowance.
    It does not assert that a reconnect or resend completes. -/
def retryBudgetAfter (remaining : Nat) (closed : Bool) (kind : ClientErrorKind)
    (safety : RetrySafety) (allowPotentiallyMutating : Bool) : Option Nat :=
  if closed || remaining == 0 || !isRetryableClientErrorKind kind ||
      !retryPermitted safety allowPotentiallyMutating then none
  else some (remaining - 1)

theorem retryBudgetAfter_closed (remaining : Nat) (kind : ClientErrorKind)
    (safety : RetrySafety) (allow : Bool) :
    retryBudgetAfter remaining true kind safety allow = none := by
  simp [retryBudgetAfter]

theorem retryBudgetAfter_zero (closed : Bool) (kind : ClientErrorKind)
    (safety : RetrySafety) (allow : Bool) :
    retryBudgetAfter 0 closed kind safety allow = none := by
  simp [retryBudgetAfter]

theorem retryBudgetAfter_nonretryable (remaining : Nat) (closed : Bool)
    (kind : ClientErrorKind) (safety : RetrySafety) (allow : Bool)
    (h : isRetryableClientErrorKind kind = false) :
    retryBudgetAfter remaining closed kind safety allow = none := by
  simp [retryBudgetAfter, h]

theorem retryBudgetAfter_mutating_default (remaining : Nat) (closed : Bool)
    (kind : ClientErrorKind) :
    retryBudgetAfter remaining closed kind .potentiallyMutating false = none := by
  have hpolicy : retryPermitted .potentiallyMutating false = false := rfl
  simp [retryBudgetAfter, hpolicy]

theorem retryBudgetAfter_invariants (remaining next : Nat) (closed : Bool)
    (kind : ClientErrorKind) (safety : RetrySafety) (allow : Bool)
    (h : retryBudgetAfter remaining closed kind safety allow = some next) :
    closed = false ∧ 0 < remaining ∧ isRetryableClientErrorKind kind = true ∧
      retryPermitted safety allow = true ∧ next + 1 = remaining := by
  unfold retryBudgetAfter at h
  split at h
  · contradiction
  · rename_i hguard
    simp only [Bool.or_eq_true, beq_iff_eq] at hguard
    have hclosed : closed = false := by cases closed <;> simp_all
    have hpositive : 0 < remaining := by
      have hn : remaining ≠ 0 := by
        intro hz
        simp [hz] at hguard
      omega
    have hkind : isRetryableClientErrorKind kind = true := by
      cases hk : isRetryableClientErrorKind kind <;> simp_all
    have hsafety : retryPermitted safety allow = true := by
      cases hs : retryPermitted safety allow <;> simp_all
    cases h
    exact ⟨hclosed, hpositive, hkind, hsafety, by omega⟩

theorem retryBudgetAfter_decreases (remaining next : Nat) (closed : Bool)
    (kind : ClientErrorKind) (safety : RetrySafety) (allow : Bool)
    (h : retryBudgetAfter remaining closed kind safety allow = some next) :
    next < remaining := by
  have bounds := retryBudgetAfter_invariants remaining next closed kind safety allow h
  omega

theorem retryBudgetAfter_eligible (remaining : Nat) (closed : Bool)
    (kind : ClientErrorKind) (safety : RetrySafety) (allow : Bool) :
    (retryBudgetAfter remaining closed kind safety allow).isSome =
      (!closed && remaining > 0 && isRetryableClientErrorKind kind && retryPermitted safety allow) := by
  unfold retryBudgetAfter
  cases closed <;> cases hs : retryPermitted safety allow <;>
    cases hk : isRetryableClientErrorKind kind <;>
    by_cases hzero : remaining = 0 <;>
    simp_all [Nat.pos_iff_ne_zero]

/-- A chain records actual successful budget decisions with arbitrary contexts
    at each step. It intentionally says nothing about native IO termination. -/
inductive RetryBudgetChain : Nat → Nat → Nat → Prop where
  | nil (remaining : Nat) : RetryBudgetChain remaining 0 remaining
  | step {remaining next count final : Nat} {closed : Bool}
      {kind : ClientErrorKind} {safety : RetrySafety} {allow : Bool}
      (decision : retryBudgetAfter remaining closed kind safety allow = some next)
      (rest : RetryBudgetChain next count final) :
      RetryBudgetChain remaining (count + 1) final

theorem RetryBudgetChain.accounting {initial count final : Nat}
    (chain : RetryBudgetChain initial count final) : count + final = initial := by
  induction chain with
  | nil remaining => omega
  | step decision rest ih =>
    have bounds := retryBudgetAfter_invariants _ _ _ _ _ _ decision
    omega

theorem RetryBudgetChain.bounded {initial count final : Nat}
    (chain : RetryBudgetChain initial count final) : count ≤ initial := by
  have accounting := chain.accounting
  omega

end LeanS7
