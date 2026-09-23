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

end LeanS7
