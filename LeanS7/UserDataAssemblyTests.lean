import LeanS7.UserDataAssembly

open LeanS7

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def getStep (result : Except DecodeError α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw <| IO.userError s!"{repr error}"

private def rejected (result : Except ε α) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

/-- Small bounds exercise the exact production accumulator without large fixtures. -/
def testUserDataAssembly : IO Unit := do
  let empty := UserDataAssembly.empty 5 3
  let first ← getStep <| UserDataAssembly.accept empty (ByteArray.mk #[1, 2]) true
  let metadata ← getStep <| UserDataAssembly.accept first.after ByteArray.empty true
  let final ← getStep <| UserDataAssembly.accept metadata.after (ByteArray.mk #[3, 4, 5]) false
  ensure (final.after.data == ByteArray.mk #[1, 2, 3, 4, 5] &&
    final.after.count == 3 && final.after.complete) "USER_DATA exact bounds/order failed"
  ensure (rejected <| UserDataAssembly.accept final.after ByteArray.empty false)
    "USER_DATA accepted a fragment after completion"
  ensure (rejected <| UserDataAssembly.accept metadata.after ByteArray.empty true)
    "USER_DATA accepted continuation at the fragment cap"
  ensure (rejected <| UserDataAssembly.accept metadata.after (ByteArray.mk #[3, 4, 5, 6]) false)
    "USER_DATA accepted cumulative byte overflow"
  ensure (rejected <| UserDataAssembly.accept (UserDataAssembly.empty 0 0) ByteArray.empty false)
    "USER_DATA accepted a fragment with zero available slots"
  let zero ← getStep <| UserDataAssembly.accept (UserDataAssembly.empty 0 1) ByteArray.empty false
  ensure (zero.after.complete && zero.after.data.isEmpty)
    "USER_DATA rejected empty final payload"
  let only ← getStep <| UserDataAssembly.accept (UserDataAssembly.empty 5 1)
    (ByteArray.mk #[1, 2, 3, 4, 5]) false
  ensure (only.after.data.size == 5) "USER_DATA rejected one-fragment exact bound"
