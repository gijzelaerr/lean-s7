import LeanS7

open LeanS7

private def checkRejected (name : String) (result : Except DecodeError α) : IO Unit :=
  match result with
  | .error error => IO.println s!"{name}: rejected ({repr error})"
  | .ok _ => throw <| IO.userError s!"{name}: unexpectedly accepted"

def main : IO Unit := do
  let shortRead : S7.Response := {
    pduType := 3, reference := 1,
    parameters := bytes #[4, 1], data := bytes #[255, 4, 0, 32, 170],
    errorClass := 0, errorCode := 0
  }
  checkRejected "short read" (S7.decodeAreaRead 1 .dataBlocks 4 shortRead)
  let wrongFunction := { shortRead with data := bytes #[255, 4, 0, 8, 170] }
  checkRejected "write answered by read" (S7.decodeDbWrite 1 wrongFunction)
  let chunks := Chunking.counts 500 ((480 - 18) / 2)
  unless chunks == [231, 231, 38] do
    throw <| IO.userError "unexpected two-byte element chunk plan"
  IO.println s!"two-byte element counts: {chunks}; byte starts: [0, 462, 924]"
