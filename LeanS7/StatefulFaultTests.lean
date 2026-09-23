import LeanS7.Upload
import LeanS7.Download
import LeanS7.UserDataAssembly

namespace LeanS7.StatefulFaultTests

private def ensure (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError label

private def bytes (n : Nat) : ByteArray :=
  ByteArray.mk ((Array.range n).map fun i => UInt8.ofNat (i + 1))

private def traces (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => (traces alphabet n).flatMap fun tail => alphabet.map (· :: tail)

/-- Independent arithmetic oracle, checked against the production accumulator at
    every accepted prefix, not just the final result of a mutated packet. -/
private def userTrace (trace : List (Nat × Bool)) : IO Unit := do
  let mut state := UserDataAssembly.empty 5 3
  let mut expected := ByteArray.empty
  let mut count := 0
  let mut complete := false
  for (size, more) in trace do
    let valid := !complete && count < 3 && expected.size + size ≤ 5 &&
      (!more || count + 1 < 3)
    match UserDataAssembly.accept state (bytes size) more with
    | .error _ =>
        ensure (!valid) "USER_DATA sequence rejected an oracle-valid prefix"
        return
    | .ok step =>
        ensure valid "USER_DATA sequence accepted an oracle-invalid prefix"
        expected := expected ++ bytes size
        count := count + 1
        complete := !more
        state := step.after
        ensure (state.data == expected && state.count == count && state.complete == complete)
          "USER_DATA sequence changed accumulated order/count/completion"

private def uploadTrace (trace : List (Option (Nat × Bool))) : IO Unit := do
  let .ok initial := Upload.start 5 (some 4)
    | throw <| IO.userError "upload seed rejected"
  let mut state := initial
  let mut expected := ByteArray.empty
  -- 0 receiving, 1 awaiting END_UPLOAD, 2 complete.
  let mut phase := 0
  for event in trace do
    match event with
    | none =>
        let valid := phase == 1 && expected.size == 4
        match Upload.finish state with
        | .error _ =>
            ensure (!valid) "upload sequence rejected valid completion"
            return
        | .ok after =>
            ensure valid "upload sequence accepted premature/repeated completion"
            phase := 2
            state := after
    | some (size, last) =>
        let nextSize := expected.size + size
        let valid := phase == 0 && nextSize ≤ 4 &&
          (if last then nextSize == 4 else size > 0 && nextSize < 4)
        match Upload.accept state { data := bytes size, isLast := last } with
        | .error _ =>
            ensure (!valid) "upload sequence rejected an oracle-valid fragment"
            return
        | .ok step =>
            ensure valid "upload sequence accepted an oracle-invalid fragment"
            expected := expected ++ bytes size
            phase := if last then 1 else 0
            state := step.after
    ensure (state.assembly.data == expected && state.phase ==
      (if phase == 0 then .receiving else if phase == 1 then .awaitingEnd else .complete))
      "upload sequence changed bytes/phase"

private def downloadTrace (trace : List Nat) : IO Unit := do
  let payload := bytes 5
  let mut state := Download.start payload
  let mut offset := 0
  let mut phase := 0
  let mut sent := ByteArray.empty
  for event in trace do
    if event == 0 then
      match Download.acknowledge state with
      | none =>
          ensure (phase != 0) "download rejected initial acknowledgement"
          return
      | some after =>
          ensure (phase == 0) "download accepted duplicate acknowledgement"
          phase := 1
          state := after
    else if event == 3 then
      match Download.finish payload state with
      | none =>
          ensure (phase != 2 || offset != 5) "download rejected valid completion"
          return
      | some after =>
          ensure (phase == 2 && offset == 5) "download accepted premature/repeated completion"
          phase := 3
          state := after
    else
      let maximum := if event == 1 then 2 else 0
      let valid := phase == 1 && maximum > 0 && offset < 5
      match Download.nextFragment payload state maximum with
      | none =>
          ensure (!valid) "download rejected an oracle-valid fragment"
          return
      | some fragment =>
          ensure valid "download accepted an oracle-invalid fragment"
          offset := min 5 (offset + maximum)
          sent := sent ++ fragment.chunk
          phase := if offset == 5 then 2 else 1
          state := fragment.after
    ensure (state.offset == offset && sent == payload.extract 0 offset &&
      state.phase == (if phase == 0 then .awaitingAck else if phase == 1 then
        .awaitingFragment else if phase == 2 then .awaitingEnd else .complete))
      "download sequence changed exact sent prefix/phase"

def run : IO Unit := do
  let userAlphabet := [0, 1, 2, 5, 6].flatMap fun n => [(n, false), (n, true)]
  let uploadAlphabet := none :: ([0, 1, 2, 4, 5].flatMap fun n =>
    [some (n, false), some (n, true)])
  let mut count := 0
  for depth in [1:5] do
    for trace in traces userAlphabet depth do
      userTrace trace
      count := count + 1
    for trace in traces uploadAlphabet depth do
      uploadTrace trace
      count := count + 1
  -- Six events include a full three-fragment download and its final acknowledgement.
  for trace in traces [0, 1, 2, 3] 6 do
    downloadTrace trace
    count := count + 1
  IO.println s!"stateful fault sequence tests passed: {count} conversations"

end LeanS7.StatefulFaultTests
