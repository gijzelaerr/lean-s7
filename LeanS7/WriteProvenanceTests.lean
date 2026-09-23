import LeanS7.Client

namespace LeanS7.WriteProvenanceTests

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def value (result : Except DecodeError α) : IO α :=
  match result with
  | .ok item => pure item
  | .error error => throw <| IO.userError (reprStr error)

private def rejected (result : Except ε α) : Bool :=
  match result with | .error _ => true | .ok _ => false

def run : IO Unit := do
  let range : S7.MemoryRange := { area := .dataBlocks, dbNumber := 1, start := 10, count := 1 }
  let first : WriteLocation := { range, itemIndex := some 0 }
  let duplicate : WriteLocation := { range, itemIndex := some 1, chunkByteOffset := 212 }
  let pending ← value <| ({} : WriteProgress.State).sent #[first, duplicate]
  ensure (rejected <| pending.sent #[first]) "write trace accepted overlapping sends"
  ensure (rejected <| ({} : WriteProgress.State).sent #[]) "write trace accepted empty send"
  ensure (rejected <| pending.acknowledge #[.success]) "write trace accepted missing result"
  ensure (rejected <| pending.acknowledge #[.success, .success, .success])
    "write trace accepted excess result"
  let knownState ← value <| pending.acknowledge #[.success, .failure 5]
  let known := knownState.snapshot
  ensure (known.attempts.map (·.location) == #[first, duplicate] &&
    known.attempts.map (·.outcome) == #[.itemResult .success, .itemResult (.failure 5)] &&
    known.acknowledged.map (·.itemIndex) == #[some 0, some 1] &&
    known.acknowledged.map (·.chunkByteOffset) == #[0, 212])
    "write trace lost duplicate caller identity/results"
  let replaying := pending.replay
  let resent ← value <| replaying.sent #[first, duplicate]
  let failed := resent.globalReject.snapshot
  ensure (failed.attempts.map (·.location) == #[first, duplicate, first, duplicate] &&
    failed.attempts.map (·.outcome) == #[.replayedUnknown, .replayedUnknown, .globalRejected, .globalRejected] &&
    failed.replayedUncertain.size == 2 && failed.rejected.size == 2 && failed.uncertain.isEmpty)
    "write trace erased or misattributed replay uncertainty"
  let freshState ← value <| knownState.sent #[{ range, itemIndex := some 2 }]
  let fresh := freshState.snapshot
  ensure (fresh.attempts.size == 3 && fresh.acknowledged.size == 2 && fresh.uncertain.size == 1)
    "write trace changed known results when appending next attempt"
  let mut accumulated : WriteProgress.State := {}
  for index in [:10000] do
    let active ← value <| accumulated.sent #[{ range, itemIndex := some index }]
    accumulated ← value <| active.acknowledge #[.success]
  let snapshot := accumulated.snapshot
  ensure (snapshot.attempts.size == 10000 && snapshot.acknowledged.size == 10000 &&
    (snapshot.attempts[0]?).map (·.location.itemIndex) == some (some 0) &&
    (snapshot.attempts[9999]?).map (·.location.itemIndex) == some (some 9999))
    "large write trace changed chronological order"
  IO.println "write provenance model tests passed"

def runIntegration (host portString mode : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let client ← Client.connect {
    endpoint := .ipv4 address, port := UInt16.ofNat port
    connectTimeoutMs := some 1000, operationTimeoutMs := some 1000
  }
  try
    if mode == "duplicates" then
      let items : Array S7.WriteItem := (Array.range 41).map fun index => {
        range := { area := .dataBlocks, dbNumber := 1, start := 10, count := 1 }
        payload := bytes #[UInt8.ofNat index] }
      match ← client.writeMultiDetailed items with
      | .error failure => throw failure.error
      | .ok (results, progress) =>
          ensure (results.size == 41 && progress.attempts.size == 41) "duplicate item count changed"
          for index in [:41] do
            let expected : S7.WriteItemResult := if index % 7 == 3 then .failure 5 else .success
            ensure (results[index]? == some expected &&
              (progress.attempts[index]?).map (·.location.itemIndex) == some (some index) &&
              (progress.attempts[index]?).map (·.outcome) == some (.itemResult expected) &&
              (progress.acknowledged[index]?).map (·.itemIndex) == some (some index))
              "duplicate item was misattributed across batch boundary"
    else
      let small : S7.WriteItem := {
        range := { area := .dataBlocks, dbNumber := 1, start := 2000, count := 1 }
        payload := bytes #[99] }
      let large : S7.WriteItem := {
        range := { area := .dataBlocks, dbNumber := 1, start := 0, count := 700 }
        payload := bytes (Array.replicate 700 42) }
      let outcome ← if mode == "scalar" then
        match ← client.writeAreaDetailed .dataBlocks 1 0 large.payload with
        | .error failure => pure (.error failure)
        | .ok progress => pure (.ok (#[S7.WriteItemResult.success], progress))
      else client.writeMultiDetailed #[small, large, small]
      match outcome with
      | .error failure =>
          ensure (mode == "drop") "unexpected provenance failure"
          ensure (failure.progress.attempts.size == 3 && failure.progress.acknowledged.size == 2 &&
            failure.progress.attempts.map (·.location.itemIndex) == #[some 0, some 1, some 1] &&
            failure.progress.attempts.map (·.location.chunkByteOffset) == #[0, 0, 212] &&
            (failure.progress.attempts[2]?).map (·.outcome) == some .pending)
            "lost acknowledgement was assigned to wrong caller/chunk"
      | .ok (results, progress) =>
          let offsets := if mode == "reject" then #[0, 0, 212, 0]
            else if mode == "scalar" then #[0, 212, 424, 636] else #[0, 0, 212, 424, 636, 0]
          let indices : Array (Option Nat) := if mode == "reject" then #[some 0, some 1, some 1, some 2]
            else if mode == "scalar" then #[none, none, none, none]
            else #[some 0, some 1, some 1, some 1, some 1, some 2]
          ensure (progress.attempts.map (·.location.itemIndex) == indices &&
            progress.attempts.map (·.location.chunkByteOffset) == offsets &&
            progress.acknowledged.map (·.itemIndex) == indices &&
            progress.acknowledged.map (·.chunkByteOffset) == offsets)
            "chunk provenance changed across fallback/batch boundary"
          ensure (results == (if mode == "reject" then #[.success, .failure 5, .success]
            else if mode == "scalar" then #[.success] else #[.success, .success, .success]))
            "provenance changed caller results"
    client.disconnect
    IO.println s!"write provenance peer passed: {mode}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.WriteProvenanceTests
