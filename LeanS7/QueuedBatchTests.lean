import LeanS7.Client

namespace LeanS7.QueuedBatchTests

private def require (condition : Bool) (stage : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"queued batches: {stage}"

private def payload (index offset count : Nat) : ByteArray :=
  ByteArray.mk <| (Array.range count).map fun position =>
    UInt8.ofNat (index * 29 + (offset + position) * 37 + 11)

private def range (sizes : Array Nat) (index : Nat) : S7.MemoryRange := {
  area := .dataBlocks, dbNumber := 1
  start := if index + 1 == sizes.size then 0 else index * 2048
  count := sizes[index]! }

private def admission (client : Client) (expected : Nat) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 3000
  repeat
    let count ← client.pendingOperationCount
    if count == expected then return
    require (count < expected) s!"admission overshot {expected}: {count}"
    require ((← IO.monoMsNow) < deadline) s!"admission timed out at {count}/{expected}"
    IO.sleep 1

private def checkRead (task : Task (Except IO.Error (Array S7.ReadItemResult)))
    (sizes : Array Nat) (closed : Bool) (stage : String) : IO Unit := do
  match ← IO.wait task with
  | .error error =>
      require (closed && classifyClientError error == .disconnected)
        s!"{stage}: unexpected error {error}"
  | .ok results =>
      require (!closed) s!"{stage}: closed operation succeeded"
      require (results.size == sizes.size) s!"{stage}: result count changed"
      for index in [:sizes.size] do
        let expected : S7.ReadItemResult := if index == 2 then .failure 5
          else .success (payload index 0 sizes[index]!)
        require (results[index]? == some expected) s!"{stage}: caller item {index} reordered/corrupted"

/-- An independently computed chronological per-item/chunk trace. This test does
    not call the implementation's batching planner or inspect private state. -/
private def locations (sizes : Array Nat) (maximum : Nat) : Array WriteLocation := Id.run do
  let mut result := #[]
  for index in [:sizes.size] do
    let original := range sizes index
    let mut offset := 0
    while offset < original.count do
      let count := min maximum (original.count - offset)
      result := result.push {
        range := { original with start := original.start + offset, count }
        itemIndex := some index, chunkByteOffset := offset }
      offset := offset + count
  return result

private def firstWriteCount (sizes : Array Nat) (pdu : Nat) : Nat := Id.run do
  let mut used := 12
  let mut count := 0
  for size in sizes do
    let next := used + 16 + size + size % 2
    if count == 20 || next > pdu then break
    used := next
    count := count + 1
  return count

private def checkProgress (progress : WriteProgress) (expected : Array WriteLocation)
    (acknowledged pending : Nat) : IO Unit := do
  require (progress.attempts.size == acknowledged + pending &&
    progress.acknowledged.size == acknowledged && progress.uncertain.size == pending)
    "write progress: acknowledged/uncertain counts"
  require (progress.replayedUncertain.isEmpty && progress.rejected.isEmpty)
    "write progress: unexpected replay/global rejection"
  for index in [:progress.attempts.size] do
    let some attempt := progress.attempts[index]? | throw <| IO.userError "missing write attempt"
    require (some attempt.location == expected[index]?) s!"write progress: provenance {index}"
    let code : S7.WriteItemResult := if attempt.location.itemIndex == some 2 then .failure 5 else .success
    require (attempt.outcome == (if index < acknowledged then .itemResult code else .pending))
      s!"write progress: outcome {index}"
    if index < acknowledged then
      let some ack := progress.acknowledged[index]? | throw <| IO.userError "missing write acknowledgement"
      let location : WriteLocation := {
        range := ack.range, itemIndex := ack.itemIndex, chunkByteOffset := ack.chunkByteOffset }
      require (location == attempt.location && ack.result == code)
        s!"write progress: acknowledgement provenance {index}"
    else
      require (progress.uncertain[index - acknowledged]? == some attempt.location.range)
        s!"write progress: uncertain range {index}"

def runIntegration (host portString pduString mode sizesString : String) : IO Unit := do
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid queued batch host"
  let some port := portString.toNat? | throw <| IO.userError "invalid queued batch port"
  let some pdu := pduString.toNat? | throw <| IO.userError "invalid queued batch PDU"
  let sizes ← (sizesString.splitOn ",").toArray.mapM fun token =>
    match token.toNat? with
    | some value => pure value
    | none => throw <| IO.userError "invalid queued batch size"
  require (pdu == 240 || pdu == 480) "unsupported PDU"
  require (sizes.size ≥ 25 && sizes.all (fun size => size > 0) && sizes[0]? == sizes.back?)
    "invalid mixed-size plan"
  require (["success", "early-retry", "read-partial-drop", "write-drop", "write-partial-drop"].contains mode)
    "invalid mode"
  let client ← Client.connect {
    endpoint := .ipv4 address, port := UInt16.ofNat port
    connectTimeoutMs := some 1000, operationTimeoutMs := some 3000
    transferReceiveTimeoutMs := some 10000, reconnectRetries := 1 }
  try
    let ranges := (Array.range sizes.size).map (range sizes)
    let items := ranges.mapIdx fun index value => ({
      range := value, payload := payload index 0 value.count } : S7.WriteItem)
    let first ← IO.asTask <| client.readMulti ranges
    admission client 1
    let _ ← (← IO.getStdin).getLine
    let write ← IO.asTask <| client.writeMultiDetailed items
    admission client 2
    let second ← IO.asTask <| client.readMulti ranges
    admission client 3
    let closing ← IO.asTask client.disconnect
    admission client 4
    let late ← IO.asTask <| client.writeMultiDetailed items
    admission client 5
    IO.println "queued batches admitted 5"
    (← IO.getStdout).flush
    let readClosed := mode == "read-partial-drop"
    let writeClosed := readClosed || mode == "write-drop" || mode == "write-partial-drop"
    checkRead first sizes readClosed "first read"
    let expected := locations sizes (pdu - 28)
    match ← IO.wait write with
    | .error error => throw error
    | .ok (.error failure) =>
        require (writeClosed && failure.kind == .disconnected) "write failure category"
        let acknowledged := if mode == "write-partial-drop" then
          (expected.toList.takeWhile fun location => !(location.itemIndex == some (sizes.size - 2) &&
            location.chunkByteOffset == pdu - 28)).length else 0
        let pending := if mode == "write-drop" then firstWriteCount sizes pdu
          else if mode == "write-partial-drop" then 1 else 0
        checkProgress failure.progress expected acknowledged pending
    | .ok (.ok (results, progress)) =>
        require (!writeClosed && results.size == sizes.size) "write succeeded after terminal closure"
        for index in [:sizes.size] do
          require (results[index]? == some (if index == 2 then .failure 5 else .success))
            s!"write result caller order {index}"
        checkProgress progress expected expected.size 0
    checkRead second sizes writeClosed "second queued read"
    match ← IO.wait closing with
    | .error error => throw error
    | .ok () => pure ()
    match ← IO.wait late with
    | .ok (.error failure) =>
        require (failure.kind == .disconnected && failure.progress.attempts.isEmpty &&
          failure.progress.acknowledged.isEmpty && failure.progress.uncertain.isEmpty)
          "late write sent/resurrected or inherited earlier progress"
    | _ => throw <| IO.userError "queued batches: late write did not reject cleanly"
    require (!(← client.isConnected) && (← client.pendingOperationCount) == 0) "queue/lifecycle cleanup"
    client.disconnect
    IO.println s!"queued batches {pdu} {mode} passed ({sizes.size} caller items)"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.QueuedBatchTests
