import LeanS7.Client

namespace LeanS7.MultiSemanticsTests

open Std.Net

private def require (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"multi semantics: {label}"

private def rejected (value : Except ε α) : Bool :=
  match value with | .error _ => true | .ok _ => false

def run : IO Unit := do
  let good : S7.MemoryRange := { area := .dataBlocks, dbNumber := 1, start := 0, count := 1 }
  let item : S7.WriteItem := { range := good, payload := bytes #[42] }
  require (!rejected (MultiValidation.range { good with count := 65536 })) "logical large count"
  require (rejected (MultiValidation.range { good with count := 0 })) "zero count"
  require (rejected (MultiValidation.range { good with start := 0x1fffff, count := 2 }))
    "byte address endpoint"
  require (rejected (MultiValidation.range {
    good with area := .timers, dbNumber := 0, start := 0xfffffe, count := 2
  })) "element address endpoint"
  require (rejected (MultiValidation.range {
    good with area := .timers, dbNumber := 0, start := 1
  })) "misalignment"
  require (rejected (MultiValidation.writes 240 #[item, { item with payload := ByteArray.empty }]))
    "late payload"
  require (rejected (MultiValidation.writes 240 #[item, {
    item with range := { good with area := .markers }
  }])) "late DB restriction"
  require (rejected (MultiValidation.writes 240 #[item, {
    range := { good with start := 0x1fff00, count := 300 }
    payload := bytes (Array.replicate 300 0)
  }])) "late chunk endpoint"
  require (!rejected (MultiValidation.writes 240 #[{
    range := { good with count := 65536 }, payload := bytes (Array.replicate 65536 0)
  }])) "large write is chunkable"
  require (MultiValidation.writeMaximum 28 .dataBlocks == 0) "small PDU"
  require (MultiValidation.readMaximum 65500 .dataBlocks == 8191) "bit length read cap"
  require (MultiValidation.readMaximum 65500 .timers == 32741) "octet read cap"
  require ((planReadBatch 65500 [{ good with count := 8191 }]).selected.length == 1)
    "representable read batch"
  require ((planReadBatch 65500 [{ good with count := 8192 }]).selected.isEmpty)
    "unrepresentable read must chunk"
  require ((planWriteBatch 65500 [{
    range := { good with count := 8191 }, payload := bytes (Array.replicate 8191 0)
  }]).selected.length == 1) "representable write batch"
  require ((planWriteBatch 65500 [{
    range := { good with count := 8192 }, payload := bytes (Array.replicate 8192 0)
  }]).selected.isEmpty) "unrepresentable write must chunk"

def runIntegration (host portString mode : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let endpoint := match IPv4Addr.ofString host with
    | some address => Transport.Endpoint.ipv4 address
    | none => Transport.Endpoint.hostname host
  let client ← Client.connect {
    endpoint, port := UInt16.ofNat port,
    connectTimeoutMs := some 1000, operationTimeoutMs := some 1000
  }
  try
    let good : S7.MemoryRange := { area := .dataBlocks, dbNumber := 1, start := 0, count := 1 }
    if mode.startsWith "invalid-" then
      let early : S7.WriteItem := { range := good, payload := bytes #[42] }
      -- Put the bad item beyond a batching boundary to guard against incremental
      -- validation. The peer rejects any data operation before disconnect.
      let earlierItems := Array.replicate 21 early
      let bad : S7.WriteItem := match mode with
        | "invalid-payload" => { early with payload := ByteArray.empty }
        | "invalid-range" => { early with range := { good with area := .markers } }
        | "invalid-endpoint" => {
            range := { good with start := 0x1fff00, count := 300 }
            payload := bytes (Array.replicate 300 0) }
        | _ => { early with range := { good with start := 0x200000 } }
      let mut failed := false
      try let _ ← client.writeMulti (earlierItems.push bad); pure ()
      catch error =>
        require (classifyClientError error == .invalidInput) "invalid request error category"
        failed := true
      require failed "invalid request was accepted"
      require (← client.isConnected) "local validation closed session"
    else
      let ranges := #[{ good with count := 700 }, { good with start := 1000 }]
      let successPayload := bytes ((Array.range 700).map fun index => UInt8.ofNat (index * 37 + 7))
      let successful := mode.endsWith "success"
      if mode.startsWith "read-" then
        let result ← client.readMulti ranges
        let first : S7.ReadItemResult := if successful then .success successPayload else .failure 5
        require (result == #[first, .success (bytes #[99])]) "read completion/failure/order"
      else
        let items := #[
          { range := { good with count := 700 },
            payload := if successful then successPayload else bytes (Array.replicate 700 42) },
          { range := { good with start := 1000 }, payload := bytes #[99] }
        ]
        let result ← client.writeMulti items
        let first : S7.WriteItemResult := if successful then .success else .failure 5
        require (result == #[first, .success]) "write completion/failure/order"
    client.disconnect
    IO.println s!"multi semantics passed: {mode}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.MultiSemanticsTests
