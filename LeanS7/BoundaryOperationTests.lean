import LeanS7.Client

namespace LeanS7.BoundaryOperationTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"boundary operations: {message}"

private def text (wide : Bool) (capacity : Nat) : String :=
  if wide then
    String.ofList ((if capacity % 2 == 1 then ['x'] else []) ++
      List.replicate (capacity / 2) '🌍')
  else String.ofList (List.replicate capacity 'é')

private def payload (id count : Nat) : ByteArray :=
  bytes <| (Array.range count).map fun i => UInt8.ofNat (id * 19 + i * 37)

/-- Stable operation IDs retain wire addresses and values when plans are reduced. -/
def runIntegration (host portString pduString plan : String) : IO Unit := do
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some pdu := pduString.toNat? | throw <| IO.userError "invalid PDU"
  let client ← Client.connect {
    endpoint := .ipv4 address, port := UInt16.ofNat port,
    connectTimeoutMs := some 1000, operationTimeoutMs := some 1000,
    transferReceiveTimeoutMs := some 3000, reconnectRetries := 1 }
  try
    require (client.pduLength.toNat == pdu) "negotiated PDU"
    for token in plan.splitOn "|" do
      if token.isEmpty then continue
      let [idString, kind, sizeString] := token.splitOn ":"
        | throw <| IO.userError s!"invalid boundary token {token}"
      let some id := idString.toNat? | throw <| IO.userError "invalid operation ID"
      let some count := sizeString.toNat? | throw <| IO.userError "invalid size"
      let start := id * 4096
      let terminal := kind == "q" || kind == "u" || kind == "z" || kind == "d"
      if kind == "r" || kind == "R" then
        require ((← client.dbRead 1 start count) == payload id count) s!"{token}: read payload"
      else if kind == "w" then client.dbWrite 1 start (payload id count)
      else if kind == "s" || kind == "t" then
        let actual ← if kind == "t" then client.dbReadWString 1 start else client.dbReadString 1 start
        require (actual == text (kind == "t") count) s!"{token}: text payload"
      else if kind == "S" then client.dbWriteString 1 start count (text false count)
      else if kind == "T" then client.dbWriteWString 1 start count (text true count)
      else if kind == "d" then
        match ← client.writeAreaDetailed .dataBlocks 1 start (payload id count) with
        | .ok _ => throw <| IO.userError s!"{token}: lost ACK accepted"
        | .error failure =>
            require (failure.kind == .disconnected && failure.progress.uncertain.size == 1 &&
              failure.progress.acknowledged.isEmpty && failure.progress.attempts.size == 1)
              s!"{token}: write replay/progress"
      else if kind == "j" || terminal then
        let error ← try
          if kind == "q" then discard <| client.dbReadString 1 start
          else if kind == "u" then discard <| client.dbReadWString 1 start
          else discard <| client.dbRead 1 start count
          pure (none : Option IO.Error)
        catch error => pure (some error)
        let some error := error | throw <| IO.userError s!"{token}: fault accepted"
        require (classifyClientError error == if kind == "j" then .plcRejected else .protocol)
          s!"{token}: fault category"
      else throw <| IO.userError s!"unknown boundary operation {kind}"
      require ((← client.isConnected) == !terminal) s!"{token}: session disposition"
      if terminal then
        let blocked ← try
          discard <| client.dbRead 1 0 1
          pure false
        catch error => pure (classifyClientError error == .disconnected)
        require blocked s!"{token}: terminal session resurrected"
    client.disconnect
    IO.println s!"boundary operation plan passed: PDU={pdu} {plan}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.BoundaryOperationTests
