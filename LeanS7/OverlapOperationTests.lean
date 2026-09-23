import LeanS7.Client

namespace LeanS7.OverlapOperationTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"overlap operations: {message}"

private def initialMemory (size : Nat) : ByteArray :=
  bytes <| (Array.range size).map fun index => UInt8.ofNat (index * 29 + 113)

private def payload (salt count : Nat) : ByteArray :=
  bytes <| (Array.range count).map fun index => UInt8.ofNat (salt * 17 + index * 43)

private def replace (memory : ByteArray) (start : Nat) (data : ByteArray) : ByteArray :=
  bytes <| (Array.range memory.size).map fun index =>
    if start ≤ index && index < start + data.size then data[index - start]!
    else memory[index]!

/-- Replay stable, parameterized operations against a local logical memory model.
    Bit expectations use arithmetic, independently of the client's bit codec. -/
def runIntegration (host portString pduString memorySizeString plan : String) : IO Unit := do
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let some pdu := pduString.toNat? | throw <| IO.userError "invalid PDU"
  let some memorySize := memorySizeString.toNat? | throw <| IO.userError "invalid memory size"
  let client ← Client.connect {
    endpoint := .ipv4 address, port := UInt16.ofNat port,
    connectTimeoutMs := some 1000, operationTimeoutMs := some 1000,
    transferReceiveTimeoutMs := some 3000, reconnectRetries := 0 }
  try
    require (client.pduLength.toNat == pdu) "negotiated PDU"
    let mut memory := initialMemory memorySize
    for token in plan.splitOn "|" do
      if token.isEmpty then continue
      let [_idString, kind, startString, sizeString, argumentString] := token.splitOn ":"
        | throw <| IO.userError s!"invalid overlap token {token}"
      let some start := startString.toNat? | throw <| IO.userError "invalid start"
      let some size := sizeString.toNat? | throw <| IO.userError "invalid size"
      let some argument := argumentString.toNat? | throw <| IO.userError "invalid argument"
      let count := if kind == "b" then 1 else size
      require (start + count ≤ memorySize) s!"{token}: range outside model"
      if kind == "r" then
        require ((← client.dbRead 1 start size) == memory.extract start (start + size))
          s!"{token}: model readback"
      else if kind == "w" then
        let data := payload argument size
        client.dbWrite 1 start data
        memory := replace memory start data
      else if kind == "b" then
        require (size < 8 && argument < 2) s!"{token}: invalid bit parameters"
        let value := memory[start]!.toNat
        let power := 2 ^ size
        let old := value / power % 2
        let updated := if argument == 1 then
          if old == 0 then value + power else value
        else if old == 1 then value - power else value
        client.dbWriteBit 1 start size (argument == 1)
        memory := replace memory start (bytes #[UInt8.ofNat updated])
        require ((← client.dbReadBit 1 start size) == (argument == 1))
          s!"{token}: bit readback"
      else throw <| IO.userError s!"unknown overlap operation {kind}"
      require (← client.isConnected) s!"{token}: session unexpectedly disconnected"
    require ((← client.dbRead 1 0 memorySize) == memory) "final full-memory observation"
    client.disconnect
    IO.println s!"overlap operation plan passed: PDU={pdu} {plan}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.OverlapOperationTests
