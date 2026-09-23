import LeanS7.Transport

namespace LeanS7.TransportResourceTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def run : IO Unit := do
  let mut state : COTP.Reassembly := {}
  for index in [:3] do
    let segment : COTP.Data := {
      payload := ByteArray.empty
      endOfTransmission := index == 2 }
    match state.pushResourceBounded segment 0 3 with
    | .ok (next, complete) =>
        require (next.segments == index + 1 && next.payload.isEmpty)
          "empty COTP segment did not consume work budget"
        require (complete == (index == 2)) "segment bound changed EOT"
        state := next
    | .error error => throw <| IO.userError s!"valid empty segment rejected: {repr error}"
  match state.pushResourceBounded { payload := ByteArray.empty } 0 3 with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "segment limit bypassed with empty payload"
  match COTP.Reassembly.pushResourceBounded {} { payload := bytes #[1] } 0 3 with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "segment count check bypassed byte limit"
  match COTP.Reassembly.pushResourceBounded {} { payload := ByteArray.empty } 0 0 with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError "zero segment budget accepted a TPDU"
  IO.println "COTP transport resource model tests passed"

/-- Raw TCP peers isolate framing/resource checks from client negotiation. -/
def runIntegration (host portString mode : String) : IO Unit := do
  let some address := Std.Net.IPv4Addr.ofString host | throw <| IO.userError "invalid host"
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let socket ← Std.Async.TCP.Socket.Client.mk
  let task ← (socket.connect (Std.Net.SocketAddressV4.mk address (UInt16.ofNat port))).toIO
  task.block
  try
    let maxSegments := if mode == "zero" then 0 else 3
    let outcome ← try
      -- No receive deadline: work bounds must terminate an adversarial stream.
      pure (.ok (← Transport.receiveData socket none 3 maxSegments) : Except IO.Error ByteArray)
    catch error => pure (.error error)
    match outcome with
    | .ok payload =>
        require (mode == "exact" || mode == "reserved") "invalid stream accepted"
        require (payload == bytes #[1, 2, 3]) "reassembly changed arrival order"
    | .error error =>
        let diagnostic := if mode == "empty" || mode == "tiny" || mode == "zero" then
          "segment limit"
        else if mode == "version" then "unsupported TPKT version"
        else if mode == "short" then "invalid TPKT frame length"
        else "body exceeds receive limit"
        require (classifyClientError error == .protocol) s!"wrong category: {error}"
        require (((toString error).splitOn diagnostic).length > 1)
          s!"wrong resource diagnostic: {error}"
    Transport.shutdown socket
    IO.println s!"transport resource case passed: {mode}"
  catch error =>
    try Transport.shutdown socket catch _ => pure ()
    throw error

end LeanS7.TransportResourceTests
