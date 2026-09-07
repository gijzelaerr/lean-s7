import LeanS7

open LeanS7 Std.Net

def runDemo : IO Unit := do
  match S7.encodeSetupCommunication 1 with
  | .error err => throw <| IO.userError s!"could not encode S7 request: {repr err}"
  | .ok s7 =>
      let cotp := COTP.encodeData { payload := s7 }
      match TPKT.encode { payload := cotp } with
      | .ok packet =>
          IO.println "lean-s7: classic S7 protocol foundation"
          IO.println s!"encoded a {packet.size}-byte TPKT/COTP/S7 setup-communication request"
      | .error err => throw <| IO.userError s!"could not encode connection request: {repr err}"

def runIntegration (host portString : String) : IO Unit := do
  let some address := IPv4Addr.ofString host
    | throw <| IO.userError s!"invalid IPv4 address: {host}"
  let some portNat := portString.toNat?
    | throw <| IO.userError s!"invalid TCP port: {portString}"
  if portNat > 65535 then
    throw <| IO.userError s!"TCP port is out of range: {portNat}"
  let client ← Client.connect { address, port := UInt16.ofNat portNat }
  try
    let initial ← client.dbRead 1 0 4
    unless initial == bytes #[0xaa, 0xbb, 0xcc, 0xdd] do
      throw <| IO.userError "python-snap7 emulator returned unexpected initial DB data"
    let written := bytes #[0xde, 0xad, 0xbe, 0xef]
    client.dbWrite 1 16 written
    let readBack ← client.dbRead 1 16 written.size
    unless readBack == written do
      throw <| IO.userError "DB write/read-back mismatch"
    client.disconnect
    IO.println s!"lean-s7 integration passed against {host}:{portNat} (PDU {client.pduLength})"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

def main (args : List String) : IO Unit := do
  match args with
  | ["integration", host, port] => runIntegration host port
  | [] => runDemo
  | _ => throw <| IO.userError "usage: lean-s7 [integration <IPv4 address> <port>]"
