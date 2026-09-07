import LeanS7

open LeanS7

def main : IO Unit := do
  match S7.encodeSetupCommunication 1 with
  | .error err => throw <| IO.userError s!"could not encode S7 request: {repr err}"
  | .ok s7 =>
      let cotp := COTP.encodeData { payload := s7 }
      match TPKT.encode { payload := cotp } with
      | .ok packet =>
          IO.println "lean-s7: classic S7 protocol foundation"
          IO.println s!"encoded a {packet.size}-byte TPKT/COTP/S7 setup-communication request"
      | .error err =>
          throw <| IO.userError s!"could not encode connection request: {repr err}"
