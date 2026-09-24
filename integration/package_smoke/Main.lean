import LeanS7

open LeanS7

-- Compile the public proof and IO surfaces as an external Lake consumer.
example : CoreProtocolAssurance := coreProtocolAssurance

def consumerConfig : ClientConfig := {
  endpoint := .hostname "localhost"
  port := 1102
}

def consumerConnected : Client → IO Bool := Client.isConnected

def main : IO Unit := do
  let .ok packet := S7.encodeSetupCommunication 0x1234
    | throw <| IO.userError "consumer setup encoder failed"
  let .ok job := S7.decodeJob packet
    | throw <| IO.userError "consumer setup decoder failed"
  unless job.reference == 0x1234 do
    throw <| IO.userError "consumer reference round trip failed"
  let .ok value := Value.getUInt64 (Value.putUInt64 0xfedcba9876543210)
    | throw <| IO.userError "consumer typed-value decoder failed"
  unless value == 0xfedcba9876543210 do
    throw <| IO.userError "consumer typed-value round trip failed"
  IO.println "external Lake consumer smoke passed"
