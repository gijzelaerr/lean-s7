import LeanS7.SessionAssurance

namespace LeanS7.SessionAssuranceTests
open Conformance.Sessions

/-- Boundary controls complement the universal pure-model theorems, especially
    manually constructed states that no exported happy-path trace visits. -/
def run : IO Unit := do
  let location : WriteLocation := {
    range := { area := .dataBlocks, dbNumber := 1, start := 0, count := 1 } }
  let phases : Array Phase := #[.idle, .ready, .awaiting, .reconnectCotp,
    .reconnectSetup, .failed, .completed, .closed]
  let failures : Array ClientErrorKind := #[.invalidInput, .protocol, .plcRejected,
    .timeout, .disconnected, .lifecycle, .transport, .other]
  let events : Array Event := #[.begin, .send, .reconnectSetup, .reconnected,
    .disconnect, .response ByteArray.empty] ++ failures.map Event.failure
  let mut checks := 0
  for write in #[false,true] do
    for allow in #[false,true] do
      for budget in [:4] do
        let config : Config := { write, allow, budget, reference := 65535, locations := #[location] }
        for lifecycle in #[Lifecycle.State.connected, .disconnected, .closed] do
          for phase in phases do
            for active in #[(none : Option UInt16), some 65535] do
              let state : State := {
                lifecycle, phase, active, remaining := budget, sends := 1,
                progress := { pending := #[location] } }
              for event in events do
                let after := (step config state event).1
                if state.active.isSome && after.remaining > state.remaining then
                  throw <| IO.userError "typed active request replenished allowance"
                if lifecycle == .closed && after.lifecycle != .closed then
                  throw <| IO.userError "typed closed model resurrected"
                checks := checks + 1
              for kind in failures do
                let after := (step config state (.failure kind)).1
                if phase == .reconnectCotp || phase == .reconnectSetup then
                  unless after.sends == state.sends && after.progress.trace == state.progress.trace do
                    throw <| IO.userError "typed failed reconnect manufactured write progress"
  unless checks == 10752 do throw <| IO.userError s!"typed session coverage changed: {checks}"
  IO.println s!"typed session model controls passed: {checks} transitions"

end LeanS7.SessionAssuranceTests
