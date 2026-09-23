import LeanS7.Client

namespace LeanS7.RetryProgressTests
open Std.Net

private def require (value : Bool) (label : String) : IO Unit :=
  unless value do throw <| IO.userError s!"retry/progress: {label}"

def run : IO Unit := do
  require (retryPermitted .readOnly false) "reads retry"
  require (!retryPermitted .potentiallyMutating false) "default denies mutation/raw replay"
  require (retryPermitted .potentiallyMutating true) "explicit opt-in"
  let failure : WriteFailure := { error := ClientError.timeout "test", progress := {} }
  require (failure.kind == .timeout) "typed failure category"

def runIntegration (host portString mode : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid port"
  let client ← Client.connect {
    endpoint := .hostname host, port := UInt16.ofNat port,
    connectTimeoutMs := some 500, operationTimeoutMs := some 500,
    reconnectRetries := 1, allowPotentiallyMutatingRetries := mode == "write-opt-in" || mode.startsWith "replay-"
  }
  try
    let range : S7.MemoryRange := { area := .dataBlocks, dbNumber := 1, start := 0, count := 700 }
    let payload := bytes (Array.replicate 700 42)
    if mode == "read-retry" then
      require ((← client.dbRead 1 0 1) == bytes #[42]) "read retried"
    else if mode == "control-no-retry" || mode == "clock-no-retry" ||
        mode == "security-no-retry" || mode == "upload-no-retry" then
      let mut failed := false
      try
        if mode == "clock-no-retry" then client.setPlcDateTime {
          year := 2026, month := 9, day := 23, hour := 12, minute := 0, second := 0,
          millisecond := 0, weekday := 4 }
        else if mode == "security-no-retry" then client.setSessionPassword "test"
        else if mode == "upload-no-retry" then discard <| client.upload .dataBlock 1
        else client.plcStop
      catch _ => failed := true
      require failed "lost control acknowledgement"
      require (!(← client.isConnected)) "control closes after lost ACK"
    else if mode == "raw-no-retry" then
      let request ← match S7.encodeAreaRead 10 { range with count := 1 } with
        | .ok value => pure value
        | .error error => throw <| IO.userError (reprStr error)
      let mut failed := false
      try discard <| client.rawExchange 10 request catch _ => failed := true
      require failed "raw unknown read does not retry"
    else if mode == "write-opt-in" then
      match ← client.writeAreaDetailed .dataBlocks 1 0 (bytes #[42]) with
      | .ok progress => require (progress.acknowledged.size == 1 && progress.uncertain.isEmpty &&
          progress.replayedUncertain.size == 1) "opt-in acknowledged but earlier attempt uncertain"
      | .error failure => throw failure.error
    else if mode.startsWith "replay-" then
      let short : S7.WriteItem := { range := { range with count := 1 }, payload := bytes #[42] }
      if mode == "replay-reconnect-reject" then
        match ← client.writeAreaDetailed .dataBlocks 1 0 short.payload with
        | .ok _ => throw <| IO.userError "expected reconnect rejection"
        | .error failure =>
            require (failure.progress.acknowledged.isEmpty && failure.progress.uncertain.isEmpty &&
              failure.progress.rejected.isEmpty && failure.progress.replayedUncertain.size == 1)
              "failed reconnect retains only earlier attempted write"
      else if mode == "replay-scalar-reject" then
        match ← client.writeAreaDetailed .dataBlocks 1 0 short.payload with
        | .ok _ => throw <| IO.userError "expected replay rejection"
        | .error failure =>
            require (failure.kind == .plcRejected && failure.progress.uncertain.isEmpty &&
              failure.progress.rejected.size == 1 && failure.progress.replayedUncertain.size == 1)
              "replay rejection retains prior unknown effects"
      else
        match ← client.writeMultiDetailed #[short] with
        | .error failure => throw failure.error
        | .ok (results, progress) =>
            require (results == #[.failure 5] && progress.uncertain.isEmpty &&
              progress.acknowledged.size == 1 && progress.replayedUncertain.size == 1)
              "replay item rejection retains prior unknown effects"
    else
      let result ← if mode.startsWith "multi-" then
        match ← client.writeMultiDetailed #[{ range, payload }] with
        | .error failure => pure (.error failure)
        | .ok (_, progress) => pure (.ok progress)
      else client.writeAreaDetailed .dataBlocks 1 0 payload
      match result with
      | .ok progress =>
          require (mode == "multi-reject") "expected write failure"
          require (progress.acknowledged.size == 2 && progress.uncertain.isEmpty) "per-item reject known"
          require ((progress.acknowledged[0]?).map (·.result) == some .success &&
            (progress.acknowledged[1]?).map (·.result) == some (.failure 5)) "prefix success and reject status"
      | .error failure =>
          let firstFailure := mode == "write-no-retry"
          require (failure.progress.acknowledged.size == (if firstFailure then 0 else 1)) "acknowledged prefix"
          if mode.endsWith "reject" then
            require (failure.kind == .plcRejected && failure.progress.uncertain.isEmpty &&
              failure.progress.rejected.size == 1) "known scalar rejection"
          else
            require (failure.progress.uncertain.size == 1) "uncertain last write"
            require ((failure.progress.uncertain[0]?).map (·.start) == some (if firstFailure then 0 else 212)) "uncertain address"
            require (!(← client.isConnected)) "lost ACK disconnects"
    try client.disconnect catch _ => pure ()
    IO.println s!"retry/progress passed: {mode}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.RetryProgressTests
