import LeanS7.ClockCodecAssurance
import LeanS7.Client

namespace LeanS7.ClockCodecAssuranceTests

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def checkRoundTrip (value : S7.PlcDateTime) : IO Unit := do
  let .ok payload := S7.encodePlcDateTime value
    | throw <| IO.userError s!"clock encoding rejected valid value {repr value}"
  require (payload.size == 10) "clock encoder changed payload length"
  require ((S7.decodePlcDateTime payload).toOption == some value)
    s!"clock roundtrip changed {repr value}"

def run : IO Unit := do
  let base : S7.PlcDateTime := {
    year := 2024, month := 2, day := 29, hour := 23, minute := 59,
    second := 58, millisecond := 123, weekday := 1 }
  let golden := bytes #[0, 0x19, 0x24, 0x02, 0x29, 0x23, 0x59, 0x58, 0x12, 0x31]
  require ((S7.encodePlcDateTime base).toOption == some golden) "clock golden encoding changed"
  require ((S7.decodePlcDateTime golden).toOption == some base) "clock golden decoding changed"
  -- An A–F final high nibble used to produce plausible 130–135 milliseconds.
  -- Each weekday remains independently valid, so calendar validation cannot
  -- accidentally hide failure to validate this decimal digit.
  for digit in [10:16] do
    for weekday in [1:8] do
      let invalid := golden.set! 9 (UInt8.ofNat (digit * 16 + weekday))
      let rejected := match S7.decodePlcDateTime invalid with
        | .error error => error == .invalidField 9 "invalid BCD millisecond digit"
        | .ok _ => false
      require rejected
        s!"clock accepted packed nondecimal millisecond digit {digit}, weekday {weekday}"
  -- Exercise both nibbles of every complete BCD field.
  for offset in [2:9] do
    for digit in [10:16] do
      for raw in #[digit * 16 + 1, 16 + digit] do
        let result := S7.decodePlcDateTime (golden.set! offset (UInt8.ofNat raw))
        match result with
        | .error (.invalidField found _) =>
          require (found == offset) "clock BCD rejection pointed to a different field"
        | _ => throw <| IO.userError s!"clock accepted nondecimal BCD at byte {offset}"
  for length in [:10] do
    require ((S7.decodePlcDateTime (golden.extract 0 length)).toBool == false)
      s!"clock accepted truncated {length}-byte payload"
  require ((S7.decodePlcDateTime (golden.push 0)).toBool == false)
    "clock accepted trailing bytes"
  -- These have decimal BCD digits and complete extents. They must reach
  -- calendar/time validation in the decoder, not just encoder validation.
  for invalid in #[golden.set! 2 0x23,
      golden.set! 3 0x04 |>.set! 4 0x31,
      golden.set! 3 0, golden.set! 3 0x13,
      golden.set! 4 0, golden.set! 4 0x32,
      golden.set! 5 0x24, golden.set! 6 0x60, golden.set! 7 0x60,
      golden.set! 9 0x30, golden.set! 9 0x38] do
    match S7.decodePlcDateTime invalid with
    | .error (.invalidField _ _) => pure ()
    | _ => throw <| IO.userError "clock decoder accepted invalid decimal calendar/time fields"
  for millisecond in [:1000] do
    for weekday in [1:8] do
      checkRoundTrip { base with millisecond, weekday }
  -- Every calendar date in the supported century, including the year-90 pivot
  -- and leap-year transitions, plus decimal carry boundaries for milliseconds.
  let mut calendarDates := 0
  for year in [1990:2090] do
    for month in [1:13] do
      for day in [1:32] do
        let candidate : S7.PlcDateTime := {
          year, month, day, hour := if day % 2 == 0 then 0 else 23,
          minute := if month % 2 == 0 then 0 else 59,
          second := if year % 2 == 0 then 0 else 59,
          weekday := day % 7 + 1 }
        match candidate.validate with
        | .error _ =>
          require ((S7.encodePlcDateTime candidate).toBool == false)
            "clock encoder accepted an invalid calendar date"
        | .ok () =>
          calendarDates := calendarDates + 1
          for millisecond in #[0, 1, 9, 10, 99, 100, 123, 990, 999] do
            checkRoundTrip { candidate with millisecond }
  require (calendarDates == 36525) "supported century calendar-date count changed"
  for invalid in #[{ base with year := 1989 }, { base with year := 2090 },
      { base with month := 0 }, { base with month := 13 },
      { base with day := 0 }, { base with year := 2023 },
      { base with hour := 24 }, { base with minute := 60 },
      { base with second := 60 }, { base with millisecond := 1000 },
      { base with weekday := 0 }, { base with weekday := 8 }] do
    require ((S7.encodePlcDateTime invalid).toBool == false)
      s!"clock encoder accepted invalid value {repr invalid}"
  IO.println "clock assurance tests passed: all 36,525 supported calendar dates and 7,000 millisecond/weekday combinations"

/-- Read-only live regressions use complete correlated USER_DATA replies.
    Malformed typed clock payloads must close the session before later reads. -/
def runIntegration (host portString digitString : String) : IO Unit := do
  let some port := portString.toNat? | throw <| IO.userError "invalid clock peer port"
  let some digit := digitString.toNat? | throw <| IO.userError "invalid clock peer digit"
  require (port < 65536 && digit < 16) "clock peer argument out of range"
  let client ← Client.connect {
    endpoint := .hostname host, port := UInt16.ofNat port
    connectTimeoutMs := some 1000, operationTimeoutMs := some 1000
    reconnectRetries := 1 }
  try
    if digit < 10 then
      let actual ← client.getPlcDateTime
      let expected : S7.PlcDateTime := {
        year := 2024, month := 2, day := 29, hour := 23, minute := 59,
        second := 58, millisecond := 120 + digit, weekday := digit % 7 + 1 }
      require (actual == expected) "clock peer changed decimal carry/weekday value"
      require (← client.isConnected) "valid clock reply poisoned session"
    else
      let rejected ← try
        discard <| client.getPlcDateTime
        pure false
      catch error =>
        require (classifyClientError error == .protocol) "malformed clock error category changed"
        require (((toString error).splitOn "invalid BCD millisecond digit").length > 1)
          "malformed clock error missed decimal digit diagnostic"
        pure true
      require rejected "malformed clock reply was accepted"
      require (!(← client.isConnected)) "malformed clock reply left session usable"
      let laterRejected ← try
        discard <| client.getPlcDateTime
        pure false
      catch error => pure (classifyClientError error == .disconnected)
      require laterRejected "later clock read escaped poisoned session"
    client.disconnect
    IO.println s!"clock full-stack assurance passed: packed digit {digit}"
  catch error =>
    try client.disconnect catch _ => pure ()
    throw error

end LeanS7.ClockCodecAssuranceTests
