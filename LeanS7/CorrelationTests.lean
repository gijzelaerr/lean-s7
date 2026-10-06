import LeanS7.Correlation

namespace LeanS7.CorrelationTests

private def require (value : Bool) (label : String) : IO Unit :=
  unless value do throw <| IO.userError s!"correlation: {label}"

def run : IO Unit := do
  let open_ := Correlation.Waiting.start 7 2
  require (Correlation.scan open_ [7] == .delivered []) "immediate delivery"
  require (Correlation.scan open_ [3, 7, 7] == .delivered [3]) "stale then first match only"
  require (Correlation.scan open_ [3, 4, 7] == .delivered [3, 4]) "allowance spent exactly"
  require (Correlation.scan open_ [3, 4, 5, 7] == .tooManyStale) "allowance exceeded"
  require (Correlation.scan open_ [3] == .awaiting) "no verdict"
  require (Correlation.scan (Correlation.Waiting.start 7 0) [8, 7] == .tooManyStale) "zero allowance"
  -- Reference wrap: the 0xffff request is followed by 0, and a delayed 0xffff
  -- reply never completes the wrapped successor.
  require (Correlation.nextReference 0xffff == 0) "wrap"
  require (Correlation.allocated 0xfffe 2 == 0) "allocated across wrap"
  require (Correlation.step (Correlation.Waiting.start 0 4) 0xffff != .deliver)
    "pre-wrap reply is stale after wrap"
  -- Within one window all allocated references are distinct.
  let refs := (List.range 65536).map (Correlation.allocated 0x1234)
  require ((refs.toArray.qsort (· < ·)).toList.eraseDups.length == 65536) "window uniqueness"
  IO.println "correlation tests passed"

end LeanS7.CorrelationTests
