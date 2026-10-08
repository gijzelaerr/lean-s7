import Lean
import LeanS7

open Lean

/-- Axioms a claimed theorem may depend on. Anything else (notably `sorryAx`) fails the audit. -/
def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Theorems the documentation relies on without naming them in a recognizable form
    (no underscore) or that are cited by name in reports rather than the docs. Each must
    exist as a theorem. Names that the docs do cite as `Namespace.name_with_underscore`
    are discovered from the docs themselves (see `docTheoremNames`). -/
def explicitTheorems : List Name :=
  [`LeanS7.coreProtocolAssurance,
   `LeanS7.Correlation.step_deliver_iff, `LeanS7.Correlation.scan_delivered,
   `LeanS7.Correlation.scan_tooManyStale, `LeanS7.Correlation.allocated_succ,
   `LeanS7.Correlation.allocated_injective_window,
   `LeanS7.Correlation.earlier_reply_not_delivered,
   `LeanS7.Correlation.Gate.submit_sequence, `LeanS7.Correlation.Gate.mayStart_unique,
   `LeanS7.Correlation.Gate.mayStart_after_earlier, `LeanS7.Correlation.Gate.finish_next,
   `LeanS7.Correlation.Gate.submit_not_next, `LeanS7.Correlation.Gate.submit_valid,
   `LeanS7.Correlation.Gate.finish_valid, `LeanS7.Correlation.Gate.pending_submit,
   `LeanS7.Correlation.Gate.pending_finish]

/-- Documentation files whose backticked theorem names are checked. -/
def docFiles : List String := ["README.md", "docs/COMPLETENESS.md", "docs/RELEASE.md"]

/-- Namespaces tried, in order, when a doc cites a theorem relative to the project. -/
def docNamespaces : List String :=
  ["", "LeanS7.", "LeanS7.S7.", "LeanS7.Value.", "LeanS7.Correlation."]

/-- A backticked token that looks like a theorem name: dotted identifier whose last
    component starts with a lowercase letter and contains an underscore
    (`decodeEndUpload_contract`, `TPKT.decode_encode`). Constants such as `DATE_AND_TIME`
    and file names do not match. -/
def looksLikeTheorem (token : String) : Bool :=
  let allowed := token.all fun c => c.isAlphanum || c == '_' || c == '.'
  match (token.splitOn ".").getLast? with
  | some last =>
    allowed && !last.isEmpty && last.front.isLower && (last.splitOn "_").length > 1 &&
      (token.splitOn ".").all (· != "")
  | none => false

/-- Backticked tokens (odd positions of a split on the backtick), whitespace-free. -/
def backtickedTokens (text : String) : List String :=
  let pieces := text.splitOn "`"
  (pieces.zipIdx.filter (fun (_, index) => index % 2 == 1)).map (·.1)
    |>.filter (fun token => !token.isEmpty && !token.any Char.isWhitespace)

def resolveTheorem (env : Environment) (token : String) : Option Name :=
  docNamespaces.findSome? fun prefix_ =>
    let name := (prefix_ ++ token).toName
    match env.find? name with
    | some (.thmInfo _) => some name
    | _ => none

def isProjectModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `LeanS7
  | none => false

unsafe def audit : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanS7 }] {} 0
  let mut failures := 0
  let mut checked := 0
  for name in explicitTheorems do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ =>
      IO.eprintln s!"explicitly listed theorem missing (or not a theorem): {name}"
      failures := failures + 1
  let mut cited := 0
  for file in docFiles do
    let text ← IO.FS.readFile file
    for token in (backtickedTokens text).eraseDups do
      if looksLikeTheorem token then
        cited := cited + 1
        if (resolveTheorem env token).isNone then
          IO.eprintln s!"{file}: cited theorem `{token}` does not exist"
          failures := failures + 1
  for (name, info) in env.constants.toList do
    if isProjectModule env name then
      match info with
      | .thmInfo _ =>
        checked := checked + 1
        let (axioms, _) ← (collectAxioms name : CoreM (Array Name)).toIO { fileName := "<audit>", fileMap := default } { env }
        let bad := axioms.filter (fun a => !allowedAxioms.contains a)
        unless bad.isEmpty do
          IO.eprintln s!"{name} depends on disallowed axioms: {bad}"
          failures := failures + 1
      | _ => pure ()
  IO.println s!"axiom audit: {checked} theorems checked, {cited} documented names resolved, {failures} failures"
  return if failures == 0 then 0 else 1

unsafe def main : IO UInt32 := audit
