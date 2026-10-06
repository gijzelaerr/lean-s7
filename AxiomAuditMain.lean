import Lean
import LeanS7

open Lean

/-- Axioms a claimed theorem may depend on. Anything else (notably `sorryAx`) fails the audit. -/
def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Theorem names cited by the README and `docs/COMPLETENESS.md`; each must still exist. -/
def documentedTheorems : List Name :=
  [`LeanS7.Chunking.writeSlices_complete, `LeanS7.S7.decodeAreaRead_size,
   `LeanS7.coreProtocolAssurance,
   `LeanS7.Correlation.step_deliver_iff, `LeanS7.Correlation.scan_delivered,
   `LeanS7.Correlation.scan_tooManyStale, `LeanS7.Correlation.allocated_succ,
   `LeanS7.Correlation.allocated_injective_window,
   `LeanS7.Correlation.earlier_reply_not_delivered]

def isProjectModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `LeanS7
  | none => false

unsafe def audit : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanS7 }] {} 0
  let mut failures := 0
  let mut checked := 0
  for name in documentedTheorems do
    unless env.contains name do
      IO.eprintln s!"documented theorem missing: {name}"
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
  IO.println s!"axiom audit: {checked} theorems checked, {failures} failures"
  return if failures == 0 then 0 else 1

unsafe def main : IO UInt32 := audit
