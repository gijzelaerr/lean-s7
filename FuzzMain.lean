import LeanS7.SessionFuzz

def main (args : List String) : IO Unit := do
  unless args.isEmpty do throw <| IO.userError "usage: lean-s7-fuzz (JSON fixture batches on stdin)"
  LeanS7.SessionFuzz.run
