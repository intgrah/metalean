import Metalean.Checker.Loader
import Metalean.Export.Driver

open Metalean Checker

def main (args : List String) : IO UInt32 := do
  let some h ← Export.open? args | return 3
  let some (_, lastUse) ← Export.scan h () (fun st _ => st)
    | return (Frontend.Failure.reject .parse).exitCode
  Export.run args lastUse State.initial step
