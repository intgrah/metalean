/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

import Cli
import Metalean.Checker.Slow.Loader
import Metalean.Checker.Fast.Loader
import Metalean.Export.Driver

/-! # Main
This is the entry point, as the name suggests
-/

open Metalean
open Cli

def options (p : Parsed) : Export.Options where
  input := p.positionalArg! "input" |>.as! String
  verbose := p.hasFlag "verbose"

def runFast (p : Parsed) : IO UInt32 := do
  let opts := options p
  let some h ← Export.open? opts.input | return 3
  let lines ← if opts.verbose then Export.countLines h else pure 0
  let some h ← Export.open? opts.input | return 3
  let some (decls, lastUse) ← Export.scan h 0 (fun n _ => n + 1) opts.verbose lines
    | return (Frontend.Failure.reject .parse).exitCode
  Export.run opts lastUse decls Checker.Fast.FState.initial Checker.Fast.step

def runSlow (p : Parsed) : IO UInt32 := do
  let opts := options p
  let some h ← Export.open? opts.input | return 3
  let lines ← if opts.verbose then Export.countLines h else pure 0
  let some h ← Export.open? opts.input | return 3
  let some (decls, lastUse) ← Export.scan h 0 (fun n _ => n + 1) opts.verbose lines
    | return (Frontend.Failure.reject .parse).exitCode
  Export.run opts lastUse decls Checker.Slow.State.initial fun st d => Checker.Slow.step st d

def fastCmd : Cmd := `[Cli|
  fast VIA runFast;
  "Check a lean4export NDJSON file with the fast checker."

  FLAGS:
    verbose; "Print lines parsed out of total, then each declaration's number out of total, name
      and time taken to check it."

  ARGS:
    input : String; "The NDJSON export to check."
]

def slowCmd : Cmd := `[Cli|
  slow VIA runSlow;
  "Check a lean4export NDJSON file with the slow checker."

  FLAGS:
    verbose; "Print line numbers, declaration numbers, name and time taken."

  ARGS:
    input : String; "The NDJSON export to check."
]

def mainCmd : Cmd := `[Cli|
  metalean NOOP;
  "Verified typechecker"

  SUBCOMMANDS:
    fastCmd;
    slowCmd
]

public def main : List String → IO UInt32 :=
  mainCmd.validate
