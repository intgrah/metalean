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
  jobs := p.flag? "jobs" |>.map (·.as! Nat) |>.getD 8

def runFast (p : Parsed) : IO UInt32 :=
  Export.run (options p) (discard ∘ Checker.Fast.check (p.hasFlag "lean-elim"))

def runSlow (p : Parsed) : IO UInt32 :=
  Export.run (options p) fun ds => do
    let mut st := Checker.Slow.State.initial (p.hasFlag "lean-elim")
    for d in ds do
      let start ← IO.monoNanosNow
      st ← d.check (.ofExcept (Checker.Slow.step st d.decl))
      ds.log d start

def fastCmd : Cmd := `[Cli|
  fast VIA runFast;
  "Check a lean4export NDJSON file with the fast checker."

  FLAGS:
    v, verbose; "Print scanning progress, then each declaration's number out of total, name and time
      taken to check it, as each check completes."
    "lean-elim"; "Use more conservative large elimination criteria implemented by Lean"
    j, jobs : Nat; "The number of worker threads checking declarations (default 8)."

  ARGS:
    input : String; "The NDJSON export to check."
]

def slowCmd : Cmd := `[Cli|
  slow VIA runSlow;
  "Check a lean4export NDJSON file with the slow checker."

  FLAGS:
    v, verbose; "Print scanning progress, then each declaration's number out of total, name and time
      taken to check it."
    "lean-elim"; "Use more conservative large elimination criteria implemented by Lean"

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
