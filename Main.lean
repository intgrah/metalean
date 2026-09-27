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

def runFast (p : Parsed) : IO UInt32 :=
  Export.run (options p) fun ds => do
    let mut st := Checker.Fast.FState.initial
    for d in ds do
      st ← d.check (Checker.Fast.step st d.decl)

def runSlow (p : Parsed) : IO UInt32 :=
  Export.run (options p) fun ds => do
    let mut st := Checker.Slow.State.initial
    for d in ds do
      st ← d.check (.ofExcept (Checker.Slow.step st d.decl))

def fastCmd : Cmd := `[Cli|
  fast VIA runFast;
  "Check a lean4export NDJSON file with the fast checker."

  FLAGS:
    verbose; "Print scanning progress, then each declaration's number out of total, name and time
      taken to check it."

  ARGS:
    input : String; "The NDJSON export to check."
]

def slowCmd : Cmd := `[Cli|
  slow VIA runSlow;
  "Check a lean4export NDJSON file with the slow checker."

  FLAGS:
    verbose; "Print scanning progress, then each declaration's number out of total, name and time
      taken to check it."

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
