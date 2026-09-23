/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

import Cli
import Metalean.Checker.Loader
import Metalean.FastChecker.Loader
import Metalean.Export.Driver

/-! # Main
This is the entry point, as the name suggests
-/

open Metalean
open Lean (Name)
open Cli

/-- Data structure to keep track of which prelude constants we have found -/
structure Scan where
  pos : Nat := 0
  found : Std.HashMap Name Nat := ∅

/-- Scan for these constants -/
def Scan.wanted : Std.HashSet Name :=
  {
    ``Nat,
    ``List,
    ``Char,
    ``Char.ofNat,
    ``String.ofList,
    ``Bool,
    ``Nat.pred,
    ``Nat.add,
    ``Nat.sub,
    ``Nat.mul,
    ``Nat.pow,
    ``Nat.beq,
    ``Nat.ble,
    ``Nat.div,
    ``Nat.mod,
    ``Nat.gcd,
    ``Nat.land,
    ``Nat.lor,
    ``Nat.xor,
    ``Nat.shiftLeft,
    ``Nat.shiftRight
    }

def Scan.step (sc : Scan) (names : List Name) : Scan := Id.run do
  have ⟨pos, found⟩ := sc
  let mut table := found
  for name in names do
    if name ∈ Scan.wanted && name ∉ table then
      table := table.insert name pos
  return ⟨pos + 1, table⟩

def Scan.at? (name : Name) (sc : Scan) : Nat :=
  sc.found.getD name sc.pos

def Scan.literals (sc : Scan) : FastChecker.Literals where
  nat := sc.at? ``Nat
  list := sc.at? ``List
  char := sc.at? ``Char
  charOfNat := sc.at? ``Char.ofNat
  stringOfList := sc.at? ``String.ofList
  bool := sc.at? ``Bool
  pred := sc.at? ``Nat.pred
  add := sc.at? ``Nat.add
  sub := sc.at? ``Nat.sub
  mul := sc.at? ``Nat.mul
  pow := sc.at? ``Nat.pow
  beq := sc.at? ``Nat.beq
  ble := sc.at? ``Nat.ble
  div := sc.at? ``Nat.div
  mod := sc.at? ``Nat.mod
  gcd := sc.at? ``Nat.gcd
  land := sc.at? ``Nat.land
  lor := sc.at? ``Nat.lor
  xor := sc.at? ``Nat.xor
  shiftLeft := sc.at? ``Nat.shiftLeft
  shiftRight := sc.at? ``Nat.shiftRight

def options (p : Parsed) : Export.Options where
  input := p.positionalArg! "input" |>.as! String
  lines := p.hasFlag "lines"

def runFast (p : Parsed) : IO UInt32 := do
  let opts := options p
  let some h ← Export.open? opts.input | return 3
  let some (sc, lastUse) ← Export.scan h ({} : Scan) Scan.step
    | return (Frontend.Failure.reject .parse).exitCode
  Export.run opts lastUse (FastChecker.FState.initial sc.literals) FastChecker.step

def runSlow (p : Parsed) : IO UInt32 := do
  let opts := options p
  let some h ← Export.open? opts.input | return 3
  let some (_, lastUse) ← Export.scan h () (fun st _ => st)
    | return (Frontend.Failure.reject .parse).exitCode
  Export.run opts lastUse Checker.State.initial Checker.step

def fastCmd : Cmd := `[Cli|
  fast VIA runFast;
  "Check a lean4export NDJSON file with the fast checker."

  FLAGS:
    lines; "Print the line number and name of each declaration as it is checked."

  ARGS:
    input : String; "The NDJSON export to check."
]

def slowCmd : Cmd := `[Cli|
  slow VIA runSlow;
  "Check a lean4export NDJSON file with the slow checker."

  FLAGS:
    lines; "Print the line number and name of each declaration as it is checked."

  ARGS:
    input : String; "The NDJSON export to check."
]

def metaleanCmd : Cmd := `[Cli|
  metalean NOOP; ["0.1.0"]
  "Verified typechecker"

  SUBCOMMANDS:
    fastCmd;
    slowCmd
]

public def main : List String → IO UInt32 :=
  metaleanCmd.validate
