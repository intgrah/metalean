/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Export.Basic
public import Metalean.Frontend.Failure
public import Std.Sync.Channel

@[expose] public section

namespace Metalean.Export

open Frontend (Failure)

def slowNanos : Nat := 100000000

def channelCapacity : Nat := 1024

inductive Parsed where
  | decl (lineNo : Nat) (d : Decl)
  | error (lineNo : Nat)

partial def produce (h : IO.FS.Handle) (ch : Std.CloseableChannel.Sync Parsed) (stop : IO.Ref Bool)
    (lastUse : Array UInt32) (tables : Tables) (lineNo : Nat) : IO Unit := do
  if ← stop.get then return
  let line ← h.getLine
  if line.isEmpty then return
  let lineNo := lineNo + 1
  let trimmed := line.trimAsciiEnd.toString
  if trimmed.isEmpty then return ← produce h ch stop lastUse tables lineNo
  match parseLine tables lastUse lineNo trimmed with
  | .error _ =>
    ch.send (.error lineNo)
  | .ok (tables, none) => produce h ch stop lastUse tables lineNo
  | .ok (tables, some d) =>
    ch.send (.decl lineNo d)
    produce h ch stop lastUse tables lineNo

partial def drain (ch : Std.CloseableChannel.Sync Parsed) : IO Unit := do
  match ← ch.recv with
  | none => return
  | some _ => drain ch

partial def consume {σ : Type} (ch : Std.CloseableChannel.Sync Parsed) (stop : IO.Ref Bool)
    (step : σ → Decl → Except Failure σ) (trace : Bool) (st : σ) : IO (Except Failure σ) := do
  match ← ch.recv with
  | none => return .ok st
  | some (.error lineNo) =>
    IO.eprintln s!"line {lineNo}: parse error"
    stop.set true
    drain ch
    return .error (.reject .parse)
  | some (.decl lineNo d) =>
    if trace then IO.eprintln s!"line {lineNo}: {d.name}"
    let start ← IO.monoNanosNow
    let name := d.name
    match step st d with
    | .error f =>
      IO.eprintln s!"line {lineNo}: {repr f}"
      stop.set true
      drain ch
      return .error f
    | .ok st =>
      let elapsed := (← IO.monoNanosNow) - start
      if elapsed > slowNanos then
        IO.eprintln s!"line {lineNo}: {name} took {elapsed / 1000000}ms"
      consume ch stop step trace st

def fold {σ : Type} (h : IO.FS.Handle) (lastUse : Array UInt32) (init : σ)
    (step : σ → Decl → Except Failure σ) (trace : Bool := false) :
    IO (Except Failure σ) := do
  let ch ← Std.CloseableChannel.Sync.new (some channelCapacity)
  let stop ← IO.mkRef false
  let producer ← IO.asTask (prio := .dedicated) do
    try produce h ch stop lastUse {} 0 finally ch.close
  let r ← consume ch stop step trace init
  match ← IO.wait producer with
  | .ok () => pure r
  | .error e => throw e

partial def scanLoop {σ : Type} (h : IO.FS.Handle) (step : σ → List Lean.Name → σ)
    (tables : IO.Ref Tables) (lastUse : IO.Ref (Array UInt32)) (lineNo : Nat) (st : σ) :
    IO (Option σ) := do
  let line ← h.getLine
  if line.isEmpty then return some st
  let lineNo := lineNo + 1
  let trimmed := line.trimAsciiEnd.toString
  if trimmed.isEmpty then return ← scanLoop h step tables lastUse lineNo st
  lastUse.modify fun a => noteRefs a trimmed.toUTF8 lineNo
  let parsed ← tables.modifyGet fun t =>
    match scanLine t trimmed with
    | .ok (t, names) => (some names, t)
    | .error _ => (none, {})
  match parsed with
  | none => return none
  | some none => scanLoop h step tables lastUse lineNo st
  | some (some names) => scanLoop h step tables lastUse lineNo (step st names)

def scan {σ : Type} (h : IO.FS.Handle) (init : σ) (step : σ → List Lean.Name → σ) :
    IO (Option (σ × Array UInt32)) := do
  let lastUse ← IO.mkRef (#[] : Array UInt32)
  match ← scanLoop h step (← IO.mkRef ({} : Tables)) lastUse 0 init with
  | none => return none
  | some st => return some (st, ← lastUse.get)

def open? (args : List String) : IO (Option IO.FS.Handle) := do
  let some path ← (match args with
      | [p] => pure (some p)
      | _ => IO.getEnv "IN")
    | return none
  try pure (some (← IO.FS.Handle.mk path .read)) catch _ => pure none

def run {σ : Type} (args : List String) (lastUse : Array UInt32) (init : σ)
    (step : σ → Decl → Except Failure σ) : IO UInt32 := do
  let some h ← open? args | return 3
  match ← fold h lastUse init step (← IO.getEnv "METALEAN_TRACE").isSome with
  | .ok _ => return 0
  | .error f =>
    println! "{repr f}"
    return f.exitCode

end Metalean.Export
