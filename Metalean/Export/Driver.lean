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

structure Lines where
  h : IO.FS.Handle
  buf : ByteArray := ∅
  pos : Nat := 0
  eof : Bool := false

def chunkSize : USize := 1048576

partial def newlineFrom (b : ByteArray) (i : Nat) : Option Nat :=
  if h : i < b.size then
    if b[i] == 10 then some i else newlineFrom b (i + 1)
  else none

partial def trimEnd (b : ByteArray) (s e : Nat) : Nat :=
  if s < e then
    let c := b[e - 1]!
    if c == 32 || c == 9 || c == 13 then trimEnd b s (e - 1) else e
  else e

partial def Lines.next (r : Lines) : IO (Option (ByteArray × Lines)) := do
  match newlineFrom r.buf r.pos with
  | some j => return some (r.buf.extract r.pos (trimEnd r.buf r.pos j), { r with pos := j + 1 })
  | none =>
    if r.eof then
      if r.pos < r.buf.size then
        return some (r.buf.extract r.pos (trimEnd r.buf r.pos r.buf.size), { r with pos := r.buf.size })
      return none
    let chunk ← r.h.read chunkSize
    Lines.next { r with buf := r.buf.extract r.pos r.buf.size ++ chunk, pos := 0, eof := chunk.isEmpty }

inductive Parsed where
  | decl (lineNo : Nat) (d : Decl)
  | error (lineNo : Nat)

partial def produce (r : Lines) (ch : Std.CloseableChannel.Sync Parsed) (stop : IO.Ref Bool)
    (lastUse : Array UInt32) (tables : Tables) (lineNo : Nat) : IO Unit := do
  if ← stop.get then return
  let some (line, r) ← r.next | return
  let lineNo := lineNo + 1
  if line.isEmpty then return ← produce r ch stop lastUse tables lineNo
  match parseLine tables lastUse lineNo line with
  | .error _ =>
    ch.send (.error lineNo)
  | .ok (tables, none) => produce r ch stop lastUse tables lineNo
  | .ok (tables, some d) =>
    ch.send (.decl lineNo d)
    produce r ch stop lastUse tables lineNo

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
    try produce { h } ch stop lastUse {} 0 finally ch.close
  let r ← consume ch stop step trace init
  match ← IO.wait producer with
  | .ok () => pure r
  | .error e => throw e

partial def scanLoop {σ : Type} (r : Lines) (step : σ → List Lean.Name → σ)
    (tables : Tables) (lastUse : Array UInt32) (lineNo : Nat) (st : σ) :
    IO (Option (σ × Array UInt32)) := do
  let some (line, r) ← r.next | return some (st, lastUse)
  let lineNo := lineNo + 1
  if line.isEmpty then return ← scanLoop r step tables lastUse lineNo st
  let lastUse := noteRefs lastUse line lineNo
  match scanLine tables line with
  | .error _ => return none
  | .ok (tables, none) => scanLoop r step tables lastUse lineNo st
  | .ok (tables, some names) => scanLoop r step tables lastUse lineNo (step st names)

def scan {σ : Type} (h : IO.FS.Handle) (init : σ) (step : σ → List Lean.Name → σ) :
    IO (Option (σ × Array UInt32)) := do
  scanLoop { h } step {} #[] 0 init

structure Options where
  input : String
  lines : Bool := false

def open? (path : String) : IO (Option IO.FS.Handle) := do
  try pure (some (← IO.FS.Handle.mk path .read)) catch _ => pure none

def run {σ : Type} (opts : Options) (lastUse : Array UInt32) (init : σ)
    (step : σ → Decl → Except Failure σ) : IO UInt32 := do
  let some h ← open? opts.input | return 3
  match ← fold h lastUse init step opts.lines with
  | .ok _ => return 0
  | .error f =>
    println! "{repr f}"
    return f.exitCode

end Metalean.Export
