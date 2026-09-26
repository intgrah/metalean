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
    (step : σ → Decl → EIO Failure σ) (verbose : Bool) (decls done : Nat) (st : σ) :
    IO (Except Failure σ) := do
  match ← ch.recv with
  | none => return .ok st
  | some (.error lineNo) =>
    IO.eprintln s!"line {lineNo}: parse error"
    stop.set true
    drain ch
    return .error (.reject .parse)
  | some (.decl lineNo d) =>
    let done := done + 1
    if verbose then IO.eprint s!"{done}/{decls} {d.name}"
    let start ← IO.monoNanosNow
    let elapsed : IO Unit := do
      if verbose then
        let ns := (← IO.monoNanosNow) - start
        let micros := toString (ns / 1000 % 1000)
        IO.eprintln s!" {ns / 1000000}.{"".pushn '0' (3 - micros.length)}{micros}ms"
    match ← (step st d).toBaseIO with
    | .error f =>
      elapsed
      IO.eprintln s!"line {lineNo}: {repr f}"
      stop.set true
      drain ch
      return .error f
    | .ok st =>
      elapsed
      consume ch stop step verbose decls done st

def fold {σ : Type} (h : IO.FS.Handle) (lastUse : Array UInt32) (decls : Nat) (init : σ)
    (step : σ → Decl → EIO Failure σ) (verbose : Bool := false) :
    IO (Except Failure σ) := do
  let ch ← Std.CloseableChannel.Sync.new (some channelCapacity)
  let stop ← IO.mkRef false
  let producer ← IO.asTask (prio := .dedicated) do
    try produce { h } ch stop lastUse {} 0 finally ch.close
  let r ← consume ch stop step verbose decls 0 init
  match ← IO.wait producer with
  | .ok () => pure r
  | .error e => throw e

/-- The number of lines in the file -/
partial def countLines (h : IO.FS.Handle) (n : Nat := 0) (last : UInt8 := 10) : IO Nat := do
  let chunk ← h.read chunkSize
  if chunk.isEmpty then return if last == 10 then n else n + 1
  countLines h (chunk.foldl (fun n b => if b == 10 then n + 1 else n) n) chunk[chunk.size - 1]!

def progressEvery : Nat := 4096

partial def scanLoop {σ : Type} (r : Lines) (step : σ → List Lean.Name → σ) (verbose : Bool)
    (lines : Nat) (tables : Tables) (lastUse : Array UInt32) (lineNo : Nat) (st : σ) :
    IO (Option (σ × Array UInt32)) := do
  let some (line, r) ← r.next | do
    if verbose then IO.eprintln s!"\rparsed {lineNo}/{lines}"
    return some (st, lastUse)
  let lineNo := lineNo + 1
  if verbose && lineNo % progressEvery == 0 then IO.eprint s!"\rparsing {lineNo}/{lines}"
  if line.isEmpty then return ← scanLoop r step verbose lines tables lastUse lineNo st
  let lastUse := noteRefs lastUse line lineNo
  match scanLine tables line with
  | .error _ => return none
  | .ok (tables, none) => scanLoop r step verbose lines tables lastUse lineNo st
  | .ok (tables, some names) => scanLoop r step verbose lines tables lastUse lineNo (step st names)

def scan {σ : Type} (h : IO.FS.Handle) (init : σ) (step : σ → List Lean.Name → σ)
    (verbose : Bool := false) (lines : Nat := 0) : IO (Option (σ × Array UInt32)) := do
  scanLoop { h } step verbose lines {} #[] 0 init

structure Options where
  input : String
  verbose : Bool := false

def open? (path : String) : IO (Option IO.FS.Handle) := do
  try pure (some (← IO.FS.Handle.mk path .read)) catch _ => pure none

def run {σ : Type} (opts : Options) (lastUse : Array UInt32) (decls : Nat) (init : σ)
    (step : σ → Decl → EIO Failure σ) : IO UInt32 := do
  let some h ← open? opts.input | return 3
  match ← fold h lastUse decls init step opts.verbose with
  | .ok _ => return 0
  | .error f =>
    println! "{repr f}"
    return f.exitCode

end Metalean.Export
