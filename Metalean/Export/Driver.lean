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

structure Options where
  input : System.FilePath
  verbose : Bool := false
  jobs : Nat := 8

structure LineFailure where
  line : Nat
  failure : Failure

abbrev DriverM := ExceptT LineFailure IO

def readSize : USize := 1048576

def trimEnd (b : ByteArray) (s e : Nat) : Nat :=
  if s < e then
    let c := b[e - 1]!
    if c == 32 || c == 9 || c == 13 then trimEnd b s (e - 1) else e
  else e
termination_by e - s

structure Line where
  number : Nat
  bytes : ByteArray

structure Lines where
  handle : IO.FS.Handle

instance : ForIn DriverM Lines Line where
  forIn lines init f := do
    let mut buf : ByteArray := ∅
    let mut start := 0
    let mut number := 0
    let mut b := init
    repeat
      match buf.findIdx? (· == 10) start with
      | some j =>
        number := number + 1
        let s := start
        let e := trimEnd buf s j
        start := j + 1
        if e == s then continue
        match ← f ⟨number, buf.extract s e⟩ b with
        | .done b' =>
          b := b'
          break
        | .yield b' => b := b'
      | none =>
        let chunk ← lines.handle.read readSize
        if chunk.isEmpty then
          let e := trimEnd buf start buf.size
          if start < e then b := (← f ⟨number + 1, buf.extract start e⟩ b).value
          break
        buf := buf.extract start buf.size ++ chunk
        start := 0
    return b

structure Scan where
  decls : Nat
  lastUse : Array UInt32

def progressEvery : Nat := 4096

def scan (lines : Lines) (verbose : Bool) : DriverM Scan := do
  let mut tables : Tables := {}
  let mut decls := 0
  let mut lastUse : Array UInt32 := #[]
  for line in lines do
    if verbose && line.number % progressEvery == 0 then
      IO.eprint s!"\rscanned {line.number} lines"
    lastUse := noteRefs lastUse line.bytes line.number
    match scanLine tables line.bytes with
    | .error _ => throw ⟨line.number, .reject .parse⟩
    | .ok (t, names) =>
      tables := t
      if names.isSome then decls := decls + 1
  if verbose then IO.eprintln s!"\rscanned {decls} declarations"
  return ⟨decls, lastUse⟩

structure Declaration where
  index : Nat
  line : Nat
  decl : Decl

def Declaration.check {α : Type} (d : Declaration) (act : EIO Failure α) : DriverM α := do
  match ← act.toBaseIO with
  | .ok a => pure a
  | .error f => throw ⟨d.line, f⟩

def produce (lines : Lines) (lastUse : Array UInt32)
    (channel : Std.CloseableChannel.Sync Declaration) : DriverM Unit := do
  let mut tables : Tables := {}
  let mut index := 0
  for line in lines do
    match parseLine tables lastUse line.number line.bytes with
    | .error _ => throw ⟨line.number, .reject .parse⟩
    | .ok (t, decl) =>
      tables := t
      if let some decl := decl then
        index := index + 1
        if (← (channel.send ⟨index, line.number, decl⟩).toBaseIO) matches .error .closed then break

def close (channel : Std.CloseableChannel.Sync Declaration) : IO Unit := do
  match ← channel.close.toBaseIO with
  | .ok () | .error .alreadyClosed => pure ()
  | .error e => throw (.userError s!"{e}")

def shutdown (channel : Std.CloseableChannel.Sync Declaration) : IO Unit := do
  close channel
  for _ in channel do
    pure ()

structure Pool where
  queue : Std.CloseableChannel.Sync (BaseIO Unit)

def Pool.start (workers : Nat) : BaseIO Pool := do
  let queue : Std.CloseableChannel.Sync (BaseIO Unit) ← Std.CloseableChannel.Sync.new (some workers)
  for _ in [0:workers] do
    discard <| IO.asTask (prio := .dedicated) do
      for job in queue do
        job
  pure ⟨queue⟩

def Pool.submit {α : Type} [Nonempty α] (p : Pool) (act : BaseIO α) :
    BaseIO (Task (Option α)) := do
  let promise ← IO.Promise.new
  discard (p.queue.send (do promise.resolve (← act))).toBaseIO
  pure promise.result?

def Pool.shutdown (p : Pool) : IO Unit := do
  match ← p.queue.close.toBaseIO with
  | .ok () | .error .alreadyClosed => pure ()
  | .error e => throw (.userError s!"{e}")
  for _ in p.queue do
    pure ()

structure Declarations where
  total : Nat
  verbose : Bool
  pool : Pool
  channel : Std.CloseableChannel.Sync Declaration

def millis (ns : Nat) : String :=
  let micros := toString (ns / 1000 % 1000)
  s!"{ns / 1000000}.{"".pushn '0' (3 - micros.length)}{micros}ms"

instance : ForIn DriverM Declarations Declaration where
  forIn ds init f := forIn ds.channel init f

def Declarations.log (ds : Declarations) (d : Declaration) (start : Nat) : IO Unit := do
  if ds.verbose then
    IO.eprint s!"{d.index}/{ds.total} {d.decl.name} {millis ((← IO.monoNanosNow) - start)}\n"

def pipeline (opts : Options) (check : Declarations → DriverM Unit) : DriverM Unit := do
  let handle ← IO.FS.Handle.mk opts.input .read
  let lines : Lines := ⟨handle⟩
  let s ← scan lines opts.verbose
  handle.rewind
  let channel ← Std.CloseableChannel.Sync.new (some 1024)
  let producer ← IO.asTask (prio := .dedicated) do
    try (produce lines s.lastUse channel).run finally close channel
  let pool ← Pool.start (max opts.jobs 1)
  let checked : Except LineFailure Unit ←
    (check ⟨s.decls, opts.verbose, pool, channel⟩ |>.run : IO _)
  pool.shutdown
  shutdown channel
  let parsed : Except LineFailure Unit ← (IO.ofExcept (← IO.wait producer) : IO _)
  match parsed, checked with
  | .ok (), .ok () => pure ()
  | .error p, .error c => throw (if c.line < p.line then c else p)
  | .error e, .ok () | .ok (), .error e => throw e

def run (opts : Options) (check : Declarations → DriverM Unit) : IO UInt32 := do
  try
    match ← (pipeline opts check).run with
    | .ok () => pure 0
    | .error ⟨line, f⟩ =>
      IO.eprintln s!"line {line}: {repr f}"
      IO.println (repr f)
      pure f.exitCode
  catch e =>
    IO.eprintln e
    pure 3

end Metalean.Export
