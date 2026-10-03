/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Check
public import Metalean.Checker.Fast.Acceleration.Verify
public import Metalean.Export.Driver

@[expose] public section

namespace Metalean.Checker.Fast

open Lean (Name)
open Frontend (Failure Table Binding)
open Export (Declaration Declarations DriverM)

abbrev Outcome (P : Prop) := Option (Except IO.Error (Except Failure (PLift P)))

structure Pending where
  line : Nat
  P : Prop
  task : Task (Outcome P)

inductive Justification (F : FEnv) (fe : FEntry) where
  | now (h : EntryWFSpec F fe)
  | later (line : Nat) (task : Task (Outcome (EntryWFSpec F fe)))

def Justification.enqueue {F : FEnv} {fe : FEntry} :
    Justification F fe → Array Pending → Array Pending
  | .now _, pending => pending
  | .later line task, pending => pending.push ⟨line, _, task⟩

theorem Justification.split {F : FEnv} {fe : FEntry} {pending : Array Pending} :
    (j : Justification F fe) →
    (∀ o ∈ j.enqueue pending, o.P) →
    (∀ o ∈ pending, o.P) ∧ EntryWFSpec F fe
  | .now h, hs => ⟨hs, h⟩
  | .later _ _, hs =>
    ⟨fun o ho => hs o (Array.mem_push_of_mem _ ho), hs _ (Array.mem_push_self ..)⟩

structure Addition (F : FEnv) where
  bindings : List (Name × Binding)
  definition : Option (Name × List Name × Export.Expr)
  entry : FEntry
  hint : Export.Hints
  hex : EntryWF F entry
  wf : Justification F entry

inductive Change (F : FEnv) where
  | bind (name : Name) (b : Binding)
  | add (a : Addition F)

structure FState where
  leanElim : Bool
  F : FEnv
  hints : PArray Export.Hints
  accel : Accel F
  table : Table
  definitions : Export.Definitions
  pending : Array Pending
  /-- Soundness of the typechecker -/
  denotes : (∀ o ∈ pending, o.P) → ∃ (ζ : Sigs) (E : Env ζ), EnvWF E ∧ FEnv.Denotes F E

def FState.initial (leanElim : Bool) : FState where
  leanElim
  F := ∅
  hints := ∅
  accel := {}
  table := ∅
  definitions := ∅
  pending := #[]
  denotes _ := ⟨.nil, .nil, .nil, .nil⟩

theorem FEnv.denotes_push {F : FEnv} {fe : FEntry}
    (hex : EntryWF F fe) (hwf : EntryWFSpec F fe) :
    (∃ (ζ : Sigs) (E : Env ζ), EnvWF E ∧ FEnv.Denotes F E) →
    ∃ (ζ : Sigs) (E : Env ζ), EnvWF E ∧ FEnv.Denotes (F.push fe) E
  | ⟨_, E, hE, hF⟩ =>
    have ⟨_, hden₀⟩ := hex (E := ⟨_, E⟩) hF
    have ⟨entry, hden, hwf'⟩ := hwf hF hE hden₀
    ⟨_, E.snoc entry, hE.snoc hwf', .snoc hF hden⟩

def FState.apply : (st : FState) → Change st.F → FState
  | ⟨leanElim, F, hints, accel, table, definitions, pending, denotes⟩, .bind name b =>
    ⟨leanElim, F, hints, accel, table.insert name b, definitions, pending, denotes⟩
  | ⟨leanElim, F, hints, accel, table, definitions, pending, denotes⟩,
    .add ⟨bindings, definition, fe, hint, hex, wf⟩ =>
    { leanElim
      F := F.push fe
      hints := hints.push hint
      accel := accel.push fe
      table := bindings.foldl (fun t (name, b) => t.insert name b) table
      definitions := match definition with
        | some (name, d) => definitions.insert name d
        | none => definitions
      pending := wf.enqueue pending
      denotes h :=
        have ⟨hs, hwf⟩ := wf.split h
        FEnv.denotes_push hex hwf (denotes hs) }

def later {F : FEnv} {fe : FEntry} (ds : Declarations) (d : Declaration)
    (check : EIO Failure (PLift (EntryWFSpec F fe))) : BaseIO (Justification F fe) := do
  let task ← ds.pool.submit do
    let start ← IO.monoNanosNow
    let r ← check.toBaseIO
    match ← (ds.log d start).toBaseIO with
    | .ok () => pure (.ok r)
    | .error e => pure (.error e)
  pure (.later d.line task)

def checkLevelParams (lps : List Name) : Except Failure Unit := do
  if lps.eraseDups.length != lps.length then
    throw (.reject .duplicateLevelParam)

def FState.checkFresh (st : FState) (names : List Name) : Except Failure Unit := do
  if names.eraseDups.length != names.length then throw (.reject .duplicateName)
  if names.any st.table.contains then throw (.reject .duplicateName)

def stepAxiom (st : FState) (ds : Declarations) (d : Declaration) (c : Export.ConstantDecl) :
    EIO Failure (Change st.F) := do
  checkLevelParams c.levelParams
  let ⟨ft, ht⟩ ← translateClosed st.leanElim st.F st.table c.levelParams st.hints st.accel c.type
  st.checkFresh [c.name]
  let wf ← later ds d (checkAxiom st.F st.hints st.accel c.levelParams.length ft).eval
  pure (.add ⟨[(c.name, .const st.F.size)], none, _, .opaque, EntryWF.axiom ht, wf⟩)

def stepDef (st : FState) (ds : Declarations) (d : Declaration) (c : Export.ConstantDecl)
    (value : Export.Expr) (hints : Export.Hints) : EIO Failure (Change st.F) := do
  checkLevelParams c.levelParams
  let (⟨ft, ht⟩, ⟨v, hv⟩) ←
    translateClosedPair st.leanElim st.F st.table c.levelParams st.hints st.accel c.type value
  st.checkFresh [c.name]
  let wf ← later ds d (checkDef st.F st.hints st.accel c.levelParams.length ft v).eval
  pure (.add ⟨[(c.name, .const st.F.size)], some (c.name, c.levelParams, value), _, hints,
    EntryWF.def ht hv, wf⟩)

def stepOpaque (st : FState) (ds : Declarations) (d : Declaration) (c : Export.ConstantDecl)
    (value : Export.Expr) : EIO Failure (Change st.F) := do
  checkLevelParams c.levelParams
  let (⟨ft, ht⟩, ⟨v, _⟩) ←
    translateClosedPair st.leanElim st.F st.table c.levelParams st.hints st.accel c.type value
  st.checkFresh [c.name]
  let wf ← later ds d (checkOpaque st.F st.hints st.accel c.levelParams.length ft v).eval
  pure (.add ⟨[(c.name, .const st.F.size)], none, _, .opaque, EntryWF.opaque ht, wf⟩)

def stepTheorem (st : FState) (ds : Declarations) (d : Declaration) (c : Export.ConstantDecl)
    (value : Export.Expr) : EIO Failure (Change st.F) := do
  checkLevelParams c.levelParams
  let (⟨ft, ht⟩, ⟨v, hv⟩) ←
    translateClosedPair st.leanElim st.F st.table c.levelParams st.hints st.accel c.type value
  st.checkFresh [c.name]
  let wf ← later ds d (checkTheorem st.F st.hints st.accel c.levelParams.length ft v).eval
  pure (.add ⟨[(c.name, .const st.F.size)], none, _, .opaque, EntryWF.def ht hv, wf⟩)

def stepQuot (st : FState) (c : Export.ConstantDecl) :
    Export.QuotKind → EIO Failure (Change st.F)
  | .type => do
    let some (.ind eqPos 0) := st.table.get? `Eq | throw (.reject .eqShape)
    st.checkFresh [c.name]
    let ⟨⟨hex⟩, ⟨hwf⟩⟩ ← checkQuot st.F eqPos
    pure (.add ⟨[(c.name, .quot st.F.size .type)], none, _, .opaque, hex, .now hwf⟩)
  | kind => do
    let some (.quot pos .type) := st.table.get? `Quot | throw (.reject .shape)
    st.checkFresh [c.name]
    pure (.bind c.name (.quot pos kind))

def stepInductive (st : FState) (ds : Declarations) (d : Declaration)
    (types : List Export.InductiveType) (ctors : List Export.Constructor) (recNames : List Name) :
    EIO Failure (Change st.F) := do
  let sortNames := types.map (·.name)
  let result ←
    tryCatch (analyzeBlock st.leanElim st.F st.table st.hints st.accel types ctors recNames st.definitions)
      fun
        | .reject (.unknownName n) =>
          if sortNames.contains n then throw (.reject .positivity)
          else throw (.reject (.unknownName n))
        | f => throw f
  let pos := st.F.size
  let mut bindings : List (Name × Binding) := []
  for (name, s) in result.sortNames.zipIdx do
    bindings := (Name.str name "rec", .recr pos s result.metaOrders) :: (name, .ind pos s) ::
      bindings
  for (names, s) in result.ctorNames.zipIdx do
    for (name, c) in names.zipIdx do
      let some order := result.metaOrders[s]?.bind (·[c]?) | throw .internal
      bindings := (name, .ctor pos s c order) :: bindings
  st.checkFresh (bindings.map (·.1))
  let levels ← (inferOrdLevels st.F st.hints st.accel result.ι result.pre).eval
  let I := result.pre.withLevels levels
  let ⟨hI⟩ ← FInductive.wf st.F result.ι I
  let wf ← later ds d (checkInductiveEntry st.F st.hints st.accel result.ι I).eval
  pure (.add ⟨bindings, none, _, .opaque, EntryWF.inductive hI, wf⟩)

def change (st : FState) (ds : Declarations) (d : Declaration) : EIO Failure (Change st.F) :=
  match d.decl with
  | .axiom c isUnsafe =>
    if isUnsafe then throw (.decline .unsafe) else stepAxiom st ds d c
  | .def c value safety hints =>
    if safety != .safe then throw (.decline .unsafe)
    else stepDef st ds d c value hints
  | .theorem c value => stepTheorem st ds d c value
  | .opaque c value isUnsafe =>
    if isUnsafe then throw (.decline .unsafe) else stepOpaque st ds d c value
  | .quot c kind => stepQuot st c kind
  | .inductive types ctors recNames => stepInductive st ds d types ctors recNames

def Pending.result (p : Pending) : DriverM (PLift p.P) := do
  match ← IO.wait p.task with
  | none => throwThe IO.Error (.userError s!"line {p.line}: check abandoned")
  | some (.error e) => throwThe IO.Error e
  | some (.ok (.error f)) => throw ⟨p.line, f⟩
  | some (.ok (.ok h)) => pure h

def settle (pending : Array Pending) (front : Nat) : DriverM Nat := do
  let mut front := front
  repeat
    let some p := pending[front]? | break
    unless ← IO.hasFinished p.task do break
    discard p.result
    front := front + 1
  return front

def awaitFrom (pending : Array Pending) (front : Nat) : DriverM Unit := do
  for p in pending[front:] do
    discard p.result

def check (leanElim : Bool) (ds : Declarations) :
    DriverM {F : FEnv // ∃ (ζ : Sigs) (E : Env ζ), EnvWF E ∧ FEnv.Denotes F E} :=
  tryFinally (m := DriverM) (do
    let mut st := FState.initial leanElim
    let mut front := 0
    for d in ds do
      match ← (change st ds d).toBaseIO with
      | .error f =>
        awaitFrom st.pending front
        throw ⟨d.line, f⟩
      | .ok c =>
        let start ← IO.monoNanosNow
        let logNow := c matches .bind ..
        st := st.apply c
        st := { st with accel := ← d.check (verifyAccel st.F st.hints st.table d.decl.name
          (st.F.size - 1) st.accel) }
        if logNow then ds.log d start
        front ← settle st.pending front
    let pending := st.pending
    let ⟨h⟩ ← pending.forallM (fun i hi => (pending[i]'hi).P) fun i hi => (pending[i]'hi).result
    pure ⟨st.F, st.denotes fun _ ho =>
      have ⟨i, hi, hio⟩ := Array.mem_iff_getElem.mp ho
      hio ▸ h i hi⟩)
    ds.pool.shutdown

end Metalean.Checker.Fast
