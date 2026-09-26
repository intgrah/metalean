/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Check
public import Metalean.Checker.Fast.Acceleration.Verify

@[expose] public section

namespace Metalean.Checker.Fast

open Lean (Name)
open Frontend (Failure Table Binding)

structure FState where
  F : FEnv := #[]
  hints : Array Export.Hints := #[]
  accel : Accel F := {}
  table : Table := ∅
  definitions : Export.Definitions := ∅
  /-- Soundness of the typechecker -/
  denotes : ∃ (ζ : Sigs) (E : Env ζ), EnvWF E ∧ FEnv.Denotes F E

def FState.initial : FState where
  denotes := ⟨.nil, .nil, .nil, .nil⟩

def FState.extend (st : FState) (bindings : List (Name × Binding))
    (definition : Option (Name × List Name × Export.Expr))
    (fe : FEntry) (hint : Export.Hints) (hex : EntryWF st.F fe)
    (hwf : EntryWFSpec st.F fe) : FState :=
  have ⟨F, hints, accel, table, definitions, denotes⟩ := st
  { F := F.push fe
    hints := hints.push hint
    accel := accel.push fe
    table := bindings.foldl (fun t (name, b) => t.insert name b) table
    definitions := match definition with
      | some (name, d) => definitions.insert name d
      | none => definitions
    denotes :=
      have ⟨_, E, hE, hF⟩ := denotes
      have ⟨_, hden₀⟩ := hex (E := ⟨_, E⟩) hF
      have ⟨entry, hden, hwf'⟩ := hwf hF hE hden₀
      ⟨_, E.snoc entry, hE.snoc hwf', .snoc hF hden⟩ }

def checkLevelParams (lps : List Name) : Except Failure Unit := do
  if lps.eraseDups.length != lps.length then
    throw (.reject .duplicateLevelParam)

def FState.checkFresh (st : FState) (names : List Name) : Except Failure Unit := do
  if names.eraseDups.length != names.length then throw (.reject .duplicateName)
  if names.any st.table.contains then throw (.reject .duplicateName)

def stepAxiom (st : FState) (c : Export.ConstantDecl) : EIO Failure FState := do
  checkLevelParams c.levelParams
  let ⟨ft, ht⟩ ← translateClosed st.F st.table c.levelParams st.hints st.accel c.type
  st.checkFresh [c.name]
  let ⟨hwf⟩ ← (checkAxiom st.F st.hints st.accel c.levelParams.length ft).eval
  let pos := st.F.size
  pure (st.extend [(c.name, .const pos)] none _ .opaque (EntryWF.axiom ht) hwf)

def stepDef (st : FState) (c : Export.ConstantDecl) (value : Export.Expr)
    (hints : Export.Hints) : EIO Failure FState := do
  checkLevelParams c.levelParams
  let (⟨ft, ht⟩, ⟨v, hv⟩) ←
    translateClosedPair st.F st.table c.levelParams st.hints st.accel c.type value
  st.checkFresh [c.name]
  let ⟨hwf⟩ ← (checkDef st.F st.hints st.accel c.levelParams.length ft v).eval
  let pos := st.F.size
  pure (st.extend [(c.name, .const pos)] (some (c.name, c.levelParams, value)) _ hints
    (EntryWF.def ht hv) hwf)

def stepOpaque (st : FState) (c : Export.ConstantDecl) (value : Export.Expr) :
    EIO Failure FState := do
  checkLevelParams c.levelParams
  let (⟨ft, ht⟩, ⟨v, _⟩) ←
    translateClosedPair st.F st.table c.levelParams st.hints st.accel c.type value
  st.checkFresh [c.name]
  let ⟨hwf⟩ ← (checkOpaque st.F st.hints st.accel c.levelParams.length ft v).eval
  let pos := st.F.size
  pure (st.extend [(c.name, .const pos)] none _ .opaque (EntryWF.opaque ht) hwf)

def stepTheorem (st : FState) (c : Export.ConstantDecl) (value : Export.Expr) :
    EIO Failure FState := do
  checkLevelParams c.levelParams
  let (⟨ft, ht⟩, ⟨v, hv⟩) ←
    translateClosedPair st.F st.table c.levelParams st.hints st.accel c.type value
  st.checkFresh [c.name]
  let ⟨hwf⟩ ← (checkTheorem st.F st.hints st.accel c.levelParams.length ft v).eval
  let pos := st.F.size
  pure (st.extend [(c.name, .const pos)] none _ .opaque (EntryWF.def ht hv) hwf)

def stepQuot (st : FState) (c : Export.ConstantDecl) :
    Export.QuotKind → EIO Failure FState
  | .type => do
    let some (.ind eqPos 0) := st.table.get? `Eq | throw (.reject .eqShape)
    st.checkFresh [c.name]
    let ⟨⟨hex⟩, ⟨hwf⟩⟩ ← checkQuot st.F eqPos
    let pos := st.F.size
    pure (st.extend [(c.name, .quot pos .type)] none _ .opaque hex hwf)
  | kind => do
    let some (.quot pos .type) := st.table.get? `Quot | throw (.reject .shape)
    st.checkFresh [c.name]
    pure { st with table := st.table.insert c.name (.quot pos kind) }

def stepInductive (st : FState) (types : List Export.InductiveType)
    (ctors : List Export.Constructor) (recNames : List Name) : EIO Failure FState := do
  let sortNames := types.map (·.name)
  let result ←
    tryCatch (analyzeBlock st.F st.table st.hints st.accel types ctors recNames st.definitions)
      fun
        | .reject (.unknownName n) =>
          if sortNames.contains n then throw (.reject .positivity)
          else throw (.reject (.unknownName n))
        | f => throw f
  let pos := st.F.size
  let mut bindings : List (Name × Binding) := []
  for (name, s) in result.sortNames.zipIdx do
    bindings := (Name.str name "rec", .recr pos s result.metaOrders) :: (name, .ind pos s) :: bindings
  for (names, s) in result.ctorNames.zipIdx do
    for (name, c) in names.zipIdx do
      let some order := result.metaOrders[s]?.bind (·[c]?) | throw .internal
      bindings := (name, .ctor pos s c order) :: bindings
  st.checkFresh (bindings.map (·.1))
  let levels ← (inferOrdLevels st.F st.hints st.accel result.ι result.pre).eval
  let I := result.pre.withLevels levels
  let ⟨hI⟩ ← FInductive.wf st.F result.ι I
  let ⟨hwf⟩ ← (checkInductiveEntry st.F st.hints st.accel result.ι I).eval
  pure (st.extend bindings none _ .opaque (EntryWF.inductive hI) hwf)

def stepDecl (st : FState) : Export.Decl → EIO Failure FState
  | .axiom c isUnsafe =>
    if isUnsafe then throw (.decline .unsafe) else stepAxiom st c
  | .def c value safety hints =>
    if safety != .safe then throw (.decline .unsafe)
    else stepDef st c value hints
  | .theorem c value => stepTheorem st c value
  | .opaque c value isUnsafe =>
    if isUnsafe then throw (.decline .unsafe) else stepOpaque st c value
  | .quot c kind => stepQuot st c kind
  | .inductive types ctors recNames => stepInductive st types ctors recNames

def step (st : FState) (d : Export.Decl) : EIO Failure FState := do
  let st ← stepDecl st d
  let accel ← verifyAccel st.F st.hints st.table d.name (st.F.size - 1) st.accel
  pure { st with accel }

end Metalean.Checker.Fast
