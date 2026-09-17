/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Inductive
public import Metalean.Checker.Projection
public import Metalean.Frontend.Inductive

@[expose] public section

namespace Metalean.Checker

open Lean (Name)
open Frontend

structure State where
  {ζ : Sigs}
  env : Env ζ
  ordered : env.Ordered
  table : Table := ∅
  definitions : Export.Definitions := ∅

def State.initial : State where
  env := .nil
  ordered := .nil

def checkLevelParams (lps : List Name) : Except Failure Unit := do
  if lps.eraseDups.length != lps.length then
    throw (.reject .duplicateLevelParam)

def bind (st : State) (name : Name) (b : Binding) : Except Failure Table := do
  if st.table.contains name then
    throw (.reject .duplicateName)
  else
    pure (st.table.insert name b)

def extend (st : State) {sig : Sig} (entry : Entry st.ζ sig)
    (hwf : Entry.WF st.env entry) : State where
  ζ := st.ζ.snoc sig
  env := st.env.snoc entry
  ordered := st.ordered.snoc hwf
  table := st.table
  definitions := st.definitions

def translateClosed (st : State) (lps : List Name) (e : Export.Expr) :
    Except Failure (Expr st.ζ lps.length 0) :=
  translate st.env st.table lps (project st.env st.table) .nil Scope.empty e

def stepAxiom (st : State) (c : Export.ConstantDecl) : Except Failure State := do
  checkLevelParams c.levelParams
  let t ← translateClosed st c.levelParams c.type
  let table ← bind st c.name (.const st.ζ.length)
  let ⟨hwf⟩ ← checkAxiom st.ordered t
  pure (extend { st with table } (.axiom t) hwf)

def stepDef (st : State) (c : Export.ConstantDecl) (value : Export.Expr) :
    Except Failure State := do
  checkLevelParams c.levelParams
  let t ← translateClosed st c.levelParams c.type
  let e ← translateClosed st c.levelParams value
  let table ← bind st c.name (.const st.ζ.length)
  let ⟨hwf⟩ ← checkDef st.ordered t e
  let definitions := st.definitions.insert c.name (c.levelParams, value)
  pure (extend { st with table, definitions } (.def t e) hwf)

def stepOpaque (st : State) (c : Export.ConstantDecl) (value : Export.Expr) :
    Except Failure State := do
  checkLevelParams c.levelParams
  let t ← translateClosed st c.levelParams c.type
  let e ← translateClosed st c.levelParams value
  let table ← bind st c.name (.const st.ζ.length)
  let ⟨hwf⟩ ← checkOpaque st.ordered t e
  pure (extend { st with table } (.opaque t) hwf)

def stepQuot (st : State) (c : Export.ConstantDecl) : Export.QuotKind → Except Failure State
  | .type => do
    let some (.ind pos 0) := st.table.get? `Eq | throw (.reject .eqShape)
    let some ⟨.inductive ι, η⟩ := st.ζ.lookup pos | throw (.reject .eqShape)
    if hsig : ι = Eq.sig then
      let eqHead : Head st.ζ (.inductive Eq.sig) := hsig ▸ η
      let ⟨hblock⟩ ← tryCatch (Inductive.decEq? (st.env.get eqHead).block Eq.block)
        fun _ => throw (.reject .eqShape)
      let table ← bind st c.name (.quot st.ζ.length .type)
      pure (extend { st with table } (.quot eqHead) (.quot hblock))
    else throw (.reject .eqShape)
  | kind => do
    let some (.quot pos .type) := st.table.get? `Quot | throw (.reject .shape)
    let table ← bind st c.name (.quot pos kind)
    pure { st with table }

def stepInductive (st : State) (types : List Export.InductiveType)
    (ctors : List Export.Constructor) (recNames : List Name) : Except Failure State := do
  let sortNames := types.map (·.name)
  let result ←
    match analyzeBlock st.env st.table (project st.env st.table) types ctors recNames
      st.definitions with
    | .error (.reject (.unknownName n)) =>
      if sortNames.contains n then throw (.reject .positivity)
      else throw (.reject (.unknownName n))
    | r => r
  let pos := st.ζ.length
  let mut table := st.table
  for (name, s) in result.sortNames.zipIdx do
    if table.contains name then throw (.reject .duplicateName)
    table := table.insert name (.ind pos s)
    if table.contains (Name.str name "rec") then throw (.reject .duplicateName)
    table := table.insert (Name.str name "rec") (.recr pos s result.metaOrders)
  for (names, s) in result.ctorNames.zipIdx do
    for (name, c) in names.zipIdx do
      let some order := result.metaOrders[s]?.bind (·[c]?) | throw .internal
      if table.contains name then throw (.reject .duplicateName)
      table := table.insert name (.ctor pos s c order)
  let ⟨levels, ⟨hwf⟩⟩ ← checkPreInductive st.ordered result.pre
  pure (extend { st with table } (.inductive (result.pre.withLevels levels)) hwf)

def stepTheorem (st : State) (c : Export.ConstantDecl) (value : Export.Expr) :
    Except Failure State := do
  checkLevelParams c.levelParams
  unless ← isProp st.ordered (← translateClosed st c.levelParams c.type) do
    throw (.reject .nonPropTheorem)
  stepOpaque st c value

def step (st : State) : Export.Decl → Except Failure State
  | .axiom c isUnsafe =>
    if isUnsafe then throw (.decline .unsafe) else stepAxiom st c
  | .def c value safety _ =>
    if safety != .safe then throw (.decline .unsafe)
    else stepDef st c value
  | .theorem c value => stepTheorem st c value
  | .opaque c value isUnsafe =>
    if isUnsafe then throw (.decline .unsafe) else stepOpaque st c value
  | .quot c kind => stepQuot st c kind
  | .inductive types ctors recNames => stepInductive st types ctors recNames

end Metalean.Checker
