/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Slow.Inductive
public import Metalean.Checker.Slow.Projection
public import Metalean.Frontend.Inductive

@[expose] public section

namespace Metalean.Checker.Slow

open Lean (Name)
open Frontend

structure State where
  leanElim : Bool
  {ζ : Sigs}
  env : Env ζ
  wf : EnvWF env
  table : Table := ∅
  definitions : Export.Definitions := ∅

def State.initial (leanElim : Bool) : State where
  leanElim
  env := .nil
  wf := .nil

def checkLevelParams (lps : List Name) : Except Failure Unit := do
  if lps.eraseDups.length != lps.length then
    throw (.reject .duplicateLevelParam)

def bind (st : State) (name : Name) (b : Binding) : Except Failure Table := do
  if st.table.contains name then
    throw (.reject .duplicateName)
  else
    pure (st.table.insert name b)

def extend (st : State) {sig : Sig} (entry : Entry st.ζ sig)
    (hwf : EntryWF st.env entry) : State where
  leanElim := st.leanElim
  ζ := st.ζ.snoc sig
  env := st.env.snoc entry
  wf := st.wf.snoc hwf
  table := st.table
  definitions := st.definitions

def translateClosed (st : State) (lps : List Name) (e : Export.Expr) :
    Except Failure (Expr st.ζ lps.length 0) :=
  translate st.leanElim st.env st.table lps (project st.env st.table) .nil Scope.empty e

def stepConst (st : State) (c : Export.ConstantDecl) {kind : ConstKind}
    (check : Expr st.ζ c.levelParams.length 0 → Except Failure
      ((entry : Entry st.ζ (.const kind c.levelParams.length)) ×' PLift (EntryWF st.env entry))) :
    Except Failure State := do
  checkLevelParams c.levelParams
  let t ← translateClosed st c.levelParams c.type
  let table ← bind st c.name (.const st.ζ.length)
  let ⟨entry, ⟨hwf⟩⟩ ← check t
  pure (extend { st with table } entry hwf)

def stepOpaque (st : State) (c : Export.ConstantDecl) (value : Export.Expr)
    (requireProp : Bool) : Except Failure State :=
  stepConst st c fun t => do
    let e ← translateClosed st c.levelParams value
    let ⟨l, ht⟩ ← checkIsType st.wf .nil t
    if requireProp ∧ l ≠ .zero then throw (.reject .nonPropTheorem)
    let ⟨he⟩ ← checkAgainst st.wf .nil e t ⟨l, ht⟩
    pure ⟨.opaque t, ⟨.opaque he ⟨l, ht⟩⟩⟩

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
    match analyzeBlock st.leanElim st.env st.table (project st.env st.table) types ctors recNames
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
  let ⟨levels, ⟨hwf⟩⟩ ← checkPreInductive st.wf result.pre
  pure (extend { st with table } (.inductive (result.pre.withLevels levels)) hwf)

def step (st : State) : Export.Decl → Except Failure State
  | .axiom c false => stepConst st c fun t => do
    let ⟨l, ht⟩ ← checkIsType st.wf .nil t
    pure ⟨.axiom t, ⟨.axiom ⟨l, ht⟩⟩⟩
  | .def c value .safe _ => do
    let next ← stepConst st c fun t => do
      let e ← translateClosed st c.levelParams value
      let ⟨l, ht⟩ ← checkIsType st.wf .nil t
      let ⟨he⟩ ← checkAgainst st.wf .nil e t ⟨l, ht⟩
      pure ⟨.def t e, ⟨.def ⟨l, ht⟩ he⟩⟩
    pure { next with definitions := st.definitions.insert c.name (c.levelParams, value) }
  | .theorem c value => stepOpaque st c value true
  | .opaque c value false => stepOpaque st c value false
  | .quot c kind => stepQuot st c kind
  | .inductive types ctors recNames => stepInductive st types ctors recNames
  | .axiom .. | .def .. | .opaque .. => throw (.decline .unsafe)

end Metalean.Checker.Slow
