/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Check
public import Metalean.FastChecker.Acceleration.Verify

@[expose] public section

namespace Metalean.FastChecker

open Lean (Name)
open Frontend (Failure Table Binding)

structure FState (L : Literals) where
  F : FEnv := #[]
  hints : Array Export.Hints := #[]
  accel : Accel L F := {}
  table : Table := ∅
  definitions : Export.Definitions := ∅
  denotes : ∃ (ζ : Sigs) (E : Env ζ), (L.NatTrust E → E.Ordered) ∧ FEnv.Denotes L F E

def FState.initial (L : Literals) : FState L where
  denotes := ⟨.nil, .nil, fun _ => .nil, .nil⟩

variable {L : Literals}

def FState.extend (st : FState L) (bindings : List (Name × Binding))
    (definition : Option (Name × List Name × Export.Expr))
    (fe : FEntry) (hint : Export.Hints) (hex : EntryWF L st.F fe)
    (hwf : EntryWFSpec L st.F fe) : FState L :=
  have ⟨F, hints, accel, table, definitions, denotes⟩ := st
  { F := F.push fe
    hints := hints.push hint
    accel := accel.push fe
    table := bindings.foldl (fun t (name, b) => t.insert name b) table
    definitions := match definition with
      | some (name, d) => definitions.insert name d
      | none => definitions
    denotes :=
      have ⟨_, E, ho, hE⟩ := denotes
      have ⟨entry₀, hden₀⟩ := hex (E := ⟨_, E⟩) hE
      open Classical in
      if htr₀ : L.NatTrust E then
        have ⟨entry, hden, hwf'⟩ := hwf hE (ho htr₀) htr₀ hden₀
        ⟨_, E.snoc entry, fun _ => (ho htr₀).snoc hwf', .snoc hE hden⟩
      else
        ⟨_, E.snoc entry₀, fun htr => absurd (htr.restrict (.step .refl)) htr₀, .snoc hE hden₀⟩ }

def checkLevelParams (lps : List Name) : Except Failure Unit := do
  if lps.eraseDups.length != lps.length then
    throw (.reject .duplicateLevelParam)

def FState.checkFresh (st : FState L) (names : List Name) : Except Failure Unit := do
  if names.eraseDups.length != names.length then throw (.reject .duplicateName)
  if names.any st.table.contains then throw (.reject .duplicateName)

def stepAxiom (st : FState L) (c : Export.ConstantDecl) : Except Failure (FState L) := do
  checkLevelParams c.levelParams
  let ⟨ft, ht⟩ ← translateClosed st.F L st.table c.levelParams st.hints st.accel c.type
  st.checkFresh [c.name]
  let ⟨hwf⟩ ← (checkAxiom L st.F st.hints st.accel c.levelParams.length ft).eval
  let pos := st.F.size
  pure (st.extend [(c.name, .const pos)] none _ .opaque (EntryWF.axiom ht) hwf)

def stepDef (st : FState L) (c : Export.ConstantDecl) (value : Export.Expr)
    (hints : Export.Hints) : Except Failure (FState L) := do
  checkLevelParams c.levelParams
  let (⟨ft, ht⟩, ⟨v, hv⟩) ← translateClosedPair st.F L st.table c.levelParams st.hints st.accel c.type value
  st.checkFresh [c.name]
  let ⟨hwf⟩ ← (checkDef L st.F st.hints st.accel c.levelParams.length ft v).eval
  let pos := st.F.size
  pure (st.extend [(c.name, .const pos)] (some (c.name, c.levelParams, value)) _ hints
    (EntryWF.def ht hv) hwf)

def stepOpaque (st : FState L) (c : Export.ConstantDecl) (value : Export.Expr) :
    Except Failure (FState L) := do
  checkLevelParams c.levelParams
  let (⟨ft, ht⟩, ⟨v, _⟩) ← translateClosedPair st.F L st.table c.levelParams st.hints st.accel c.type value
  st.checkFresh [c.name]
  let ⟨hwf⟩ ← (checkOpaque L st.F st.hints st.accel c.levelParams.length ft v).eval
  let pos := st.F.size
  pure (st.extend [(c.name, .const pos)] none _ .opaque (EntryWF.opaque ht) hwf)

def stepTheorem (st : FState L) (c : Export.ConstantDecl) (value : Export.Expr) :
    Except Failure (FState L) := do
  checkLevelParams c.levelParams
  let (⟨ft, ht⟩, ⟨v, hv⟩) ← translateClosedPair st.F L st.table c.levelParams st.hints st.accel c.type value
  st.checkFresh [c.name]
  let ⟨hwf⟩ ← (checkTheorem L st.F st.hints st.accel c.levelParams.length ft v).eval
  let pos := st.F.size
  pure (st.extend [(c.name, .const pos)] none _ .opaque (EntryWF.def ht hv) hwf)

def stepQuot (st : FState L) (c : Export.ConstantDecl) :
    Export.QuotKind → Except Failure (FState L)
  | .type => do
    let some (.ind eqPos 0) := st.table.get? `Eq | throw (.reject .eqShape)
    st.checkFresh [c.name]
    let ⟨⟨hex⟩, ⟨hwf⟩⟩ ← checkQuot L st.F eqPos
    let pos := st.F.size
    pure (st.extend [(c.name, .quot pos .type)] none _ .opaque hex hwf)
  | kind => do
    let some (.quot pos .type) := st.table.get? `Quot | throw (.reject .shape)
    st.checkFresh [c.name]
    let ⟨F, hints, accel, table, definitions, denotes⟩ := st
    pure ⟨F, hints, accel, table.insert c.name (.quot pos kind), definitions, denotes⟩

def stepInductive (st : FState L) (types : List Export.InductiveType)
    (ctors : List Export.Constructor) (recNames : List Name) : Except Failure (FState L) := do
  let sortNames := types.map (·.name)
  let result ←
    match analyzeBlock st.F L st.table st.hints st.accel types ctors recNames st.definitions with
    | .error (.reject (.unknownName n)) =>
      if sortNames.contains n then throw (.reject .positivity)
      else throw (.reject (.unknownName n))
    | r => r
  let pos := st.F.size
  let mut bindings : List (Name × Binding) := []
  for (name, s) in result.sortNames.zipIdx do
    bindings := (Name.str name "rec", .recr pos s result.metaOrders) :: (name, .ind pos s) :: bindings
  for (names, s) in result.ctorNames.zipIdx do
    for (name, c) in names.zipIdx do
      let some order := result.metaOrders[s]?.bind (·[c]?) | throw .internal
      bindings := (name, .ctor pos s c order) :: bindings
  st.checkFresh (bindings.map (·.1))
  let levels ← (inferOrdLevels L st.F st.hints st.accel result.ι result.pre).eval
  let I := result.pre.withLevels levels
  let ⟨hI⟩ ← FInductive.wf L st.F result.ι I
  let ⟨hwf⟩ ← (checkInductiveEntry L st.F st.hints st.accel result.ι I).eval
  pure (st.extend bindings none _ .opaque (EntryWF.inductive hI) hwf)

def Literals.accelPoints (L : Literals) : List Nat :=
  [[L.nat, L.add], [L.nat, L.pred, L.sub], [L.nat, L.add, L.mul], [L.nat, L.add, L.mul, L.pow],
    [L.nat, L.bool, L.beq], [L.nat, L.bool, L.ble], [L.nat, L.div], [L.nat, L.mod],
    [L.nat, L.gcd], [L.nat, L.land], [L.nat, L.lor], [L.nat, L.xor],
    [L.nat, L.add, L.mul, L.shiftLeft], [L.nat, L.div, L.shiftRight]].map
    fun ps => ps.foldl max 0 + 1

def stepDecl (st : FState L) : Export.Decl → Except Failure (FState L)
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

def step (st : FState L) (d : Export.Decl) : Except Failure (FState L) := do
  let st ← stepDecl st d
  if L.accelPoints.contains st.F.size then
    pure { st with accel := verifyAccel L st.F st.hints st.accel }
  else
    pure st

end Metalean.FastChecker
