/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Pre
public import Metalean.Frontend.Translate

@[expose] public section

universe u

namespace Metalean.Frontend

open Lean (Name)

variable {ζ : Sigs} {nsorts : Nat}

def tupleOf {α : Type u} (k : Nat) (xs : List α) : Except Failure (Fin k → α) :=
  if h : xs.length = k then pure fun i => xs[i.val]'(by omega) else throw (.reject .arity)

def spineOf : Export.Expr → Export.Expr × List Export.Expr
  | .app fn arg =>
    let (head, args) := spineOf fn
    (head, args ++ [arg])
  | e => (e, [])

def peelForalls : Export.Expr → List Export.Expr × Export.Expr
  | .forallE type body =>
    let (binders, rest) := peelForalls body
    (type :: binders, rest)
  | e => ([], e)

def takeForallsRev : Nat → Export.Expr → Except Failure (List Export.Expr × Export.Expr)
  | 0, e => pure ([], e)
  | k + 1, .forallE type body => do
    let (binders, rest) ← takeForallsRev k body
    pure (binders ++ [type], rest)
  | _, _ => throw (.reject .arity)

def takeForallsRevWhnf (defs : Export.Definitions) :
    Nat → Export.Expr → Except Failure (List Export.Expr × Export.Expr)
  | 0, e => pure ([], Export.whnf defs e)
  | k + 1, e => do
    let .forallE type body := Export.whnf defs e | throw (.reject .arity)
    let (binders, rest) ← takeForallsRevWhnf defs k body
    pure (binders ++ [type], rest)

partial def peelFieldForalls (defs : Export.Definitions) (e : Export.Expr) :
    List Export.Expr × Export.Expr :=
  match Export.whnf defs e with
  | .forallE type body =>
    let (binders, rest) := peelFieldForalls defs body
    (type :: binders, rest)
  | e => ([], e)

def paramArgsOk (nparams offset : Nat) (args : List Export.Expr) : Bool :=
  (List.range nparams).all fun p => args[p]? == some (.bvar (nparams + offset - 1 - p))

def levelArgsOk (lps : List Name) (us : List Export.Level) : Bool :=
  us == lps.map Export.Level.param

structure OrdField where
  leanPos : Nat
  type : Export.Expr

structure RecField (nsorts : Nat) where
  leanPos : Nat
  bindersRev : List Export.Expr
  target : Fin nsorts
  indices : List Export.Expr

structure CtorShape (nsorts : Nat) where
  ords : List OrdField
  recs : List (RecField nsorts)
  resultIndices : List Export.Expr

def CtorShape.toSig (shape : CtorShape nsorts) : CtorSig nsorts where
  nfields := shape.ords.length
  nrecFields := shape.recs.length
  recursiveArity r := (shape.recs[r.val]'r.isLt).bindersRev.length
  recursiveTarget r := (shape.recs[r.val]'r.isLt).target

def mentionsSort (sortIdx? : Name → Option (Fin nsorts)) : Export.Expr → Bool
  | .bvar _ | .sort _ | .natLit _ | .stringLit _ => false
  | .const name _ => (sortIdx? name).isSome
  | .app fn arg => mentionsSort sortIdx? fn || mentionsSort sortIdx? arg
  | .lam type body | .forallE type body =>
    mentionsSort sortIdx? type || mentionsSort sortIdx? body
  | .letE type value body =>
    mentionsSort sortIdx? type || mentionsSort sortIdx? value || mentionsSort sortIdx? body
  | .proj _ _ struct => mentionsSort sortIdx? struct

def classifyField (defs : Export.Definitions) (sortIdx? : Name → Option (Fin nsorts)) (lps : List Name)
    (nparams leanPos : Nat) (type : Export.Expr) :
    Except Failure (List OrdField × List (RecField nsorts)) := do
  let (binders, codomain) := peelFieldForalls defs type
  if binders.any (mentionsSort sortIdx?) then throw (.reject .positivity)
  let ordinary : Except Failure (List OrdField × List (RecField nsorts)) :=
    if mentionsSort sortIdx? codomain then throw (.decline .unreducedOccurrence)
    else pure ([{ leanPos, type }], [])
  let (head, args) := spineOf codomain
  match head with
  | .const name us =>
    match sortIdx? name with
    | some target =>
      let indices := args.drop nparams
      if !levelArgsOk lps us then throw (.reject .positivity)
      else if !paramArgsOk nparams (leanPos + binders.length) args then throw (.reject .positivity)
      else if indices.any (mentionsSort sortIdx?) then throw (.reject .positivity)
      else pure ([], [{ leanPos, bindersRev := binders.reverse, target, indices }])
    | none => ordinary
  | _ => ordinary

def shapeCtor (defs : Export.Definitions) (sortIdx? : Name → Option (Fin nsorts)) (lps : List Name)
    (nparams nindices : Nat) (s : Fin nsorts) (ctorType : Export.Expr) :
    Except Failure (CtorShape nsorts) := do
  let (_, rest) ← takeForallsRev nparams ctorType
  let (fieldTypes, codomain) := peelForalls rest
  let (ords, recs) ← fieldTypes.zipIdx.foldlM (fun (ords₁, recs₁) (type, leanPos) => do
    let (ords₂, recs₂) ← classifyField defs sortIdx? lps nparams leanPos type
    pure (ords₁ ++ ords₂, recs₁ ++ recs₂)) ([], [])
  let (head, args) := spineOf codomain
  match head with
  | .const name us =>
    if sortIdx? name != some s then throw (.reject .shape)
    else if !levelArgsOk lps us then throw (.reject .shape)
    else if !paramArgsOk nparams fieldTypes.length args then throw (.reject .shape)
    else if args.length != nparams + nindices then throw (.reject .arity)
    else pure { ords, recs, resultIndices := args.drop nparams }
  | _ => throw (.reject .shape)

def metaOrderOf (shape : CtorShape nsorts) : List Nat :=
  shape.ords.map (·.leanPos) ++ shape.recs.map (·.leanPos)

def fieldScope (ords : List OrdField) (nparams leanPos target : Nat) : Scope target :=
  fun k =>
    if k < leanPos then
      let q := leanPos - 1 - k
      match ords.findFinIdx? fun field => field.leanPos == q with
      | some o =>
        if h : nparams + o.val < target then some ⟨nparams + o.val, h⟩ else none
      | none => none
    else
      let p := k - leanPos
      if h : p < nparams ∧ nparams ≤ target then some ⟨nparams - 1 - p, by omega⟩ else none

structure SortData (nsorts : Nat) where
  indicesRev : List Export.Expr
  level : Export.Level
  shapes : List (CtorShape nsorts)

def indSigOf (nlevels nparams nsorts : Nat) (sd : Fin nsorts → SortData nsorts) : IndSig where
  nlevels := nlevels
  nparams := nparams
  nsorts := nsorts
  nindices s := (sd s).indicesRev.length
  nctors s := (sd s).shapes.length
  ctors s c := ((sd s).shapes[c.val]'c.isLt).toSig

structure BlockResult (ζ : Sigs) where
  ι : IndSig
  pre : PreInductive ζ ι
  sortNames : List Name
  ctorNames : List (List Name)
  metaOrders : List (List (List Nat))

variable (E : Env ζ) (table : Table) (lps : List Name) (project : Projector ζ)

def buildClosed : (rev : List Export.Expr) → Except Failure (Ctx ζ lps.length 0 rev.length)
  | [] => pure #t[]
  | t :: rest => do
    let Γ ← buildClosed rest
    let t' ← translate E table lps project Γ (Scope.id rest.length) t
    pure (Γ.snoc t')

def buildFrom {m : Nat} (base : Ctx ζ lps.length 0 m) (ρ : Scope m) :
    (rev : List Export.Expr) → Except Failure (Ctx ζ lps.length m (m + rev.length))
  | [] => pure #t[]
  | t :: rest => do
    let Γ ← buildFrom base ρ rest
    let t' ← translate E table lps project (base ++ Γ) (ρ.pushN rest.length) t
    pure (Γ.snoc t')

def preRecField (nparams : Nat) (sd : Fin nsorts → SortData nsorts) (ords : List OrdField)
    (nfields : Nat) (Γ : Ctx ζ lps.length 0 (nparams + nfields)) (rf : RecField nsorts) :
    Except Failure (Metalean.RecField ζ (indSigOf lps.length nparams nsorts sd) nfields
      rf.bindersRev.length rf.target) := do
  let ρ := fieldScope ords nparams rf.leanPos (nparams + nfields)
  let telescope ← buildFrom E table lps project Γ ρ rf.bindersRev
  let is ← rf.indices.mapM (translate E table lps project (Γ ++ telescope) (ρ.pushN rf.bindersRev.length))
  pure ⟨telescope, ← tupleOf (sd rf.target).indicesRev.length is⟩

def ordinaryFields (nparams : Nat) (params : Ctx ζ lps.length 0 nparams)
    (shape : CtorShape nsorts) :
    (count : Nat) → count ≤ shape.ords.length →
      Except Failure (Ctx ζ lps.length nparams (nparams + count))
  | 0 => fun _ => pure .nil
  | count + 1 => fun h => do
    let Δ ← ordinaryFields nparams params shape count (by omega)
    let field := shape.ords[count]'(by omega)
    let t ← translate E table lps project (params ++ Δ)
      (fieldScope shape.ords nparams field.leanPos (nparams + count)) field.type
    pure (Δ.snoc t)

def preCtorOf (nparams : Nat) (params : Ctx ζ lps.length 0 nparams)
    (sd : Fin nsorts → SortData nsorts) (s : Fin nsorts)
    (shape : CtorShape nsorts) :
    Except Failure (PreCtorDecl ζ (indSigOf lps.length nparams nsorts sd) s shape.toSig) := do
  let fields ← ordinaryFields E table lps project nparams params shape shape.ords.length le_rfl
  let ordinary := fun f : Fin shape.ords.length =>
    fields.entry (p := nparams + f.val) (by omega) (by omega)
  let recursive : (r : Fin shape.recs.length) →
      Metalean.RecField ζ (indSigOf lps.length nparams nsorts sd) shape.ords.length
        (shape.recs[r.val]'r.isLt).bindersRev.length
        (shape.recs[r.val]'r.isLt).target ←
    Fin.mapM fun r =>
      preRecField E table lps project nparams sd shape.ords shape.ords.length (params ++ fields)
        (shape.recs[r.val]'r.isLt)
  let tis ← shape.resultIndices.mapM (translate E table lps project (params ++ fields)
    (fieldScope shape.ords nparams (shape.ords.length + shape.recs.length) (nparams + shape.ords.length)))
  let targetIndices ← tupleOf (sd s).indicesRev.length tis
  pure { ordinary, recursive, targetIndices }

def analyzeBlock (E : Env ζ) (table : Table) (project : Projector ζ) (types : List Export.InductiveType)
    (ctors : List Export.Constructor) (recNames : List Name) (defs : Export.Definitions := ∅) :
    Except Failure (BlockResult ζ) := do
  if hpos : 0 < types.length then
    let first := types[0]
    if types.any (·.isUnsafe) then throw (.decline .unsafe)
    if types.any (·.numNested != 0) then throw (.decline .nested)
    if recNames.length != types.length then throw (.reject .arity)
    let lps := first.levelParams
    if lps.eraseDups.length != lps.length then throw (.reject .duplicateLevelParam)
    if types.any (·.levelParams != lps) then throw (.reject .shape)
    if ctors.any (·.levelParams != lps) then throw (.reject .shape)
    if types.any (·.numParams != first.numParams) then throw (.reject .arity)
    let allCtorNames := types.flatMap (·.ctors)
    if ctors.length != allCtorNames.length then throw (.reject .shape)
    if allCtorNames.any fun cname => (ctors.find? (·.name == cname)).isNone then
      throw (.reject .shape)
    let sortIdx? : Name → Option (Fin types.length) := fun nm =>
      types.findFinIdx? (·.name == nm)
    let (paramBindersRev, _) ← takeForallsRevWhnf defs first.numParams first.type
    let sd ← Fin.mapM fun s : Fin types.length => do
      let ty := types[s.val]
      let (_, rest) ← takeForallsRevWhnf defs first.numParams ty.type
      let (indicesRev, .sort level) ← takeForallsRevWhnf defs ty.numIndices rest
        | throw (.reject .shape)
      let shapes ← ty.ctors.mapM fun cname => do
        let some c := ctors.find? (·.name == cname) | throw (.reject .shape)
        shapeCtor defs sortIdx? lps paramBindersRev.length ty.numIndices s c.type
      pure ({ indicesRev, level, shapes } : SortData types.length)
    let levels ← Fin.mapM fun s : Fin types.length => translateLevel lps (sd s).level
    let level := levels ⟨0, hpos⟩
    if ∃ s, levels s ≠ level then throw (.reject .shape)
    let params ← buildClosed E table lps project paramBindersRev
    let indices ← Fin.mapM fun s : Fin types.length =>
      buildFrom E table lps project params (Scope.id paramBindersRev.length) (sd s).indicesRev
    let preCtors ← Fin.mapM fun s : Fin types.length =>
      Fin.mapM fun c : Fin (sd s).shapes.length =>
        preCtorOf E table lps project paramBindersRev.length params sd s ((sd s).shapes[c.val]'c.isLt)
    pure {
      ι := indSigOf lps.length paramBindersRev.length types.length sd
      pre := { params, indices, level, ctors := preCtors }
      sortNames := types.map (·.name)
      ctorNames := types.map (·.ctors)
      metaOrders := List.ofFn fun s : Fin types.length =>
        (sd s).shapes.map fun shape => metaOrderOf shape }
  else throw (.reject .shape)

end Metalean.Frontend
