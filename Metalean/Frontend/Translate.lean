/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Decide
public import Metalean.Control
public import Metalean.Export.Normalize
public import Metalean.Frontend.Failure
public import Metalean.Frontend.Lookup
public import Metalean.Frontend.Rename
public import Metalean.Frontend.Table

@[expose] public section

namespace Metalean.Frontend

open Lean (Name)

variable {ζ : Sigs} {ℓ n : Nat}

def Scope (n : Nat) := Nat → Option (Fin n)

namespace Scope

def empty : Scope 0 := fun _ => none

def id (n : Nat) : Scope n := fun i =>
  if h : i < n then some ⟨n - 1 - i, by omega⟩ else none

def push (ρ : Scope n) : Scope (n + 1) := fun i =>
  if i = 0 then some (Fin.last n) else (ρ (i - 1)).map Fin.castSucc

def pushN (ρ : Scope n) : (k : Nat) → Scope (n + k)
  | 0 => ρ
  | k + 1 => (ρ.pushN k).push

end Scope

def translateLevel (lps : List Name) : Export.Level → Except Failure (Level lps.length)
  | .zero => pure .zero
  | .succ l => .succ <$> translateLevel lps l
  | .max l₁ l₂ => do pure (.max (← translateLevel lps l₁) (← translateLevel lps l₂))
  | .imax l₁ l₂ => do pure (.imax (← translateLevel lps l₁) (← translateLevel lps l₂))
  | .param name =>
    match lps.finIdxOf? name with
    | some p => pure (.param p)
    | none => throw (.reject .unknownLevelParam)

def translateLevels (lps : List Name) (k : Nat) (us : List Export.Level) :
    Except Failure (Fin k → Level lps.length) := do
  let ls ← us.mapM (translateLevel lps)
  if h : ls.length = k then pure fun i => ls[i.val]'(by omega) else throw (.reject .arity)

def tuple (es : List (Expr ζ ℓ n)) (k : Nat) (h : k ≤ es.length) : Fin k → Expr ζ ℓ n :=
  fun i => es[i.val]'(by omega)

abbrev Projector (ζ : Sigs) :=
  ∀ {ℓ n : Nat}, Ctx ζ ℓ 0 n → Name → Nat → Expr ζ ℓ n → Except Failure (Expr ζ ℓ n)

variable (E : Env ζ) (table : Table) (lps : List Name) (project : Projector ζ)

def translateConst (lps : List Name) {n : Nat} (pos : Nat) (us : List Export.Level)
    (args : List (Expr ζ lps.length n)) : Except Failure (Expr ζ lps.length n) := do
  match ζ.lookup pos with
  | some ⟨.const _ nlevels, η⟩ => do
    let ls ← translateLevels lps nlevels us
    pure ((Expr.const η ls).appList args)
  | _ => throw .internal

def orderMaps? (metaOrder : List Nat) (k : Nat) :
    Option ((Fin k → Option (Fin k)) × (Fin k → Option (Fin k))) :=
  if metaOrder.length = k then
    some
      (fun j => (metaOrder.idxOf? j.val).bind fun o => if h : o < k then some ⟨o, h⟩ else none,
      fun o => metaOrder[o.val]?.bind fun j => if h : j < k then some ⟨j, h⟩ else none)
  else none

def isIdentityOrder (metaOrder : List Nat) (k : Nat) : Bool :=
  metaOrder == List.range k

def wrapCase {ι : IndSig} (I : Inductive ζ ι) (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (ms : Fin ι.nsorts → Expr ζ ℓ n) (t : Fin ι.nsorts) (c : Fin (ι.nctors t))
    (metaOrder : List Nat) (minor : Expr ζ ℓ n) : Except Failure (Expr ζ ℓ n) := do
  let csig := ι.ctors t c
  if isIdentityOrder metaOrder (csig.nfields + csig.nrecFields) then pure minor else
  let some (π, _) := orderMaps? metaOrder (csig.nfields + csig.nrecFields) | throw .internal
  let some fieldVars := Fin.mapM fun j : Fin (csig.nfields + csig.nrecFields) =>
      (π j).map fun o =>
        (Expr.var ⟨n + o.val, by omega⟩ :
          Expr ζ ℓ (n + csig.nfields + csig.nrecFields + csig.nrecFields))
    | throw .internal
  let ihVars := fun r : Fin csig.nrecFields =>
    (Expr.var ⟨n + csig.nfields + csig.nrecFields + r.val, by omega⟩ :
      Expr ζ ℓ (n + csig.nfields + csig.nrecFields + csig.nrecFields))
  let body := (((minor.wkN csig.nfields).wkN csig.nrecFields).wkN
    csig.nrecFields).apps (Fin.append fieldVars ihVars)
  pure (Ctx.lam body (I.caseTele η ls ps ms t c))

def indTerm {ι : IndSig} (I : Inductive ζ ι) (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ) : Expr ζ ℓ 0 :=
  let body : Expr ζ ℓ (ι.nparams + ι.nindices s) :=
    .ind η s ls (fun p => .var ⟨p.val, by omega⟩) fun i => .var ⟨ι.nparams + i.val, by omega⟩
  (I.argTele s){ls}.lam body

def ctorTerm {ι : IndSig} (I : Inductive ζ ι) (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ)
    (metaOrder : List Nat) : Except Failure (Expr ζ ℓ 0) := do
  let csig := ι.ctors s c
  let some (π, πinv) := orderMaps? metaOrder (csig.nfields + csig.nrecFields) | throw .internal
  let fields : Ctx ζ ℓ ι.nparams (ι.nparams + csig.nfields + csig.nrecFields) :=
    (I.ctors s c).fieldTele η ls fun p => .var p
  let some fields' := Ctx.permute? (k := csig.nfields + csig.nrecFields) (by omega) π πinv fields
    | throw .internal
  let fieldVar (o : Fin (csig.nfields + csig.nrecFields)) :
      Option (Expr ζ ℓ (ι.nparams + (csig.nfields + csig.nrecFields))) := do
    let j ← πinv o
    some (.var ⟨ι.nparams + j.val, by omega⟩)
  let some fds := Fin.mapM fun f => fieldVar (f.castAdd csig.nrecFields)
    | throw .internal
  let some recFds := Fin.mapM fun r => fieldVar (Fin.natAdd csig.nfields r)
    | throw .internal
  let body : Expr ζ ℓ (ι.nparams + (csig.nfields + csig.nrecFields)) :=
    .ctor η s c ls (fun p => .var ⟨p.val, by omega⟩) fds recFds
  pure (Ctx.lam body (I.params{ls} ++ fields'))

def leanCaseType {ι : IndSig} (I : Inductive ζ ι) (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (ms : Fin ι.nsorts → Expr ζ ℓ n) (t : Fin ι.nsorts) (c : Fin (ι.nctors t))
    (metaOrder : List Nat) : Except Failure (Expr ζ ℓ n) := do
  let csig := ι.ctors t c
  let some (π, πinv) := orderMaps? metaOrder (csig.nfields + csig.nrecFields) | throw .internal
  let π' : Fin (csig.nfields + csig.nrecFields + csig.nrecFields) →
      Option (Fin (csig.nfields + csig.nrecFields + csig.nrecFields)) := fun j =>
    if h : j.val < csig.nfields + csig.nrecFields then (π ⟨j.val, h⟩).map (Fin.castAdd _)
    else some j
  let πinv' : Fin (csig.nfields + csig.nrecFields + csig.nrecFields) →
      Option (Fin (csig.nfields + csig.nrecFields + csig.nrecFields)) := fun o =>
    if h : o.val < csig.nfields + csig.nrecFields then (πinv ⟨o.val, h⟩).map (Fin.castAdd _)
    else some o
  let caseTele : Ctx ζ ℓ n (n + csig.nfields + csig.nrecFields + csig.nrecFields) :=
    I.caseTele η ls ps ms t c
  let some tele := Ctx.permute? (k := csig.nfields + csig.nrecFields + csig.nrecFields)
      (by omega) π' πinv' caseTele
    | throw .internal
  let ρ : Fin (n + csig.nfields + csig.nrecFields + csig.nrecFields) →
      Option (Fin (n + (csig.nfields + csig.nrecFields + csig.nrecFields))) := fun v =>
    if h : v.val < n then some ⟨v.val, by omega⟩
    else (πinv' ⟨v.val - n, by omega⟩).map fun j => ⟨n + j.val, by omega⟩
  let some concl := (I.caseType η ls ps ms t c).rename? ρ | throw .internal
  pure (Ctx.pi concl tele)

def leanCaseBinders {ι : IndSig} (I : Inductive ζ ι) (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (metaOrders : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat) :
    (count : Nat) → count ≤ Fin.sum ι.nctors →
      Except Failure (Ctx ζ ℓ (ι.nparams + ι.nsorts) (ι.nparams + ι.nsorts + count))
  | 0 => fun _ => pure .nil
  | count + 1 => fun hcount => do
    let ⟨t, c⟩ := Fin.decodeSigma ι.nctors ⟨count, by omega⟩
    let Γ ← leanCaseBinders I η ls metaOrders count (by omega)
    let ty ← leanCaseType I η ls
      (fun param => Expr.var (param.castLE (by omega)))
      (fun t => Expr.var ⟨ι.nparams + t.val, by omega⟩)
      t c (metaOrders t c)
    pure (Γ.snoc ty)

def recrTerm {ι : IndSig} (I : Inductive ζ ι) (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ)
    (metaOrders : (t : Fin ι.nsorts) → Fin (ι.nctors t) → List Nat) :
    Except Failure (Expr ζ ℓ 0) := do
  let ps : Fin ι.nparams → Expr ζ ℓ (ι.nparams + ι.nsorts + Fin.sum ι.nctors) :=
    fun param => .var (param.castLE (by omega))
  let is := I.indexTele ls s ps
  let maj : Expr ζ ℓ (ι.nparams + ι.nsorts + Fin.sum ι.nctors + ι.nindices s) :=
    .ind η s ls (fun param => (ps param).wkN (ι.nindices s))
      fun index => .var ⟨ι.nparams + ι.nsorts + Fin.sum ι.nctors + index.val, by omega⟩
  let cases ← leanCaseBinders I η ls metaOrders (Fin.sum ι.nctors) le_rfl
  let tele : Ctx ζ ℓ 0 _ :=
    I.params{ls} ++ I.motiveBinders η ls l ++ cases ++ is |>.snoc maj
  let psB : Fin ι.nparams → Expr ζ ℓ (ι.recrEnd s) :=
    fun p => .var (IndSig.RecrBinder.param (s := s) p).resolve
  let msB : Fin ι.nsorts → Expr ζ ℓ (ι.recrEnd s) :=
    fun t => .var (IndSig.RecrBinder.motive (s := s) t).resolve
  let some minsB := Fin.mapM fun t => Fin.mapM fun c =>
      (wrapCase I η ls psB msB t c (metaOrders t c)
        (.var (IndSig.RecrBinder.case (s := s) t c).resolve)).toOption
    | throw .internal
  let body : Expr ζ ℓ (ι.recrEnd s) :=
    .recr η s ls l psB msB minsB (fun i => .var (IndSig.RecrBinder.index i).resolve)
      (.var (IndSig.RecrBinder.major (ι := ι) (s := s)).resolve)
  pure (tele.lam body)

def quotTerm (η : Head ζ .quot) (eqHead : Head ζ (.inductive Eq.sig)) :
    Export.QuotKind → List (Level ℓ) → Except Failure (Expr ζ ℓ 0)
  | .type, [u] =>
    pure (Ctx.lam (.quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩))
      #t[.sort u, Quot.relType (.var ⟨0, by omega⟩)])
  | .ctor, [u] =>
    pure (Ctx.lam (.quotMk η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩))
      #t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        .var ⟨0, by omega⟩])
  | .lift, [u, v] =>
    pure (Ctx.lam
      (.quotLift η u v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩)
        (.var ⟨3, by omega⟩) (.var ⟨4, by omega⟩) (.var ⟨5, by omega⟩))
      #t[.sort u, Quot.relType (.var ⟨0, by omega⟩), .sort v,
        .forallE (.var ⟨0, by omega⟩) (.var ⟨2, by omega⟩),
        Quot.compatType eqHead v (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩) (.var ⟨3, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)])
  | .ind, [u] =>
    pure (Ctx.lam
      (.quotInd η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩) (.var ⟨2, by omega⟩)
        (.var ⟨3, by omega⟩) (.var ⟨4, by omega⟩))
      #t[.sort u, Quot.relType (.var ⟨0, by omega⟩),
        Quot.motiveType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩),
        Quot.minorType η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)
          (.var ⟨2, by omega⟩),
        .quot η u (.var ⟨0, by omega⟩) (.var ⟨1, by omega⟩)])
  | _, _ => throw (.reject .arity)

def saturate {n : Nat} (arity : Nat) (args : List (Expr ζ ℓ n))
    (node : (Fin arity → Expr ζ ℓ n) → Except Failure (Expr ζ ℓ n))
    (eta : Unit → Except Failure (Expr ζ ℓ 0)) : Except Failure (Expr ζ ℓ n) := do
  if h : arity ≤ args.length then
    pure ((← node (tuple args arity h)).appList (args.drop arity))
  else
    pure ((← eta ()).wkClosed.appList args)

def translateSpecial (E : Env ζ) (lps : List Name) {n : Nat}
    (us : List Export.Level) (args : List (Expr ζ lps.length n)) :
    Binding → Except Failure (Expr ζ lps.length n)
  | .const _ => throw .internal
  | .quot pos kind => do
    let some ⟨.quot, η⟩ := ζ.lookup pos | throw .internal
    let us ← us.mapM (translateLevel lps)
    let eqHead := (E.get η).eqHead
    let eta := fun _ : Unit => quotTerm η eqHead kind us
    match kind, us with
    | .type, [u] => saturate 2 args (fun a => pure (.quot η u (a 0) (a 1))) eta
    | .ctor, [u] => saturate 3 args (fun a => pure (.quotMk η u (a 0) (a 1) (a 2))) eta
    | .lift, [u, v] =>
      saturate 6 args (fun a => pure (.quotLift η u v (a 0) (a 1) (a 2) (a 3) (a 4) (a 5))) eta
    | .ind, [u] => saturate 5 args (fun a => pure (.quotInd η u (a 0) (a 1) (a 2) (a 3) (a 4))) eta
    | _, _ => throw (.reject .arity)
  | .ind pos s => do
    let some ⟨.inductive ι, η⟩ := ζ.lookup pos | throw .internal
    let I := (E.get η).block
    if hs : s < ι.nsorts then
      let s : Fin ι.nsorts := ⟨s, hs⟩
      let ls ← translateLevels lps ι.nlevels us
      saturate (ι.nparams + ι.nindices s) args
        (fun a => pure (.ind η s ls (fun p => a (p.castAdd _)) fun i => a (Fin.natAdd _ i)))
        fun _ => pure (indTerm I η s ls)
    else throw .internal
  | .ctor pos s c metaOrder => do
    let some ⟨.inductive ι, η⟩ := ζ.lookup pos | throw .internal
    let I := (E.get η).block
    if hs : s < ι.nsorts then
      let s : Fin ι.nsorts := ⟨s, hs⟩
      if hc : c < ι.nctors s then
        let c : Fin (ι.nctors s) := ⟨c, hc⟩
        let csig := ι.ctors s c
        let ls ← translateLevels lps ι.nlevels us
        saturate (ι.nparams + (csig.nfields + csig.nrecFields)) args
          (fun a => do
            let some (_, πinv) := orderMaps? metaOrder (csig.nfields + csig.nrecFields)
              | throw .internal
            let fieldArg (o : Fin (csig.nfields + csig.nrecFields)) :
                Option (Expr ζ lps.length n) :=
              (πinv o).map fun j => a (Fin.natAdd ι.nparams j)
            let some fds := Fin.mapM fun f => fieldArg (f.castAdd csig.nrecFields)
              | throw .internal
            let some recFds := Fin.mapM fun r => fieldArg (Fin.natAdd csig.nfields r)
              | throw .internal
            pure (.ctor η s c ls (fun p => a (p.castAdd _)) fds recFds))
          fun _ => ctorTerm I η s c ls metaOrder
      else throw .internal
    else throw .internal
  | .recr pos s orders => do
    let some ⟨.inductive ι, η⟩ := ζ.lookup pos | throw .internal
    let I := (E.get η).block
    if hs : s < ι.nsorts then
      let s : Fin ι.nsorts := ⟨s, hs⟩
      let (l, rest) ←
        if I.LargeElim then
          match us with
          | u :: rest => do pure (← translateLevel lps u, rest)
          | [] => throw (.reject .arity)
        else pure (Level.zero, us)
      let ls ← translateLevels lps ι.nlevels rest
      let some metaOrders := Fin.mapM fun t : Fin ι.nsorts =>
          Fin.mapM fun c : Fin (ι.nctors t) => orders[t.val]?.bind (·[c.val]?)
        | throw .internal
      saturate (ι.recrEnd s) args
        (fun a => do
          let ps : Fin ι.nparams → Expr ζ lps.length n :=
            fun p => a (IndSig.RecrBinder.param (s := s) p).resolve
          let ms : Fin ι.nsorts → Expr ζ lps.length n :=
            fun t => a (IndSig.RecrBinder.motive (s := s) t).resolve
          let some mins := Fin.mapM fun t => Fin.mapM fun c =>
              (wrapCase I η ls ps ms t c (metaOrders t c)
                (a (IndSig.RecrBinder.case (s := s) t c).resolve)).toOption
            | throw .internal
          pure (.recr η s ls l ps ms mins
            (fun i => a (IndSig.RecrBinder.index i).resolve)
            (a (IndSig.RecrBinder.major (ι := ι) (s := s)).resolve)))
        fun _ => recrTerm I η s ls l metaOrders
    else throw .internal

partial def translateWith {n : Nat} (Γ : Ctx ζ lps.length 0 n) (ρ : Scope n)
    (args : List (Expr ζ lps.length n)) : Export.Expr → Except Failure (Expr ζ lps.length n)
  | .bvar i =>
    match ρ i with
    | some v => pure ((Expr.var v).appList args)
    | none => throw (.reject .unboundVariable)
  | .sort l => do pure ((Expr.sort (← translateLevel lps l)).appList args)
  | .const name us =>
    match table.get? name with
    | none => throw (.reject (.unknownName name))
    | some (.const pos) => translateConst lps pos us args
    | some binding => translateSpecial E lps us args binding
  | .app fn arg => do
    let arg ← translateWith Γ ρ [] arg
    translateWith Γ ρ (arg :: args) fn
  | .lam type body => do
    let type' ← translateWith Γ ρ [] type
    pure ((Expr.lam type' (← translateWith (Γ.snoc type') ρ.push [] body)).appList args)
  | .forallE type body => do
    let type' ← translateWith Γ ρ [] type
    pure ((Expr.forallE type' (← translateWith (Γ.snoc type') ρ.push [] body)).appList args)
  | .letE type value body => do
    let type' ← translateWith Γ ρ [] type
    pure ((Expr.letE type' (← translateWith Γ ρ [] value)
      (← translateWith Γ ρ [] (body.inst value)).wk).appList args)
  | .proj name idx e => do
    pure ((← project Γ name idx (← translateWith Γ ρ [] e)).appList args)
  | .natLit _ => throw (.decline .literal)
  | .stringLit _ => throw (.decline .literal)

def translate {n : Nat} (Γ : Ctx ζ lps.length 0 n) (ρ : Scope n) (e : Export.Expr) :
    Except Failure (Expr ζ lps.length n) :=
  translateWith E table lps project Γ ρ [] e

end Metalean.Frontend
