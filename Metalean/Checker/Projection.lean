/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Whnf
public import Metalean.Frontend.Translate
public import Metalean.Syntax.Structure
public import Metalean.Decide
public import Metalean.Control

@[expose] public section

namespace Metalean.Checker

open Lean (Name)
open Frontend (Failure Table)

variable {ζ : Sigs} (E : Env ζ) {ℓ : Nat}

partial def inferType {n : Nat} (Γ : Ctx ζ ℓ 0 n) : Expr ζ ℓ n → Except Failure (Expr ζ ℓ n)
  | .var v => pure (Γ.get v)
  | .sort l => pure (.sort (.succ l))
  | .const η ls => pure ((E.get η).constType.instL ls).wkClosed
  | .ind η _ ls _ _ => pure (.sort ((E.get η).block.level.inst ls))
  | .ctor η s c ls ps fds _ =>
    pure (.ind η s ls ps fun i => ((E.get η).block.ctors s c).targetIndex ls ps fds i)
  | .recr _ s _ _ _ ms _ is maj => pure (Inductive.motiveResult (ms s) is maj)
  | .quot _ l _ _ => pure (.sort l)
  | .quotMk η l α r _ => pure (.quot η l α r)
  | .quotLift _ _ _ _ _ β _ _ _ => pure β
  | .quotInd _ _ _ _ β _ e => pure (.app β e)
  | .app f a => do
    let t ← inferType Γ f
    let ⟨.forallE _ b, _⟩ ← whnfCore E t | throw (.decline .unchecked)
    pure (b.inst a)
  | .lam t b => do pure (.forallE t (← inferType (Γ.snoc t) b))
  | .forallE t b => do
    let tt ← inferType Γ t
    let ⟨.sort u, _⟩ ← whnfCore E tt | throw (.decline .unchecked)
    let tb ← inferType (Γ.snoc t) b
    let ⟨.sort v, _⟩ ← whnfCore E tb | throw (.decline .unchecked)
    pure (.sort (.imax u v))
  | .letE _ v b => inferType Γ (b.inst v)

section ProofProjection

variable {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
variable (hs : ∀ t : Fin ι.nsorts, t = s) (hc : ∀ d : Fin (ι.nctors s), d = c)
variable (hi : IsEmpty (Fin (ι.nindices s)))

mutual

partial def proofProjection {n : Nat} (Γ : Ctx ζ ℓ 0 n)
    (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (f : Fin (ι.ctors s c).nfields) (maj : Expr ζ ℓ n) : Except Failure (Expr ζ ℓ n) := do
  let I := (E.get η).block
  let Δ := I.motiveTele η ls ps s
  let type ← proofProjectionType (Γ ++ Δ) ls
    (fun p => (ps p).wkN (ι.nindices s + 1)) f (.var (Fin.last (n + ι.nindices s)))
  let motive := Ctx.lam type Δ
  let ms : Fin ι.nsorts → Expr ζ ℓ n := fun _ => motive
  let mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr ζ ℓ n := fun t d => by
    have ht := hs t
    subst t
    have hd := hc d
    subst d
    exact Ctx.lam ((ι.ctors s c).caseOrdinary (n := n) f) (I.caseTele η ls ps ms s c)
  pure (.recr η s ls .zero ps ms mins hi.elim maj)

partial def proofProjectionType {n : Nat} (Γ : Ctx ζ ℓ 0 n)
    (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (f : Fin (ι.ctors s c).nfields) (maj : Expr ζ ℓ n) : Except Failure (Expr ζ ℓ n) := do
  let I := (E.get η).block
  let mut type := Ctx.pi .prop ((I.ctors s c).fieldTele η ls ps)
  for j in [:f.val] do
    let ⟨.forallE _ body, _⟩ ← whnfCore E type | throw (.decline .unchecked)
    match body.rename? fun v => if h : v.val < n then some ⟨v.val, h⟩ else none with
    | some rest => type := rest
    | none =>
      let ⟨hj⟩ ← guardProofOr (j < (ι.ctors s c).nfields) (.decline .unchecked)
      let projected ← proofProjection Γ ls ps ⟨j, hj⟩ maj
      type := body.inst projected
  let ⟨.forallE field _, _⟩ ← whnfCore E type | throw (.decline .unchecked)
  let fieldType ← inferType E Γ field
  let ⟨.sort l, _⟩ ← whnfCore E fieldType | throw (.decline .unchecked)
  unless l = .zero do throw (.reject .propProjection)
  pure field

end

end ProofProjection

def project (table : Table) {n : Nat} (Γ : Ctx ζ ℓ 0 n) (name : Name) (idx : Nat)
    (e : Expr ζ ℓ n) : Except Failure (Expr ζ ℓ n) := do
  let t ← inferType E Γ e
  let .ok ⟨.ind (ι := ι) η s ls ps _, _⟩ := whnfCore E t | throw (.reject .shape)
  let some (.ind pos sort) := table.get? name | throw (.reject (.unknownName name))
  unless η.position = pos ∧ s.val = sort do throw (.reject .shape)
  let ⟨hc⟩ ← guardProofOr (ι.nctors s = 1) (.reject .shape)
  let c : Fin (ι.nctors s) := ⟨0, by omega⟩
  let ⟨hf⟩ ← guardProofOr (idx < (ι.ctors s c).nfields) (.reject .arity)
  if hs : (E.get η).block.IsStructure s c then
    return hs.projTerm η ls ps ⟨idx, hf⟩ e
  let ⟨hs⟩ ← guardProofOr (∀ t : Fin ι.nsorts, t = s) (.reject .shape)
  let ⟨hc⟩ ← guardProofOr (∀ d : Fin (ι.nctors s), d = c) (.reject .shape)
  let ⟨hi⟩ ← guardProofOr (ι.nindices s = 0) (.reject .shape)
  unless (ι.ctors s c).nrecFields = 0 do throw (.reject .shape)
  have hindices : IsEmpty (Fin (ι.nindices s)) :=
    ⟨fun i => Nat.not_lt_zero i.val (hi ▸ i.isLt)⟩
  proofProjection E η s c hs hc hindices Γ ls ps ⟨idx, hf⟩ e

end Metalean.Checker
