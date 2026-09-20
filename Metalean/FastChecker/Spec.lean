/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.LiteralTyping
public import Metalean.FastChecker.Quot
public import Metalean.FastChecker.LiteralTyping
public import Metalean.FastChecker.Whnf
public import Metalean.Strong.Inversion
public import Metalean.Control
public import Metalean.Export.Basic
public import Metalean.Frontend.Failure
public import Metalean.Metatheory.Conversion
public import Metalean.Metatheory.Injectivity
public import Metalean.Metatheory.SubjectReduction
public import Metalean.Strong.Context
import Metalean.Metatheory.Unique
public import Metalean.FastChecker.Coherence
import Metalean.Strong.Strengthen

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

section

variable {ζ : Sigs} (L : Literals) (F : FEnv) (ℓ : Nat)

structure Sem (G : FCtx) {ζ : Sigs} {ℓ : Nat} (E : Env ζ) {n : Nat} (Γ : Ctx ζ ℓ 0 n) :
    Prop where
  env : FEnv.Denotes L F E
  ordered : E.Ordered
  trust : L.NatTrust E
  ctx : FCtx.Denotes L ⟨ζ, E⟩ G Γ
  wf : E[Γ] ⊢ₛ ok

def InferSpec (G : FCtx) (fe ft : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e₀ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe e₀ →
  ∃ e t : Expr ζ ℓ n, FExpr.Denotes L ⟨ζ, E⟩ 0 fe e ∧ FExpr.Denotes L ⟨ζ, E⟩ 0 ft t ∧
    E[Γ] ⊢ₛ e : t

def InferOnlySpec (G : FCtx) (fe ft : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e t : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe e →
  E[Γ] ⊢ₛ e : t →
  ∃ t', FExpr.Denotes L ⟨ζ, E⟩ 0 ft t' ∧ E[Γ] ⊢ₛ e : t'

def InferTeleSpec (G : FCtx) (k : Nat) (fe ft : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e₀ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ k fe e₀ →
  ∃ e t : Expr ζ ℓ n, FExpr.Denotes L ⟨ζ, E⟩ k fe e ∧ FExpr.Denotes L ⟨ζ, E⟩ 0 ft t ∧
    E[Γ] ⊢ₛ e : t

def InferOnlyTeleSpec (G : FCtx) (k : Nat) (fe ft : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e t : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ k fe e →
  E[Γ] ⊢ₛ e : t →
  ∃ t', FExpr.Denotes L ⟨ζ, E⟩ 0 ft t' ∧ E[Γ] ⊢ₛ e : t'

def TypeEqTeleSpec (G : FCtx) (k : Nat) (ft₁ ft₂ : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃t₁ t₂ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ k ft₁ t₁ →
  FExpr.Denotes L ⟨ζ, E⟩ k ft₂ t₂ →
  E[Γ] ⊢ₛ t₁ typ →
  E[Γ] ⊢ₛ t₂ typ →
  E[Γ] ⊢ₛ t₁ ≡ t₂ typ

def DefEqTeleSpec (G : FCtx) (k : Nat) (fe₁ fe₂ : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e₁ e₂ t₁ t₂ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ k fe₁ e₁ →
  FExpr.Denotes L ⟨ζ, E⟩ k fe₂ e₂ →
  E[Γ] ⊢ₛ e₁ : t₁ →
  E[Γ] ⊢ₛ e₂ : t₂ →
  E[Γ] ⊢ₛ e₁ ≡ e₂ : t₁

def SortSpec (G : FCtx) (ft : FExpr) (l : FLevel) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃t : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 ft t →
  E[Γ] ⊢ₛ t typ →
  ∃ l', FLevel.Denotes l l' ∧ E[Γ] ⊢ₛ t ≡ .sort ⟦l'⟧ typ

def ForallSpec (G : FCtx) (ft ft₁ fb : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃t : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 ft t →
  E[Γ] ⊢ₛ t typ →
  ∃ t₁ b, FExpr.Denotes L ⟨ζ, E⟩ 0 ft₁ t₁ ∧ FExpr.Denotes L ⟨ζ, E⟩ 1 fb b ∧
    E[Γ] ⊢ₛ t ≡ .forallE t₁ b typ

def CheckSpec (G : FCtx) (fe ft : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e₀ t : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe e₀ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 ft t →
  E[Γ] ⊢ₛ t typ →
  ∃ e : Expr ζ ℓ n, FExpr.Denotes L ⟨ζ, E⟩ 0 fe e ∧ E[Γ] ⊢ₛ e : t

def TypeEqSpec (G : FCtx) (ft₁ ft₂ : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃t₁ t₂ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 ft₁ t₁ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 ft₂ t₂ →
  E[Γ] ⊢ₛ t₁ typ →
  E[Γ] ⊢ₛ t₂ typ →
  E[Γ] ⊢ₛ t₁ ≡ t₂ typ

def DefEqSpec (G : FCtx) (fe₁ fe₂ : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e₁ e₂ t₁ t₂ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe₁ e₁ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe₂ e₂ →
  E[Γ] ⊢ₛ e₁ : t₁ →
  E[Γ] ⊢ₛ e₂ : t₂ →
  E[Γ] ⊢ₛ e₁ ≡ e₂ : t₁

def SortedSpec (G : FCtx) (fe : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e₀ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe e₀ →
  ∃ (e : Expr ζ ℓ n) (u : Level ℓ), FExpr.Denotes L ⟨ζ, E⟩ 0 fe e ∧ E[Γ] ⊢ₛ e : .sort u

def SortedAtSpec (G : FCtx) (fe : FExpr) (l : FLevel) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e₀ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe e₀ →
  ∃ (e : Expr ζ ℓ n) (l' : RawLevel ℓ), FExpr.Denotes L ⟨ζ, E⟩ 0 fe e ∧ FLevel.Denotes l l' ∧
    E[Γ] ⊢ₛ e : .sort ⟦l'⟧

def PropSpec (G : FCtx) (ft : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃t : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 ft t →
  E[Γ] ⊢ₛ t typ →
  E[Γ] ⊢ₛ t : .prop

def RedSpec (G : FCtx) (fe₁ fe₂ : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e₁ t : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe₁ e₁ →
  E[Γ] ⊢ₛ e₁ : t →
  ∃ e₂, FExpr.Denotes L ⟨ζ, E⟩ 0 fe₂ e₂ ∧ E[Γ] ⊢ₛ e₁ ≡ e₂ : t

def TypedSpec (G : FCtx) (fe ft : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃e₀ t₀ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe e₀ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 ft t₀ →
  ∃ e t : Expr ζ ℓ n, FExpr.Denotes L ⟨ζ, E⟩ 0 fe e ∧ FExpr.Denotes L ⟨ζ, E⟩ 0 ft t ∧
    E[Γ] ⊢ₛ e : t

partial def FExpr.noProj : (fe : FExpr) → Option (PLift fe.NoProj)
  | .bvar i => some ⟨.bvar i⟩
  | .fvar i => some ⟨.fvar i⟩
  | .sort l => some ⟨.sort l⟩
  | .const pos ls => some ⟨.const pos ls⟩
  | .ind _ _ _ ps is => do
    let ⟨hp⟩ ← noProjArr ps
    let ⟨hi⟩ ← noProjArr is
    pure ⟨.ind hp hi⟩
  | .ctor _ _ _ _ ps fds recFds => do
    let ⟨hp⟩ ← noProjArr ps
    let ⟨hf⟩ ← noProjArr fds
    let ⟨hr⟩ ← noProjArr recFds
    pure ⟨.ctor hp hf hr⟩
  | .recr _ _ _ _ ps ms mins is maj => do
    let ⟨hp⟩ ← noProjArr ps
    let ⟨hm⟩ ← noProjArr ms
    let ⟨hmin⟩ ← noProjArr mins
    let ⟨hi⟩ ← noProjArr is
    let ⟨hmaj⟩ ← noProj maj
    pure ⟨.recr hp hm hmin hi hmaj⟩
  | .quot _ _ α r => do
    let ⟨hα⟩ ← noProj α
    let ⟨hr⟩ ← noProj r
    pure ⟨.quot hα hr⟩
  | .quotMk _ _ α r a => do
    let ⟨hα⟩ ← noProj α
    let ⟨hr⟩ ← noProj r
    let ⟨ha⟩ ← noProj a
    pure ⟨.quotMk hα hr ha⟩
  | .quotLift _ _ _ α r β f h a => do
    let ⟨hα⟩ ← noProj α
    let ⟨hr⟩ ← noProj r
    let ⟨hβ⟩ ← noProj β
    let ⟨hf⟩ ← noProj f
    let ⟨hh⟩ ← noProj h
    let ⟨ha⟩ ← noProj a
    pure ⟨.quotLift hα hr hβ hf hh ha⟩
  | .quotInd _ _ α r β f a => do
    let ⟨hα⟩ ← noProj α
    let ⟨hr⟩ ← noProj r
    let ⟨hβ⟩ ← noProj β
    let ⟨hf⟩ ← noProj f
    let ⟨ha⟩ ← noProj a
    pure ⟨.quotInd hα hr hβ hf ha⟩
  | .proj .. => none
  | .app f a => do
    let ⟨hf⟩ ← noProj f
    let ⟨ha⟩ ← noProj a
    pure ⟨.app hf ha⟩
  | .lam t b => do
    let ⟨ht⟩ ← noProj t
    let ⟨hb⟩ ← noProj b
    pure ⟨.lam ht hb⟩
  | .forallE t b => do
    let ⟨ht⟩ ← noProj t
    let ⟨hb⟩ ← noProj b
    pure ⟨.forallE ht hb⟩
  | .letE t v b => do
    let ⟨ht⟩ ← noProj t
    let ⟨hv⟩ ← noProj v
    let ⟨hb⟩ ← noProj b
    pure ⟨.letE ht hv hb⟩
  | .natLit num => some ⟨.natLit num⟩
  | .strLit str => some ⟨.strLit str⟩
where
  noProjArr (xs : Array FExpr) : Option (PLift (∀ x ∈ xs, x.NoProj)) := do
    let ⟨h⟩ ← Array.forallM xs (fun i hi => (xs[i]'hi).NoProj) fun i hi => noProj (xs[i]'hi)
    pure ⟨fun x hx => by
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
      exact h i hi⟩

def DefEqAtSpec (G : FCtx) (ft fe₁ fe₂ : FExpr) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄ ⦃n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃t e₁ e₂ : Expr ζ ℓ n⦄,
  Sem L F G E Γ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 ft t →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe₁ e₁ →
  FExpr.Denotes L ⟨ζ, E⟩ 0 fe₂ e₂ →
  E[Γ] ⊢ₛ e₁ ≡ e₂ : t

def UnfoldsTo (F : FEnv) (pos : Nat) (ls : Array FLevel) (v : FExpr) : Prop :=
  ∀ nlevels t v₀, F[pos]? = some (.def nlevels t v₀) → v = v₀.instL ls

structure Caches where
  whnfCore : Std.DHashMap (FCtx × FExpr)
    (fun ⟨G, fe⟩ => {fe₂ : FExpr // RedSpec L F ℓ G fe fe₂}) := ∅
  whnf : Std.DHashMap (FCtx × FExpr)
    (fun ⟨G, fe⟩ => {fe₂ : FExpr // RedSpec L F ℓ G fe fe₂}) := ∅
  infer : Std.DHashMap (FCtx × FExpr)
    (fun ⟨G, fe⟩ => {ft : FExpr // InferSpec L F ℓ G fe ft}) := ∅
  inferOnly : Std.DHashMap (FCtx × FExpr)
    (fun ⟨G, fe⟩ => {ft : FExpr // InferOnlySpec L F ℓ G fe ft}) := ∅
  defEq : Std.DHashMap (FCtx × FExpr × FExpr)
    (fun ⟨G, fe₁, fe₂⟩ => PLift (DefEqSpec L F ℓ G fe₁ fe₂)) := ∅
  failure : Std.HashSet (FExpr × FExpr) := ∅
  unfold : Std.DHashMap (Nat × Array FLevel)
    (fun ⟨pos, ls⟩ => {v : FExpr // UnfoldsTo F pos ls v}) := ∅
  intern : Std.HashMap FExpr FExpr := ∅
  ancestors : Std.HashMap USize ((G : FCtx) × FCtx.Ancestors G) := ∅
  push : Std.HashMap (USize × USize)
    ((k : FCtx × FExpr) × {G : FCtx // G = k.1.push k.2}) := ∅

abbrev CheckM := EStateM Failure (Caches L F ℓ)

instance : MonadLiftT (Except Failure) (CheckM L F ℓ) where
  monadLift
    | .ok a => pure a
    | .error f => throw f

def CheckM.eval {α : Type} (x : CheckM L F ℓ α) : Except Failure α :=
  match x.run {} with
  | .ok a _ => .ok a
  | .error e _ => .error e

instance {α : Type} : Inhabited (CheckM L F ℓ α) := ⟨throw .internal⟩

variable {L F ℓ}

theorem Sem.nil {E : Env ζ} (hE : FEnv.Denotes L F E) (ho : E.Ordered) (ht : L.NatTrust E) :
    Sem L F #[] E (.nil (ℓ := ℓ)) :=
  ⟨hE, ho, ht, .nil, Tele.Forall.nil⟩

theorem Sem.size {G : FCtx} {E : Env ζ} {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hS : Sem L F G E Γ) :
    G.size = n := by
  have := hS.ctx.size
  omega

theorem Sem.snoc {G : FCtx} {E : Env ζ} {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hS : Sem L F G E Γ) {ft : FExpr} {t : Expr ζ ℓ n} {l : Level ℓ}
    (ht : FExpr.Denotes L ⟨ζ, E⟩ 0 ft t) (hty : E[Γ] ⊢ₛ t : .sort l) :
    Sem L F (G.push ft) E (Γ.snoc t) :=
  ⟨hS.env, hS.ordered, hS.trust, hS.ctx.snoc ht, hS.wf.snoc ⟨l, hty⟩⟩

theorem InferSpec.push {G : FCtx} {fe ft : FExpr} (t : FExpr)
    (hr : fe.fvarRange ≤ G.size) (hc : fe.data.looseBVarRange.toNat = 0) :
    InferSpec L F ℓ G fe ft →
    InferSpec L F ℓ (G.push t) fe ft := by
  intro h ζ E n Γ e₀ hS hden
  have hwf := hS.wf
  revert e₀ hwf
  refine hS.ctx.push_elim
    (motive := fun {b} Γ => ∀ e₀ : Expr ζ ℓ b, FExpr.Denotes L ⟨ζ, E⟩ 0 fe e₀ → E[Γ] ⊢ₛ ok →
      ∃ e t' : Expr ζ ℓ b, FExpr.Denotes L ⟨ζ, E⟩ 0 fe e ∧ FExpr.Denotes L ⟨ζ, E⟩ 0 ft t' ∧
        E[Γ] ⊢ₛ e : t') ?_
  intro b₀ Γ₀ t' hΓ₀ _ e₀ hden hwf
  cases hwf with
  | snoc hwf₀ _ =>
    have hb := hΓ₀.size
    have ⟨e₁, he₁⟩ := hden.strengthen (by omega) hc
    have ⟨e, t₀, he, htd, hty⟩ := h ⟨hS.env, hS.ordered, hS.trust, hΓ₀, hwf₀⟩ he₁
    exact ⟨e.wk, t₀.wk, he.wk, htd.wk, hty.wk t'⟩

theorem InferSpec.extend {G₀ G : FCtx} {fe ft : FExpr}
    (hr : fe.fvarRange ≤ G₀.size) (hc : fe.data.looseBVarRange.toNat = 0) :
    FCtx.Extends G₀ G →
    InferSpec L F ℓ G₀ fe ft →
    InferSpec L F ℓ G fe ft := by
  intro hx h
  induction hx with
  | refl => exact h
  | push t hx ih =>
    have := hx.size_le
    exact ih.push t (by omega) hc

theorem RedSpec.push {G : FCtx} {fe₁ fe₂ ft : FExpr} (t : FExpr)
    (hr : fe₁.fvarRange ≤ G.size) (hc : fe₁.data.looseBVarRange.toNat = 0)
    (hinf : InferSpec L F ℓ G fe₁ ft) :
    RedSpec L F ℓ G fe₁ fe₂ →
    RedSpec L F ℓ (G.push t) fe₁ fe₂ := by
  intro h ζ E n Γ e₁ ty hS hd hty
  refine hS.ctx.push_elim
    (motive := fun {b} Γ => E[Γ] ⊢ₛ ok → ∀ e₁ ty : Expr ζ ℓ b,
      FExpr.Denotes L ⟨ζ, E⟩ 0 fe₁ e₁ → E[Γ] ⊢ₛ e₁ : ty →
      ∃ e₂, FExpr.Denotes L ⟨ζ, E⟩ 0 fe₂ e₂ ∧ E[Γ] ⊢ₛ e₁ ≡ e₂ : ty) ?_ hS.wf e₁ ty hd hty
  intro b₀ Γ₀ t' hΓ₀ _ hwf e₁ ty hd hty
  cases hwf with
  | snoc hwf₀ _ =>
    have hb := hΓ₀.size
    have ⟨e', he'⟩ := hd.strengthen (by omega) hc
    have hS₀ : Sem L F G E Γ₀ := ⟨hS.env, hS.ordered, hS.trust, hΓ₀, hwf₀⟩
    have ⟨e'', _, he'', _, hty''⟩ := hinf hS₀ he'
    have ⟨e₂, he₂, heq⟩ := h hS₀ he'' hty''
    have hΓ : E[Γ₀.snoc t'] ⊢ₛ ok := hwf₀.snoc ‹_›
    have hco := FExpr.Denotes.defeq hS.ordered hΓ hd he''.wk hty (hty''.wk t')
    exact ⟨e₂.wk, he₂.wk, hco.trans (DefeqStrong.retype hS.ordered hΓ (heq.wk t') hco.right)⟩

theorem RedSpec.extend {G₀ G : FCtx} {fe₁ fe₂ ft : FExpr}
    (hr : fe₁.fvarRange ≤ G₀.size) (hc : fe₁.data.looseBVarRange.toNat = 0)
    (hinf : InferSpec L F ℓ G₀ fe₁ ft) :
    FCtx.Extends G₀ G →
    RedSpec L F ℓ G₀ fe₁ fe₂ →
    RedSpec L F ℓ G fe₁ fe₂ := by
  intro hx h
  induction hx with
  | refl => exact h
  | push t hx ih =>
    have := hx.size_le
    exact ih.push t (by omega) hc (hinf.extend hr hc hx)

theorem DefEqSpec.push {G : FCtx} {fe₁ fe₂ ft₁ ft₂ : FExpr} (t : FExpr)
    (hr₁ : fe₁.fvarRange ≤ G.size) (hr₂ : fe₂.fvarRange ≤ G.size)
    (hc₁ : fe₁.data.looseBVarRange.toNat = 0) (hc₂ : fe₂.data.looseBVarRange.toNat = 0)
    (hinf₁ : InferSpec L F ℓ G fe₁ ft₁) (hinf₂ : InferSpec L F ℓ G fe₂ ft₂) :
    DefEqSpec L F ℓ G fe₁ fe₂ →
    DefEqSpec L F ℓ (G.push t) fe₁ fe₂ := by
  intro h ζ E n Γ e₁ e₂ ty₁ ty₂ hS hd₁ hd₂ hty₁ hty₂
  refine hS.ctx.push_elim
    (motive := fun {b} Γ => E[Γ] ⊢ₛ ok → ∀ e₁ e₂ ty₁ ty₂ : Expr ζ ℓ b,
      FExpr.Denotes L ⟨ζ, E⟩ 0 fe₁ e₁ → FExpr.Denotes L ⟨ζ, E⟩ 0 fe₂ e₂ →
      E[Γ] ⊢ₛ e₁ : ty₁ → E[Γ] ⊢ₛ e₂ : ty₂ →
      E[Γ] ⊢ₛ e₁ ≡ e₂ : ty₁) ?_ hS.wf e₁ e₂ ty₁ ty₂ hd₁ hd₂ hty₁ hty₂
  intro b₀ Γ₀ t' hΓ₀ _ hwf e₁ e₂ ty₁ ty₂ hd₁ hd₂ hty₁ hty₂
  cases hwf with
  | snoc hwf₀ _ =>
    have hb := hΓ₀.size
    have ⟨u₁, hu₁⟩ := hd₁.strengthen (by omega) hc₁
    have ⟨u₂, hu₂⟩ := hd₂.strengthen (by omega) hc₂
    have hS₀ : Sem L F G E Γ₀ := ⟨hS.env, hS.ordered, hS.trust, hΓ₀, hwf₀⟩
    have ⟨v₁, _, hv₁, _, htv₁⟩ := hinf₁ hS₀ hu₁
    have ⟨v₂, _, hv₂, _, htv₂⟩ := hinf₂ hS₀ hu₂
    have heq := h hS₀ hv₁ hv₂ htv₁ htv₂
    have hΓ : E[Γ₀.snoc t'] ⊢ₛ ok := hwf₀.snoc ‹_›
    have hco₁ := FExpr.Denotes.defeq hS.ordered hΓ hd₁ hv₁.wk hty₁ (htv₁.wk t')
    have hco₂ := FExpr.Denotes.defeq hS.ordered hΓ hd₂ hv₂.wk hty₂ (htv₂.wk t')
    have hmid := DefeqStrong.retype hS.ordered hΓ (heq.wk t') hco₁.right
    exact hco₁.trans (hmid.trans (DefeqStrong.retype hS.ordered hΓ hco₂.symm hmid.right))

theorem DefEqSpec.extend {G₀ G : FCtx} {fe₁ fe₂ ft₁ ft₂ : FExpr}
    (hr₁ : fe₁.fvarRange ≤ G₀.size) (hr₂ : fe₂.fvarRange ≤ G₀.size)
    (hc₁ : fe₁.data.looseBVarRange.toNat = 0) (hc₂ : fe₂.data.looseBVarRange.toNat = 0)
    (hinf₁ : InferSpec L F ℓ G₀ fe₁ ft₁) (hinf₂ : InferSpec L F ℓ G₀ fe₂ ft₂) :
    FCtx.Extends G₀ G →
    DefEqSpec L F ℓ G₀ fe₁ fe₂ →
    DefEqSpec L F ℓ G fe₁ fe₂ := by
  intro hx h
  induction hx with
  | refl => exact h
  | push t hx ih =>
    have := hx.size_le
    exact ih.push t (by omega) (by omega) hc₁ hc₂
      (hinf₁.extend hr₁ hc₁ hx) (hinf₂.extend hr₂ hc₂ hx)

theorem InferSpec.fvar {G : FCtx} {i : Nat} (hi : i < G.size) :
    InferSpec L F ℓ G (.fvar i) G[i] := by
  intro ζ E n Γ e₀ hS hden
  have hn := hS.size
  subst hn
  exact ⟨_, _, .fvar (by simpa using hi), hS.ctx.get i hi, hS.wf.var _⟩

theorem InferSpec.sort {G : FCtx} (l : FLevel) :
    InferSpec L F ℓ G (.sort l) (.sort (.succ l)) :=
  fun {_ _ _ _ _} _ (.sort hl) => ⟨_, _, .sort hl, .sort (.succ hl), .sortDF⟩

theorem CheckSpec.ofInfer {G : FCtx} {fe te ft : FExpr} :
    InferSpec L F ℓ G fe te →
    TypeEqSpec L F ℓ G te ft →
    CheckSpec L F ℓ G fe ft :=
  fun he hconv {_ _ _ _ _ _} hS hed htd htt =>
    have ⟨_, _, hed', hte, hety⟩ := he hS hed
    ⟨_, hed', (hconv hS hte htd hety.regular htt).convStrong hety⟩

theorem TypedSpec.ofCheck {G : FCtx} {fe ft tt : FExpr} {l : FLevel} :
    InferSpec L F ℓ G ft tt →
    SortSpec L F ℓ G tt l →
    CheckSpec L F ℓ G fe ft →
    TypedSpec L F ℓ G fe ft :=
  fun htt hl hc {_ _ _ _ _ _} hS hed htd =>
    have ⟨_, _, htd', htt', hty⟩ := htt hS htd
    have ⟨_, _, hconv⟩ := hl hS htt' hty.regular
    have ⟨_, hed', hety⟩ := hc hS hed htd' ⟨_, hconv.convStrong hty⟩
    ⟨_, _, hed', htd', hety⟩

theorem InferSpec.app {G : FCtx} {f a tf t b : FExpr} :
    InferSpec L F ℓ G f tf →
    ForallSpec L F ℓ G tf t b →
    CheckSpec L F ℓ G a t →
    InferSpec L F ℓ G (.app f a) (FExpr.instAt a 0 b) :=
  fun hf hpi ha {_ _ _ _ _} hS (.app hfd had) =>
    have ⟨_, _, hfd', htf, hfty⟩ := hf hS hfd
    have ⟨_, _, ht₁, hb, hconv⟩ := hpi hS htf hfty.regular
    have hfty' := hconv.convStrong hfty
    have ⟨_, hty⟩ := hfty'.regular
    have hinv := hty.forallE_inv
    have ⟨_, had', haty⟩ := ha hS had ht₁ hinv.1
    have ⟨_, ht⟩ := hinv.1
    have ⟨_, ht'⟩ := hinv.2
    ⟨_, _, .app hfd' had', hb.inst had', .appDF ht ht' hfty' haty (ht'.inst_congr haty)⟩

theorem InferTeleSpec.base {G : FCtx} {k : Nat} {fe ty : FExpr} (hk : k ≤ G.size) :
    InferSpec L F ℓ G (fe.openBVars (G.size - k) k) ty →
    InferTeleSpec L F ℓ G k fe ty := by
  intro h ζ E n Γ e₀ hS hden
  have hn := hS.size
  subst hn
  have ⟨_, _, he, hty, hety⟩ := h hS (hden.openBVars (by omega))
  exact ⟨_, _, hden.unopenBVars (by omega) he, hty, hety⟩

theorem InferTeleSpec.baseSort {G : FCtx} {k : Nat} {fe tb : FExpr} {l : FLevel}
    (hk : k ≤ G.size) :
    InferSpec L F ℓ G (fe.openBVars (G.size - k) k) tb →
    SortSpec L F ℓ G tb l →
    InferTeleSpec L F ℓ G k fe (.sort l) := by
  intro h hl ζ E n Γ e₀ hS hden
  have hn := hS.size
  subst hn
  have ⟨_, _, he, htb, hety⟩ := h hS (hden.openBVars (by omega))
  have ⟨_, hl', hconv⟩ := hl hS htb hety.regular
  exact ⟨_, _, hden.unopenBVars (by omega) he, .sort hl', hconv.convStrong hety⟩

theorem InferTeleSpec.lam {G : FCtx} {k : Nat} {t b tt ty : FExpr} {l : FLevel}
    {ds : List FExpr} (hk : k ≤ G.size) :
    InferSpec L F ℓ G (t.openBVars (G.size - k) k) tt →
    SortSpec L F ℓ G tt l →
    InferTeleSpec L F ℓ (G.push (t.openBVars (G.size - k) k)) (k + 1) b
      (FExpr.mkPi (G.push (t.openBVars (G.size - k) k)).size ty ds) →
    InferTeleSpec L F ℓ G k (.lam t b)
      (FExpr.mkPi G.size ty (t.openBVars (G.size - k) k :: ds)) := by
  intro htt hl hr ζ E n Γ e₀ hS hden
  have hn := hS.size
  subst hn
  have .lam htd hbd := hden
  have ⟨_, _, hd', htt', htty⟩ := htt hS (htd.openBVars (by omega))
  have ⟨_, _, hconv⟩ := hl hS htt' htty.regular
  have hts := hconv.convStrong htty
  have ⟨_, _, hb', htb', hbty⟩ := hr (hS.snoc hd' hts) hbd
  have ⟨_, htb''⟩ := hbty.regular
  simp only [Array.size_push] at htb'
  exact ⟨_, _, .lam (htd.unopenBVars (by omega) hd') hb',
    .forallE hd' (htb'.abstractAt (by omega)), .lamDF hts htb'' htb'' hbty hbty⟩

theorem InferTeleSpec.pi {G : FCtx} {k : Nat} {t b tt : FExpr} {l₁ l₂ : FLevel}
    (hk : k ≤ G.size) :
    InferSpec L F ℓ G (t.openBVars (G.size - k) k) tt →
    SortSpec L F ℓ G tt l₁ →
    InferTeleSpec L F ℓ (G.push (t.openBVars (G.size - k) k)) (k + 1) b (.sort l₂) →
    InferTeleSpec L F ℓ G k (.forallE t b) (.sort (.imax l₁ l₂)) := by
  intro htt hl₁ hr ζ E n Γ e₀ hS hden
  have hn := hS.size
  subst hn
  have .forallE htd hbd := hden
  have ⟨_, _, hd', htt', htty⟩ := htt hS (htd.openBVars (by omega))
  have ⟨_, hl₁', hconv₁⟩ := hl₁ hS htt' htty.regular
  have hts := hconv₁.convStrong htty
  have ⟨_, _, hb', hs, hbs⟩ := hr (hS.snoc hd' hts) hbd
  have .sort hl₂' := hs
  exact ⟨_, _, .forallE (htd.unopenBVars (by omega) hd') hb', .sort (.imax hl₁' hl₂'),
    .forallEDF hts hbs hbs⟩

theorem TypedSpec.fixArgs {G : FCtx} {E : Env ζ} {n k : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hS : Sem L F G E Γ) {xs : Array FExpr} (hxs : xs.size = k) {fts : Fin k → FExpr}
    {e₀ : Fin k → Expr ζ ℓ n}
    (S : (Fin k → Expr ζ ℓ n) → Fin k → Expr ζ ℓ n)
    (he₀ : ∀ p, FExpr.Denotes L ⟨ζ, E⟩ 0 (xs[p.val]'(hxs.symm ▸ p.isLt)) (e₀ p))
    (hden : ∀ e : Fin k → Expr ζ ℓ n,
      (∀ p, FExpr.Denotes L ⟨ζ, E⟩ 0 (xs[p.val]'(hxs.symm ▸ p.isLt)) (e p)) →
      ∀ p, FExpr.Denotes L ⟨ζ, E⟩ 0 (fts p) (S e p))
    (hpre : ∀ (e : Fin k → Expr ζ ℓ n) (p : Fin k),
      (∀ q : Fin k, q < p → E[Γ] ⊢ₛ e q : S e q) → E[Γ] ⊢ₛ S e p typ)
    (htyped : ∀ p : Fin k, TypedSpec L F ℓ G (xs[p.val]'(hxs.symm ▸ p.isLt)) (fts p)) :
    ∃ e : Fin k → Expr ζ ℓ n,
      (∀ p, FExpr.Denotes L ⟨ζ, E⟩ 0 (xs[p.val]'(hxs.symm ▸ p.isLt)) (e p)) ∧
      ∀ p, E[Γ] ⊢ₛ e p : S e p := by
  have hex (p : Fin k) := htyped p hS (he₀ p) (hden e₀ he₀ p)
  choose e t hde hdt hty using hex
  refine ⟨e, hde, ?_⟩
  have key : ∀ N (p : Fin k), p.val < N → E[Γ] ⊢ₛ e p : S e p := by
    intro N
    induction N with
    | zero => exact fun p hp => absurd hp (Nat.not_lt_zero _)
    | succ N ih =>
      intro p hp
      have ⟨_, hSp⟩ := hpre e p fun q hq => ih q (by have := Fin.lt_def.mp hq; omega)
      have ⟨_, htp⟩ := (hty p).regular
      have heq := FExpr.Denotes.defeq hS.ordered hS.wf (hdt p) (hden e hde p) htp hSp
      exact (IsTypeEq.ofDefEq heq).convStrong (hty p)
  exact fun p => key (p.val + 1) p (Nat.lt_succ_self _)

theorem TypedSpec.at {G : FCtx} {fe ft : FExpr} {E : Env ζ} {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    {e₀ T : Expr ζ ℓ n} :
    TypedSpec L F ℓ G fe ft →
    Sem L F G E Γ →
    FExpr.Denotes L ⟨ζ, E⟩ 0 fe e₀ →
    FExpr.Denotes L ⟨ζ, E⟩ 0 ft T →
    E[Γ] ⊢ₛ T typ →
    ∃ e, FExpr.Denotes L ⟨ζ, E⟩ 0 fe e ∧ E[Γ] ⊢ₛ e : T := by
  intro h hS he₀ hT ⟨_, hTty⟩
  have ⟨_, _, hd, htd, hty⟩ := h hS he₀ hT
  have ⟨_, htty⟩ := hty.regular
  exact ⟨_, hd, (IsTypeEq.ofDefEq
    (FExpr.Denotes.defeq hS.ordered hS.wf htd hT htty hTty)).convStrong hty⟩

theorem Sem.eqBlock {G : FCtx} {E : Env ζ} {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hS : Sem L F G E Γ) (η : Head ζ .quot) :
    (E.get (E.get η).eqHead).block = Eq.block := by
  have h := hS.ordered.entryWFStrong η
  generalize E.get η = entry at h
  cases h with
  | quot heq => exact heq

theorem ForallSpec.refl {G : FCtx} (t b : FExpr) : ForallSpec L F ℓ G (.forallE t b) t b :=
  fun {_ _ _ _ _} _ (.forallE ht hb) hty => ⟨_, _, ht, hb, hty.isTypeEq⟩

theorem InferOnlySpec.app {G : FCtx} {f a tf t b : FExpr} :
    InferOnlySpec L F ℓ G f tf →
    ForallSpec L F ℓ G tf t b →
    InferOnlySpec L F ℓ G (.app f a) (FExpr.instAt a 0 b) :=
  fun hf hpi {_ _ _ _ _ _} hS (.app hfd had) he =>
    have ⟨_, _, hfty, haty, _⟩ := he.app_inv
    have ⟨_, htf, hfty'⟩ := hf hS hfd hfty
    have ⟨_, _, _, hb, hconv⟩ := hpi hS htf hfty'.regular
    have hfAB := hconv.convStrong hfty'
    have ⟨hdom, _⟩ := IsTypeEq.forallE_inj hS.ordered hS.wf
      (DefeqStrong.uniqTy hS.ordered hS.wf hfty hfAB)
    have haA := hdom.convStrong haty
    have ⟨_, hty⟩ := hfAB.regular
    have hinv := hty.forallE_inv
    have ⟨_, ht⟩ := hinv.1
    have ⟨_, ht'⟩ := hinv.2
    ⟨_, hb.inst had, .appDF ht ht' hfAB haA (ht'.inst_congr haA)⟩

theorem InferOnlySpec.appPending {G : FCtx} {f a t b : FExpr} {rev : List FExpr} :
    InferOnlySpec L F ℓ G f (FExpr.instManyRev rev (.forallE t b)) →
    InferOnlySpec L F ℓ G (.app f a) (FExpr.instManyRev (a :: rev) b) := by
  intro hf
  have ⟨t', heq, hinst⟩ := FExpr.instManyRev_cons_forallE rev a t b
  rw [heq] at hf
  rw [← hinst]
  exact hf.app (ForallSpec.refl _ _)

theorem InferOnlySpec.letE {G : FCtx} {t v b r : FExpr} :
    InferOnlySpec L F ℓ G (FExpr.instAt v 0 b) r →
    InferOnlySpec L F ℓ G (.letE t v b) r :=
  fun hr {_ _ _ _ _ _} hS (.letE _ hvd hbd) he =>
    have ⟨_, ⟨_, hts⟩, hvty, hbody, _⟩ := he.letE_inv hS.wf
    have ⟨_, hr', hbty⟩ := hr hS (hbd.inst hvd) hbody
    have ⟨_, hrs⟩ := hbty.regular
    ⟨_, hr', (DefeqStrong.zeta hts hvty hrs hbty).left⟩

theorem InferOnlySpec.letPending {G : FCtx} {t v b r : FExpr} {rev : List FExpr} :
    InferOnlySpec L F ℓ G (FExpr.instManyRev (FExpr.instManyRev rev v :: rev) b) r →
    InferOnlySpec L F ℓ G (FExpr.instManyRev rev (.letE t v b)) r := by
  intro hr
  have ⟨heq, hinst⟩ := FExpr.instManyRev_letE rev t v b
  rw [heq]
  rw [← hinst] at hr
  exact InferOnlySpec.letE hr

theorem InferSpec.toOnly {G : FCtx} {fe ft : FExpr} :
    InferSpec L F ℓ G fe ft →
    InferOnlySpec L F ℓ G fe ft :=
  fun h {_ _ _ _ _ _} hS hd he =>
    have ⟨_, _, hd', htd, hty⟩ := h hS hd
    ⟨_, htd, (FExpr.Denotes.defeq hS.ordered hS.wf hd' hd hty he).right⟩

theorem RedSpec.ofRed {G : FCtx} {fe₁ fe₂ : FExpr} :
    FWHRedS L F G.size fe₁ fe₂ →
    RedSpec L F ℓ G fe₁ fe₂ := by
  intro hr _ _ _ _ _ _ hS hd he
  have hn := hS.size
  subst hn
  have ⟨_, hd₂, hred⟩ := FWHRedS.denotes hS.env hr hd
  exact ⟨_, hd₂, WHRedS.defeq hS.ordered hS.wf hred he⟩

theorem RedSpec.refl {G : FCtx} (fe : FExpr) : RedSpec L F ℓ G fe fe :=
  fun {_ _ _ _ _ _} _ hd he => ⟨_, hd, he⟩

instance {G : FCtx} {fe₁ : FExpr} : Nonempty {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂} :=
  ⟨fe₁, RedSpec.refl fe₁⟩

theorem RedSpec.trans {G : FCtx} {fe₁ fe₂ fe₃ : FExpr} :
    RedSpec L F ℓ G fe₁ fe₂ →
    RedSpec L F ℓ G fe₂ fe₃ →
    RedSpec L F ℓ G fe₁ fe₃ := by
  intro h₁ h₂ _ _ _ _ _ _ hS hd he
  have ⟨_, hd₂, hc₁⟩ := h₁ hS hd he
  have ⟨_, hd₃, hc₂⟩ := h₂ hS hd₂ hc₁.right
  exact ⟨_, hd₃, hc₁.trans hc₂⟩

theorem RedSpec.frame {G : FCtx} {fe₁ fe₂ : FExpr} (K : FFrame) :
    RedSpec L F ℓ G fe₁ fe₂ →
    RedSpec L F ℓ G (K.plug fe₁) (K.plug fe₂) := by
  intro h ζ E n Γ e₁ t hS hd he
  obtain ⟨K', e₁'', rfl, hd₁, hK⟩ := FFrame.denotes hd
  have ⟨ft₁, ht₁⟩ : ∃ ft₁, E[Γ] ⊢ₛ e₁'' : ft₁ := by
    cases K' with
    | app fa =>
      have ⟨_, _, hf, _, _⟩ := he.app_inv
      exact ⟨_, hf⟩
    | recr =>
      have ⟨_, _, _, _, _, _, _, _, _, _, hmaj, _, _⟩ := he.recr_inv
      exact ⟨_, hmaj.right⟩
    | quotLift =>
      have ⟨_, _, _, _, _, _, _, _, _, _, _, ha, _⟩ := he.quotLift_prem
      exact ⟨_, ha.right⟩
    | quotInd =>
      have ⟨_, _, _, _, _, _, _, _, _, ha, _, _⟩ := he.quotInd_prem
      exact ⟨_, ha.right⟩
  have ⟨e₂, hd₂, hc₀⟩ := h hS hd₁ ht₁
  exact ⟨_, hK hd₂, K'.plug_defeq hS.ordered hS.wf
    (fun hf => DefeqStrong.retype hS.ordered hS.wf hc₀ hf) he⟩

theorem RedSpec.appList {G : FCtx} {fe₁ fe₂ : FExpr} (as : List FExpr) :
    RedSpec L F ℓ G fe₁ fe₂ →
    RedSpec L F ℓ G (FExpr.appList fe₁ as) (FExpr.appList fe₂ as) := by
  intro h
  induction as generalizing fe₁ fe₂ with
  | nil => exact h
  | cons a as ih => exact ih (h.frame (.app a))

theorem RedSpec.betaMany {G : FCtx} {f b : FExpr} {m : Nat} (as : List FExpr)
    (hm : m ≤ as.length) :
    FExpr.LamBody m f b →
    RedSpec L F ℓ G (FExpr.appList f as)
      (FExpr.appList (FExpr.instMany (as.take m) b) (as.drop m)) := by
  intro h
  have hlen : (as.take m).length = m := by simp [hm]
  have hβ := FWHRedS.appList (L := L) (F := F) (n := G.size) (as.drop m)
    (FWHRedS.betaMany (as := as.take m) (hlen ▸ h))
  have happ : FExpr.appList (FExpr.appList f (as.take m)) (as.drop m) = FExpr.appList f as := by
    simp [FExpr.appList, ← List.foldl_append]
  rw [happ] at hβ
  exact .ofRed hβ

theorem DefEqSpec.ofRedSpec {G : FCtx} {fe₁ fe₂ fe₃ fe₄ : FExpr} :
    RedSpec L F ℓ G fe₁ fe₃ →
    RedSpec L F ℓ G fe₂ fe₄ →
    DefEqSpec L F ℓ G fe₃ fe₄ →
    DefEqSpec L F ℓ G fe₁ fe₂ := by
  intro hr₁ hr₂ h _ _ _ _ _ _ _ _ hS hd₁ hd₂ he₁ he₂
  have ⟨_, hd₃, h₁⟩ := hr₁ hS hd₁ he₁
  have ⟨_, hd₄, h₂⟩ := hr₂ hS hd₂ he₂
  have hmid := h hS hd₃ hd₄ h₁.right h₂.right
  exact h₁.trans (hmid.trans (h₂.symm.retype hS.ordered hS.wf hmid.right))

theorem DefEqSpec.proj {G : FCtx} {pos s idx : Nat} {e₁ e₂ : FExpr} :
    DefEqSpec L F ℓ G e₁ e₂ →
    DefEqSpec L F ℓ G (.proj pos s idx e₁) (.proj pos s idx e₂) := by
  intro h _ _ _ _ _ _ _ _ hS hd₁ hd₂ he₁ he₂
  have .proj (f' := f₁) hstruct₁ hη₁ hs₁ hidx₁ hed₁ := hd₁
  have .proj (f' := f₂) hstruct₂ hη₂ hs₂ hidx₂ hed₂ := hd₂
  cases hη₂.symm.trans hη₁
  obtain rfl := Fin.ext (hs₂.trans hs₁.symm)
  exact Inductive.IsStructure.projTerm_congr_defeq hS.ordered hstruct₁ hstruct₂ f₁ f₂
    (hidx₁.trans hidx₂.symm) hS.wf he₁ he₂ fun ht₁ ht₂ => h hS hed₁ hed₂ ht₁ ht₂

theorem RedSpec.arg {G : FCtx} {ff a₁ a₂ : FExpr} :
    RedSpec L F ℓ G a₁ a₂ →
    RedSpec L F ℓ G (.app ff a₁) (.app ff a₂) := by
  intro h _ _ _ _ _ _ hS hd he
  have .app (f' := f) hf ha := hd
  have ⟨_, _, hfty, hay, ht⟩ := he.app_inv
  have ⟨_, hπ⟩ := hfty.regular
  have ⟨⟨_, ht₁⟩, ⟨_, ht₂⟩⟩ := hπ.forallE_inv
  have ⟨a₂', hd₂, hc⟩ := h hS ha hay
  exact ⟨.app f a₂', .app hf hd₂,
    ht.symm.convStrong (.appDF ht₁ ht₂ hfty hc (ht₂.inst_congr hc))⟩

theorem RedSpec.strLit {G : FCtx} (str : String) :
    RedSpec L F ℓ G (.strLit str) (FExpr.strLitExpand L str) :=
  fun {_ _ _ _ _ _} _ hd he => ⟨_, hd.ofStrLit, he⟩

theorem RedSpec.projCtor {G : FCtx} {pos pos₂ s s₂ idx c : Nat} {ls₂ : Array FLevel}
    {ps₂ fds recFds : Array FExpr} (hpos : pos₂ = pos) (hs : s₂ = s) (hidx : idx < fds.size) :
    RedSpec L F ℓ G (.proj pos s idx (.ctor pos₂ s₂ c ls₂ ps₂ fds recFds)) fds[idx] := by
  subst hpos hs
  intro ζ E n Γ e₁ t hS hd he
  have .proj (f' := f') hstruct hη hs hidx' hctor := hd
  have .ctor (s' := s₂) (c' := c₂) _ _ _ _ hη₂ hs₂ _ _ _ hfds _ := hctor
  cases hη₂.symm.trans hη
  obtain rfl := Fin.ext (hs₂.trans hs.symm)
  obtain rfl := hstruct.ctor_unique c₂
  subst hidx'
  exact ⟨_, hfds f', hstruct.projTerm_ctor_defeq hS.ordered f' hS.wf he⟩

theorem DefEqSpec.refl {G : FCtx} (fe : FExpr) : DefEqSpec L F ℓ G fe fe :=
  fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ =>
    FExpr.Denotes.defeq hS.ordered hS.wf hd₁ hd₂ he₁ he₂

theorem DefEqSpec.symm {G : FCtx} {fe₁ fe₂ : FExpr} :
    DefEqSpec L F ℓ G fe₁ fe₂ →
    DefEqSpec L F ℓ G fe₂ fe₁ := by
  intro h _ _ _ _ _ _ _ _ hS hd₂ hd₁ he₂ he₁
  exact (h hS hd₁ hd₂ he₁ he₂).symm.retype hS.ordered hS.wf he₂

theorem DefEqSpec.app {G : FCtx} {ff g fa fb : FExpr} :
    DefEqSpec L F ℓ G ff g →
    DefEqSpec L F ℓ G fa fb →
    DefEqSpec L F ℓ G (.app ff fa) (.app g fb) := by
  intro hf ha _ _ _ _ _ _ _ _ hS hd₁ hd₂ he₁ he₂
  have .app hdf hda := hd₁
  have .app hdg hdb := hd₂
  have ⟨_, _, hf', ha', hty₁⟩ := he₁.app_inv
  have ⟨_, _, hg', hb', _⟩ := he₂.app_inv
  have hfg := hf hS hdf hdg hf' hg'
  have hteq := DefeqStrong.uniqTy hS.ordered hS.wf hfg.right hg'
  have ⟨hdom, _⟩ := IsTypeEq.forallE_inj hS.ordered hS.wf hteq
  have hab := ha hS hda hdb ha' (hdom.symm.convStrong hb')
  have ⟨_, hpi⟩ := hf'.regular
  have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := hpi.forallE_inv
  exact hty₁.symm.convStrong (DefeqStrong.appDF ht ht' hfg hab (ht'.inst_congr hab))

theorem Sem.append {G ts : FCtx} {E : Env ζ} {n b : Nat} {Γ : Ctx ζ ℓ 0 n}
    {Δ : Ctx ζ ℓ n b} {P : Level ℓ → Prop} :
    Sem L F G E Γ →
    FCtx.Denotes L ⟨ζ, E⟩ ts Δ →
    WFTele E P Γ Δ →
    Sem L F (G ++ ts) E (Γ ++ Δ) := fun hS hΔ hwf =>
  ⟨hS.env, hS.ordered, hS.trust, hS.ctx.append hΔ, CtxWFStrong.append hS.ordered hS.wf hwf⟩

theorem TypeEqSpec.forallE {G : FCtx} {ft₁ ft₂ b₁ b₂ : FExpr}
    {E : Env ζ} {Γ : Ctx ζ ℓ 0 G.size} {e₁ e₂ t₁ t₂ : Expr ζ ℓ G.size} :
    TypeEqSpec L F ℓ G ft₁ ft₂ →
    TypeEqSpec L F ℓ (G.push ft₁) (FExpr.instAt (.fvar G.size) 0 b₁)
      (FExpr.instAt (.fvar G.size) 0 b₂) →
    Sem L F G E Γ →
    FExpr.Denotes L ⟨ζ, E⟩ 0 (.forallE ft₁ b₁) e₁ →
    FExpr.Denotes L ⟨ζ, E⟩ 0 (.forallE ft₂ b₂) e₂ →
    E[Γ] ⊢ₛ e₁ : t₁ →
    E[Γ] ⊢ₛ e₂ : t₂ →
    E[Γ] ⊢ₛ e₁ ≡ e₂ typ := by
  intro hdom hcod hS hd₁ hd₂ he₁ he₂
  have .forallE hdt₁ hb₁ := hd₁
  have .forallE hdt₂ hb₂ := hd₂
  have hinv₁ := he₁.forallE_inv
  have hinv₂ := he₂.forallE_inv
  have hd := hdom hS hdt₁ hdt₂ hinv₁.1 hinv₂.1
  have ⟨_, ht₁⟩ := hinv₁.1
  have ⟨u, hcl⟩ := hinv₂.2
  have hcod₁ : IsTypeStrong _ _ _ :=
    ⟨u, ((hd.symm.snocConv hS.ordered hS.wf).mp hcl.defeq).toStrongOrdered
      hS.ordered (hS.wf.snoc hinv₁.1)⟩
  exact hd.forallE_congr' hS.ordered hS.wf
    (hcod (hS.snoc hdt₁ ht₁) hb₁.instFVar hb₂.instFVar hinv₁.2 hcod₁)

theorem TypeEqTeleSpec.forallE {G : FCtx} {k : Nat} {ft₁ ft₂ b₁ b₂ : FExpr}
    (hk : k ≤ G.size) :
    TypeEqTeleSpec L F ℓ G k ft₁ ft₂ →
    TypeEqTeleSpec L F ℓ (G.push (ft₁.openBVars (G.size - k) k)) (k + 1) b₁ b₂ →
    TypeEqTeleSpec L F ℓ G k (.forallE ft₁ b₁) (.forallE ft₂ b₂) := by
  intro hdom hcod ζ E n Γ t₁ t₂ hS hd₁ hd₂ ⟨_, he₁⟩ ⟨_, he₂⟩
  have hn := hS.size
  subst hn
  have .forallE hdt₁ hb₁ := hd₁
  have .forallE hdt₂ hb₂ := hd₂
  have hinv₁ := he₁.forallE_inv
  have hinv₂ := he₂.forallE_inv
  have hd := hdom hS hdt₁ hdt₂ hinv₁.1 hinv₂.1
  have ⟨_, ht₁⟩ := hinv₁.1
  have ⟨u, hcl⟩ := hinv₂.2
  have hcod₁ : IsTypeStrong _ _ _ :=
    ⟨u, ((hd.symm.snocConv hS.ordered hS.wf).mp hcl.defeq).toStrongOrdered
      hS.ordered (hS.wf.snoc hinv₁.1)⟩
  exact hd.forallE_congr' hS.ordered hS.wf
    (hcod (hS.snoc (hdt₁.openBVars (by omega)) ht₁) hb₁ hb₂ hinv₁.2 hcod₁)

theorem TypeEqTeleSpec.toDefEq {G : FCtx} {ft₁ ft₂ b₁ b₂ : FExpr} :
    TypeEqTeleSpec L F ℓ G 0 (.forallE ft₁ b₁) (.forallE ft₂ b₂) →
    DefEqSpec L F ℓ G (.forallE ft₁ b₁) (.forallE ft₂ b₂) := by
  intro h ζ E n Γ e₁ e₂ t₁ t₂ hS hd₁ hd₂ he₁ he₂
  have .forallE hdt₁ hb₁ := hd₁
  have .forallE hdt₂ hb₂ := hd₂
  have ⟨⟨_, ht₁⟩, ⟨_, hc₁⟩⟩ := he₁.forallE_inv
  have ⟨⟨_, ht₂⟩, ⟨_, hc₂⟩⟩ := he₂.forallE_inv
  have ⟨_, hpi⟩ := (h hS (.forallE hdt₁ hb₁) (.forallE hdt₂ hb₂)
    ⟨_, .forallEDF ht₁ hc₁ hc₁⟩ ⟨_, .forallEDF ht₂ hc₂ hc₂⟩).sort_uniq hS.ordered hS.wf
  exact DefeqStrong.retype hS.ordered hS.wf hpi he₁

inductive Lazy (L : Literals) (F : FEnv) (ℓ : Nat) (G : FCtx) (fe₁ fe₂ : FExpr) where
  | eq (h : DefEqSpec L F ℓ G fe₁ fe₂)
  | stuck (e₁ e₂ : FExpr) (h₁ : RedSpec L F ℓ G fe₁ e₁) (h₂ : RedSpec L F ℓ G fe₂ e₂)

def Lazy.ofRed {G : FCtx} {fe₁ fe₂ fe₃ fe₄ : FExpr}
    (hr₁ : RedSpec L F ℓ G fe₁ fe₃)
    (hr₂ : RedSpec L F ℓ G fe₂ fe₄) :
    Lazy L F ℓ G fe₃ fe₄ →
    Lazy L F ℓ G fe₁ fe₂
  | .eq h => .eq (h.ofRedSpec hr₁ hr₂)
  | .stuck e₅ e₆ h₅ h₆ => .stuck e₅ e₆ (hr₁.trans h₅) (hr₂.trans h₆)

end

end Metalean.FastChecker
