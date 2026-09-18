/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Instantiate
import Metalean.Meta.DeriveFunctor
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean.FastChecker

abbrev FCtx := Array FExpr

instance (priority := high) : DecidableEq FCtx :=
  fun G₁ G₂ => withPtrEqDecEq G₁ G₂ fun _ => inferInstance

unsafe def FCtx.addrImpl (G : FCtx) : USize :=
  ptrAddrUnsafe G

@[implemented_by FCtx.addrImpl]
opaque FCtx.addr (G : FCtx) : USize

instance (priority := high) : Hashable FCtx :=
  ⟨fun G => hash G.addr⟩

inductive FCtx.Extends (G₀ : FCtx) : FCtx → Prop where
  | refl :
    FCtx.Extends G₀ G₀
  | push {G : FCtx} (t : FExpr) :
    FCtx.Extends G₀ G →
    FCtx.Extends G₀ (G.push t)

theorem FCtx.Extends.size_le {G₀ G : FCtx} :
    FCtx.Extends G₀ G →
    G₀.size ≤ G.size := by
  intro h
  induction h with
  | refl => rfl
  | push t _ ih => grind

structure FCtx.Ancestors (G : FCtx) where
  arr : Array FCtx
  size_le : arr.size ≤ G.size + 1
  spec : ∀ i (h : i < arr.size), i ≤ arr[i].size ∧ FCtx.Extends arr[i] G

def FCtx.Ancestors.cast {G₁ G₂ : FCtx} (h : G₁ = G₂) (a : FCtx.Ancestors G₁) : FCtx.Ancestors G₂ :=
  h ▸ a

def FCtx.Ancestors.root (G : FCtx) : FCtx.Ancestors G where
  arr := Array.replicate (G.size + 1) G
  size_le := by simp
  spec i h := by
    simp at h ⊢
    exact ⟨by omega, .refl⟩

def FCtx.Ancestors.push {G : FCtx} (a : FCtx.Ancestors G) (t : FExpr) (G' : FCtx)
    (hG : G' = G.push t) :
    FCtx.Ancestors G' where
  arr := a.arr.push G'
  size_le := by have := a.size_le; grind
  spec i h := by
    subst hG
    by_cases hi : i < a.arr.size
    · rw [Array.getElem_push_lt hi]
      exact ⟨(a.spec i hi).1, (a.spec i hi).2.push t⟩
    · obtain rfl : i = a.arr.size := by grind
      simp
      have := a.size_le
      exact ⟨by omega, .refl⟩

@[derive_functor E]
judgement FCtx.Denotes {ℓ a : Nat} (L : Literals) (E : Σ ζ, Env ζ) :
    FCtx → {b : Nat} → Ctx E.1 ℓ a b → Prop where

  ──────────────────── nil
  FCtx.Denotes L E #[] .nil

  FCtx.Denotes L E G Γ
  FExpr.Denotes L E 0 ft t
  ──────────────────── snoc {G : FCtx} {b} {Γ : Ctx E.1 ℓ a b} {ft t}
  FCtx.Denotes L E (G.push ft) (Γ.snoc t)

variable {E : Σ ζ, Env ζ} {L : Literals} {ℓ : Nat}

namespace FCtx.Denotes

theorem size {a b : Nat} {ts : Array FExpr} {Δ : Ctx E.1 ℓ a b} :
    FCtx.Denotes L E ts Δ →
    a + ts.size = b := by
  intro h
  induction h with
  | nil => rfl
  | snoc _ _ ih => simp; omega

theorem entry {a b p : Nat} {ts : Array FExpr} {Δ : Ctx E.1 ℓ a b} (hp : a ≤ p) (hp' : p < b) :
    (h : FCtx.Denotes L E ts Δ) →
    FExpr.Denotes L E 0 (ts[p - a]'(by have := h.size; omega)) (Δ.entry hp hp') := by
  intro h
  induction h with
  | nil => omega
  | @snoc ts b Δ ft t hΔ ht ih =>
    have hb := hΔ.size
    by_cases hpb : p = b
    · subst hpb
      simp
      grind
    · simp!
      grind

theorem ofFn {a k k' : Nat} (hk : k' = k) (Δ : Ctx E.1 ℓ a (a + k)) (f : Fin k' → FExpr) :
    (∀ i : Fin k',
      FExpr.Denotes L E 0 (f i) (Δ.entry (Nat.le_add_right a i.val) (by omega))) →
    FCtx.Denotes L E (Array.ofFn f) Δ := by
  intro hent
  subst hk
  induction Δ using Tele.addInduction with
  | nil =>
    simp
    exact .nil
  | snoc k Δ t ih =>
    rw [Array.ofFn_succ]
    refine .snoc (ih _ fun i => ?_) ?_
    · simpa using hent i.castSucc
    · simpa [Fin.last] using hent (Fin.last k)

theorem append {a b d : Nat} {ts ts' : Array FExpr} {Δ : Ctx E.1 ℓ a b} {Δ' : Ctx E.1 ℓ b d} :
    FCtx.Denotes L E ts Δ →
    FCtx.Denotes L E ts' Δ' →
    FCtx.Denotes L E (ts ++ ts') (Δ ++ Δ') := by
  intro h h'
  induction h' with
  | nil => exact h
  | snoc _ ht ih =>
    rw [Array.append_push]
    exact .snoc ih ht

theorem piTele {a b : Nat} {ts : Array FExpr} {Δ : Ctx E.1 ℓ a b} {fbody : FExpr}
    {body : Expr E.1 ℓ b} :
    FCtx.Denotes L E ts Δ →
    FExpr.Denotes L E 0 fbody body →
    FExpr.Denotes L E 0 (FExpr.piTele a ts fbody) (Ctx.pi body Δ) := by
  intro h hbody
  induction h generalizing fbody with
  | nil => exact hbody
  | @snoc ts b Δ ft t hΔ ht ih =>
    have hb := hΔ.size
    simp! [FExpr.piTele]
    rw [FExpr.teleAux_push _ a ts ft ts.size le_rfl]
    exact ih (.forallE ht (hbody.abstractAt (by omega)))

theorem lamTele {a b : Nat} {ts : Array FExpr} {Δ : Ctx E.1 ℓ a b} {fbody : FExpr}
    {body : Expr E.1 ℓ b} :
    FCtx.Denotes L E ts Δ →
    FExpr.Denotes L E 0 fbody body →
    FExpr.Denotes L E 0 (FExpr.lamTele a ts fbody) (Ctx.lam body Δ) := by
  intro h hbody
  induction h generalizing fbody with
  | nil => exact hbody
  | @snoc ts b Δ ft t hΔ ht ih =>
    have hb := hΔ.size
    simp! [FExpr.lamTele]
    rw [FExpr.teleAux_push _ a ts ft ts.size le_rfl]
    exact ih (.lam ht (hbody.abstractAt (by omega)))

theorem ofTypes {n k k' : Nat} (hk : k' = k) {tys : Fin k' → FExpr}
    {types : Fin k → Expr E.1 ℓ n} :
    (∀ i : Fin k', FExpr.Denotes L E 0 (tys i) (types (i.cast hk))) →
    FCtx.Denotes L E (Array.ofFn tys) (Ctx.ofTypes types) := by
  intro h
  subst hk
  exact FCtx.Denotes.ofFn rfl _ tys fun i => by
    rw [Ctx.entry_ofTypes]
    exact (h i).wkN i.val

theorem instTele {a m n k : Nat} {ts : Array FExpr} {Δ : Ctx E.1 a m (m + k)} {us : Array FLevel}
    {ls' : Fin a → RawLevel ℓ} (hus : us.size = a) {args : Array FExpr} {σ : Subst E.1 ℓ m n} :
    FCtx.Denotes L E ts Δ →
    (∀ i, FLevel.Denotes (us[i.val]'(hus.symm ▸ i.isLt)) (ls' i)) →
    ArgsDenote L E args σ →
    FCtx.Denotes L E
      (Array.ofFn fun j : Fin ts.size => (ts[j].instL us).instFVars (args ++ FExpr.fvars n j.val))
      ((Δ.instL (⟦ls' ·⟧)).substN σ k) := fun h hus' hargs =>
  FCtx.Denotes.ofFn (by have := h.size; lia) _ _ fun i => by
    have := h.size
    rw [Ctx.entry_substN (σ := σ) _ _ i.val (by omega) (by omega) (by omega) (by omega),
      ← Ctx.entry_instL]
    have := h.entry (p := m + i.val) (Nat.le_add_right m i.val) (by have := h.size; omega)
    simp only [Nat.add_sub_cancel_left] at this
    exact (this.instL hus hus').instFVars (hargs.liftN i.val)

theorem get {n : Nat} {G : FCtx} {Γ : Ctx E.1 ℓ 0 n} (i : Nat) (hi : i < n) :
    (h : FCtx.Denotes L E G Γ) →
    FExpr.Denotes L E 0 (G[i]'(by have := h.size; omega)) (Γ.get ⟨i, hi⟩) := by
  intro h
  induction h generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero i)
  | @snoc ts b Δ ft t hΔ ht ih =>
    have hsize : ts.size = b := by have := hΔ.size; omega
    simp only [Array.getElem_push, Ctx.get]
    by_cases hib : i = b
    · simp [hsize, hib]
      exact ht.wk
    · simp [hsize, show i < b by omega, hib]
      exact (ih i (by omega)).wk

theorem unique {a b : Nat} {G : FCtx} {Δ₁ Δ₂ : Ctx E.1 ℓ a b} :
    FCtx.Denotes L E G Δ₁ →
    FCtx.Denotes L E G Δ₂ →
    (∀ t ∈ G, t.NoProj) →
    Δ₁ = Δ₂ := by
  intro h₁ h₂ hnp
  obtain rfl := h₁.size
  exact Ctx.ext Δ₁ Δ₂ fun p hp hp' =>
    (h₁.entry hp hp').unique (h₂.entry hp hp') (hnp _ (Array.getElem_mem _))


theorem push_elim {a b : Nat} {G : FCtx} {ft : FExpr} {Δ : Ctx E.1 ℓ a b}
    {motive : {b : Nat} → Ctx E.1 ℓ a b → Prop}
    (h : FCtx.Denotes L E (G.push ft) Δ)
    (k : ∀ {b₀ : Nat} (Γ₀ : Ctx E.1 ℓ a b₀) (t : Expr E.1 ℓ b₀),
      FCtx.Denotes L E G Γ₀ → FExpr.Denotes L E 0 ft t → motive (Γ₀.snoc t)) :
    motive Δ := by
  generalize hG : G.push ft = G' at h
  cases h with
  | nil => exact absurd hG (by simp)
  | snoc hΓ ht =>
    obtain ⟨rfl, rfl⟩ := Array.push_eq_push.mp hG
    exact k _ _ hΓ ht

end FCtx.Denotes

end Metalean.FastChecker
