/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Realization
import Metalean.Syntax.Substitution

public section

universe u

namespace Metalean

open ZFSet

variable {ζ : Sigs} {ℓ : Nat} {ε : Atom ζ ℓ → ZFSet} {ν : Param ℓ → Nat}
  {n : Nat} {Γ : Ctx ζ ℓ 0 n} {γ : Slots n}

@[expose] def SemCtx (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat)
    (γ : Slots n) (Γ : Ctx ζ ℓ 0 n) : Prop :=
  ∀ v, γ v ∈ ε[ν; γ]⟦Γ.get v⟧

notation:65 ε:max "[" ν "]" " ⊨ " γ " : " Γ:lead => SemCtx ε ν γ Γ

theorem SemCtx.nil {γ : Slots 0} : ε[ν] ⊨ γ : #t[] := nofun

theorem SemCtx.snoc {t : Expr ζ ℓ n} {x : ZFSet}
    (hΓ : ε[ν] ⊨ γ : Γ) (hx : x ∈ ε[ν; γ]⟦t⟧) :
    ε[ν] ⊨ γ.snoc x : Γ.snoc t := by
  intro v
  cases v using Fin.lastCases with
  | last => simpa using hx
  | cast v => simpa using hΓ v

theorem Realizes.semCtx {reach : Set (Slots 0)} {Δ : SemTele 0 n}
    (h : Realizes ε ν reach Γ Δ) (γ : Slots n) (hγ : γ ∈ Reachable reach Δ) :
    ε[ν] ⊨ γ : Γ := by
  induction h with
  | nil => exact SemCtx.nil
  | snoc _ hdomain ih =>
    have .snoc hprefix hlast := hγ
    rw [← hdomain _ hprefix] at hlast
    simpa using (ih (Fin.init γ) hprefix).snoc hlast

theorem Realizes.reachable_of_semCtx
    {a b : Nat} {Γ : Ctx ζ ℓ 0 a} {reach : Set (Slots a)}
    {Δsyn : Ctx ζ ℓ a b} {Δsem : SemTele a b}
    (h : Realizes ε ν reach Δsyn Δsem)
    (γ : Slots b) (hγ : ε[ν] ⊨ γ : (Γ ++ Δsyn))
    (hbase : (fun base => γ (base.castLE Δsem.le)) ∈ reach) :
    γ ∈ Reachable reach Δsem :=
  h.reachable_subst Subst.id γ hbase (fun _ => rfl) fun slot _ => by
    simpa using hγ slot

theorem Expr.denote_lam_mem_pi {b : Nat} {Δ : Ctx ζ ℓ n b} {body leaf : Expr ζ ℓ b}
    (hleaf : ∀ slots ∈ Reachable {γ} (Δ.denote ε ν),
      ε[ν; slots]⟦body⟧ ∈ ε[ν; slots]⟦leaf⟧) :
    ε[ν; γ]⟦Ctx.lam body Δ⟧ ∈ ε[ν; γ]⟦Ctx.pi leaf Δ⟧ := by
  rw [Realizes.denotes_lam rfl (fun _ _ => rfl) Realizes.denote,
    Realizes.denotes_pi rfl (fun _ _ => rfl) Realizes.denote]
  exact Reachable.lam_mem_pi hleaf γ rfl

structure SemDefeq (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat) (γ : Slots n)
    (e₁ e₂ t : Expr ζ ℓ n) : Prop where
  eq : ε[ν; γ]⟦e₁⟧ = ε[ν; γ]⟦e₂⟧
  mem : ε[ν; γ]⟦e₁⟧ ∈ ε[ν; γ]⟦t⟧

notation:65 ε:max "[" ν "; " γ "]" " ⊨ " e₁ " ≡ " e₂ " : " t:lead => SemDefeq ε ν γ e₁ e₂ t
notation:65 ε:max "[" γ "]" " ⊨ " e₁ " ≡ " e₂ " : " t:lead => SemDefeq ε zeroNs γ e₁ e₂ t

namespace SemDefeq

variable {e₁ e₂ e₃ t : Expr ζ ℓ n}

theorem symm :
    ε[ν; γ] ⊨ e₁ ≡ e₂ : t →
    ε[ν; γ] ⊨ e₂ ≡ e₁ : t
  | ⟨heq, hmem⟩ => ⟨heq.symm, heq ▸ hmem⟩

theorem trans :
    ε[ν; γ] ⊨ e₁ ≡ e₂ : t →
    ε[ν; γ] ⊨ e₂ ≡ e₃ : t →
    ε[ν; γ] ⊨ e₁ ≡ e₃ : t
  | ⟨heq₁, hmem₁⟩, ⟨heq₂, _⟩ => ⟨heq₁.trans heq₂, hmem₁⟩

theorem reachable {m : Nat} {Δsyn : Ctx ζ ℓ 0 m}
    {Δsem : SemTele 0 m} {left right : Fin m → Expr ζ ℓ n}
    (hrealizes : Realizes ε ν Set.univ Δsyn Δsem)
    (hargs : ∀ f, ε[ν; γ] ⊨ left f ≡ right f : (Ctx.get f Δsyn).subst left) :
    (ε[ν; γ]⟦left ·⟧) ∈ Reachable Set.univ Δsem :=
  hrealizes.reachable_subst (Γ := .nil) left (ε[ν; γ]⟦left ·⟧) trivial (fun _ => rfl)
    fun f _ => by simpa using (hargs f).mem

end SemDefeq

theorem Realizes.slot_interp
    {a b : Nat} {Γ : Ctx ζ ℓ 0 a} {reach : Set (Slots a)}
    {Δsyn : Ctx ζ ℓ a b} {Δsem : SemTele a b}
    (h : Realizes ε ν reach Δsyn Δsem)
    {n : Nat} {γ₂ : Slots n} (σ₁ : Subst ζ ℓ b n) (γ₁ : Slots b)
    (hreach : γ₁ ∈ Reachable reach Δsem)
    (hσ : ∀ v, ε[ν; γ₂]⟦σ₁ v⟧ = γ₁ v)
    (v : Fin b) (hv : a ≤ v.val) :
    ε[ν; γ₂] ⊨ σ₁ v ≡ σ₁ v : (Ctx.get v (Γ ++ Δsyn)).subst σ₁ := by
  induction h generalizing n with
  | nil => have := v.isLt; omega
  | @snoc scope Δsyn Δsem t domain _ hdomain ih =>
    have hprefix := Reachable.init hreach
    let σ₂ : Subst ζ ℓ scope n := Subst.wk.comp σ₁
    cases v using Fin.lastCases with
    | last =>
      refine ⟨rfl, ?_⟩
      rw [Tele.append_snoc, Ctx.get_last, Expr.wk_subst,
        Expr.denote_subst, show (ε[ν; γ₂]⟦σ₂ ·⟧) = Fin.init γ₁ from
          funext fun w => hσ w.castSucc, hdomain _ hprefix, hσ]
      exact Reachable.last hreach
    | cast v =>
      rw [Tele.append_snoc, Ctx.get_castSucc, Expr.wk_subst]
      exact ih σ₂ (Fin.init γ₁) hprefix (fun w => hσ w.castSucc) v hv

end Metalean
