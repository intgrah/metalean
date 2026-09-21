/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Context.Transport
import Metalean.Semantics.Interpretation.Computation
import Metalean.Semantics.Interpretation

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ : CtxCat E ℓ} {t e e₁ e₂ p r : Expr ζ ℓ Γ₁.as.len}
  {e' : Expr ζ ℓ (Γ₁.as.len + 1)} {u : Level ℓ}

open CodeAssignment Presheaf

theorem HasIdeality.sort (Γ : CtxCat E ℓ) (u : Level ℓ) : HasIdeality Γ (.sort u) := by
  intro _ σ ρ _
  rw [rawInterpret_sort]
  exact (principalIdeal (sortAtom u : CoherentShape _)).property

theorem HasFixedness.sort (Γ : CtxCat E ℓ) (u : Level ℓ) : HasFixedness Γ (.sort u) (.sort u.succ) :=
  fun _ _ σ ρ _ ↦ rawInterpret_sort_fixed u σ ρ _

theorem RawInterpretationProperties.sort (Γ : CtxCat E ℓ) (u : Level ℓ) :
    RawInterpretationProperties Γ (.sort u) :=
  ⟨HasIdeality.sort Γ u, HasSubstitution.sort Γ u⟩

theorem HasEquality.beta (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (he : E[Γ₁.as.ctx] ⊢ₛ e : t)
    (htI : HasIdeality Γ₁ t) (heI' : HasIdeality (CtxCat.extension Γ₁ ht) e')
    (heI : HasIdeality Γ₁ e) (heF : HasFixedness Γ₁ e t) (heR : HasSubstitution Γ₁ e)
    (heS' : HasSubstitution (CtxCat.extension Γ₁ ht) e') :
    HasEquality Γ₁ (.app (.lam t e') e) (e'.inst e) :=
  fun _ σ ρ hρ => rawInterpret_beta (piLimit E ℓ) ht he σ ρ
    (RawFamily.bodyAction_isIdealValued ht htI heI' σ ρ hρ) (heI σ ρ hρ) (heF he σ ρ hρ)
    (HasSubstitution.instantiate ht he htI heI heF heR heS' σ ρ hρ)

theorem HasEquality.proofIrrel (hpt : E[Γ₁.as.ctx] ⊢ₛ p : .sort .zero)
    (he₁ : E[Γ₁.as.ctx] ⊢ₛ e₁ : p) (he₂ : E[Γ₁.as.ctx] ⊢ₛ e₂ : p)
    (hp : HasFixedness Γ₁ p (.sort .zero)) (hf₁ : HasFixedness Γ₁ e₁ p)
    (hf₂ : HasFixedness Γ₁ e₂ p) : HasEquality Γ₁ e₁ e₂ :=
  fun _ σ ρ hρ ↦ by
    have hpσ := hp hpt σ ρ hρ
    rw [rawInterpret_sort] at hpσ
    exact (hf₁ he₁ σ ρ hρ).symm.trans ((piLimit_rawExtend_prop _ hpσ _ _).trans
      ((piLimit_rawExtend_prop _ hpσ _ _).symm.trans (hf₂ he₂ σ ρ hρ)))

theorem RawInterpretationProperties.letE (pinst : RawInterpretationProperties Γ₁ (e'.inst e)) :
    RawInterpretationProperties Γ₁ (.letE t e e') where
  ideal _ σ ρ hρ := by
    rw [rawInterpret_letE]
    exact pinst.ideal σ ρ hρ
  subst _ _ σ₁ σ₂ ρ₁ ρ₂ hσ hρ := by
    simpa [Expr.subst, Expr.inst_subst] using pinst.subst σ₁ σ₂ ρ₁ ρ₂ hσ hρ

namespace RawJudgment

theorem of_typings :
    E[Γ₁.as.ctx] ⊢ₛ e₁ ≡ e₂ : t →
    RawJudgment Γ₁ e₁ e₁ t →
    RawJudgment Γ₁ e₂ e₂ t →
    HasEquality Γ₁ e₁ e₂ →
    RawJudgment Γ₁ e₁ e₂ t :=
  fun hsyn pe₁ pe₂ heq ↦ ⟨hsyn, pe₁.type, pe₁.left, pe₂.left, heq, pe₁.fixed⟩

theorem leftRefl (h : RawJudgment Γ₁ e₁ e₂ t) : RawJudgment Γ₁ e₁ e₁ t :=
  ⟨h.syntactic.left, h.type, h.left, h.left, HasEquality.refl Γ₁ e₁, h.fixed⟩

theorem var (pΓ : RawTeleProperties E .nil Γ₁.as.ctx) (v : Var Γ₁.as.len) :
    RawJudgment Γ₁ (.var v) (.var v) (Γ₁.as.ctx.get v) := by
  have p : RawTyped Γ₁ (.var v) (Γ₁.as.ctx.get v) := by
    convert pΓ.var (Γ₁ := CtxCat.nil E ℓ) Γ₁.as.wf.wfTeleStrong v (Nat.zero_le _) using 1 <;>
      simp [CtxCat.extendTele, CtxCat.nil]
  exact ⟨p.typed, p.type, p.term, p.term, HasEquality.refl Γ₁ _, p.fixed⟩

theorem sort (Γ : CtxCat E ℓ) (u : Level ℓ) :
    RawJudgment Γ (.sort u) (.sort u) (.sort u.succ) :=
  ⟨.sortDF, .sort Γ u.succ, .sort Γ u, .sort Γ u, HasEquality.refl Γ _, HasFixedness.sort Γ u⟩

theorem zeta {l : Level ℓ} :
    RawJudgment Γ₁ t t (.sort l) →
    RawJudgment Γ₁ e e t →
    RawJudgment Γ₁ (e'.inst e) (e'.inst e) r →
    RawJudgment Γ₁ (.letE t e e') (e'.inst e) r := by
  intro pt pe pinst
  have hzeta : HasEquality Γ₁ (.letE t e e') (e'.inst e) := fun _ _ _ ↦ by simp
  have hsyn := DefeqStrong.zeta pt.syntactic pe.syntactic pinst.syntactic.regular.choose_spec
    pinst.syntactic
  exact ⟨hsyn, pinst.type, .letE pinst.left, pinst.left, hzeta,
    HasEquality.fixed_right (HasEquality.symm hzeta) hsyn.symm pinst.fixed⟩

theorem proofIrrel :
    RawJudgment Γ₁ t t (.sort .zero) →
    RawJudgment Γ₁ e₁ e₁ t →
    RawJudgment Γ₁ e₂ e₂ t →
    RawJudgment Γ₁ e₁ e₂ t :=
  fun pt pe₁ pe₂ ↦ of_typings (.proofIrrel pt.syntactic pe₁.syntactic pe₂.syntactic) pe₁ pe₂
    (HasEquality.proofIrrel pt.syntactic.left pe₁.syntactic.left pe₂.syntactic.left pt.fixed
      pe₁.fixed pe₂.fixed)

end RawJudgment

end Metalean.CoherentShape
