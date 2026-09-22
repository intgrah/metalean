/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Judgment
import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Soundness.Rules.Core

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ : CtxCat E ℓ} {nlevels : Nat} {u : Level ℓ}

open CategoryTheory CodeAssignment Presheaf

theorem RawJudgment.delta (η : Head ζ (.const .def nlevels)) {ls : Fin nlevels → Level ℓ}
    (p : RawJudgment (CtxCat.nil E ℓ) ((E.get η).defValue.instL ls)
      ((E.get η).defValue.instL ls) ((E.get η).constType.instL ls))
    (pt : RawJudgment Γ₁ ((E.get η).constType.instL ls).wkClosed
      ((E.get η).constType.instL ls).wkClosed (.sort u)) :
    RawJudgment Γ₁ (.const η ls) ((E.get η).defValue.instL ls).wkClosed
      ((E.get η).constType.instL ls).wkClosed := by
  have hσ : SemanticHom (⟨Fin.elim0, fun v => v.elim0⟩ : Γ₁.as ⟶ (CtxCat.nil E ℓ).as) :=
    ⟨fun v => v.elim0, fun _ _ ρ _ => ⟨ρ, .nil _ _ _ _, .nil _ _⟩⟩
  have pv := hσ.props p.left
  have hf : HasFixedness Γ₁ _ _ := hσ.fixed p.syntactic.left p.type.subst p.left.subst p.fixed
  simp only [Expr.subst_closed] at pv hf
  have hdelta : E[Γ₁.as.ctx] ⊢ .const η ls ≡ ((E.get η).defValue.instL ls).wkClosed :
      ((E.get η).constType.instL ls).wkClosed :=
    .delta pt.syntactic p.syntactic.left.wkClosed
  refine ⟨hdelta, pt.left, ⟨fun _ σ ρ hρ => ?_, fun _ _ σ₁ σ₂ ρ₁ ρ₂ hσ₁ hρ => ?_⟩, pv,
    fun _ _ _ _ => by rw [rawInterpret_const_def], fun _ he σ ρ hρ => ?_⟩
  · rw [rawInterpret_const_def]
    exact pv.ideal σ ρ hρ
  · change (rawInterpret (piLimit E ℓ) _ (.const η ls)).app _ σ₂.op ρ₂ = _
    rw [rawInterpret_const_def, rawInterpret_const_def, ← pv.subst σ₁ σ₂ ρ₁ ρ₂ hσ₁ hρ,
      Expr.wkClosed_subst]
  · rw [rawInterpret_const_def,
      Tm.label_eq (IsType.typeEq he.regular) hdelta]
    exact hf hdelta.right σ ρ hρ

theorem RawJudgment.const_bot {kind : ConstKind} (η : Head ζ (.const kind nlevels))
    {ls : Fin nlevels → Level ℓ}
    (hbot : ∀ Γ : CtxCat E ℓ, rawInterpret (piLimit E ℓ) Γ (.const η ls) = ⊥)
    (pt : RawJudgment Γ₁ ((E.get η).constType.instL ls).wkClosed
      ((E.get η).constType.instL ls).wkClosed (.sort u)) :
    RawJudgment Γ₁ (.const η ls) (.const η ls) ((E.get η).constType.instL ls).wkClosed :=
  have pc : RawInterpretationProperties Γ₁ (.const η ls) := by
    refine ⟨fun _ _ _ _ => ?_, fun _ _ _ σ₂ _ _ _ _ => ?_⟩
    · rw [hbot]
      exact ΩLower.isDirected_bot
    · change (rawInterpret (piLimit E ℓ) _ (.const η ls)).app _ σ₂.op _ = _
      rw [hbot, hbot]
      rfl
  { syntactic := .constDF pt.syntactic
    type := pt.left
    left := pc
    right := pc
    equal := HasEquality.refl _ _
    fixed := fun _ _ _ _ _ => by
      rw [hbot]
      exact rawExtend_bottom_payload piLimit_isPayloadStrict _ _ }

end Metalean.CoherentShape
