/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Judgment
import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Interpretation.Computation
import Metalean.Semantics.Interpretation
import Metalean.Semantics.Soundness.Context.Transport
import Metalean.Semantics.Soundness.Rules.Core
import Metalean.Semantics.Soundness.Rules.Function

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment Presheaf

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}
  {η : Head ζ .quot} {u v : Level ℓ}
  {α α' r r' β β' f f' h h' a a₁ a₂ : Expr ζ ℓ Γ₁.as.len}

theorem rawInterpret_quotMk_app (ha : E[Γ₁.as.ctx] ⊢ₛ a : α) (σ : Γ₂ ⟶ Γ₁)
    (ρ : RawValuation Γ₂) :
    (rawInterpret (piLimit E ℓ) Γ₁ (.quotMk η u α r a)).app _ σ.op ρ =
      bif u.rel then
        RawValue.quotMk η ((Tm E ℓ).map σ.op (Tm.label Γ₁.as ha))
          ((rawInterpret (piLimit E ℓ) Γ₁ a).app _ σ.op ρ)
      else ⊥ := by
  cases hu : u.rel
  · rw [rawInterpret_quotMk_prop _ hu]
    rfl
  · rw [rawInterpret_quotMk _ ha hu]
    rfl

theorem rawInterpret_quotLift_app (hlift : E[Γ₁.as.ctx] ⊢ₛ .quotLift η u v α r β f h a : β)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (rawInterpret (piLimit E ℓ) Γ₁ (.quotLift η u v α r β f h a)).app _ σ.op ρ =
      (piLimit E ℓ).rawExtend ((rawInterpret (piLimit E ℓ) Γ₁ β).app _ σ.op ρ)
        ((Tm E ℓ).map σ.op (Tm.label Γ₁.as hlift))
        (bif u.rel then
          rawQuotLift (piLimit E ℓ) η ((rawInterpret (piLimit E ℓ) Γ₁ α).app _ σ.op ρ)
            ((rawInterpret (piLimit E ℓ) Γ₁ f).app _ σ.op ρ)
            ((rawInterpret (piLimit E ℓ) Γ₁ a).app _ σ.op ρ)
        else
          rawProofApplication ((Ty E ℓ).map σ.op (Ty.ofTyping Γ₁.as (QuotTyping.ofLift hlift).carrier))
            ((rawInterpret (piLimit E ℓ) Γ₁ f).app _ σ.op ρ)) := by
  cases hu : u.rel
  · rw [rawInterpret_quotLift_proof _ hlift hu (QuotTyping.ofLift hlift).carrier]
    rfl
  · rw [rawInterpret_quotLift_typed _ hlift hu]
    rfl

theorem HasFixedness.quot (h : QuotTyping Γ₁ u α r) :
    HasFixedness Γ₁ (.quot η u α r) (.sort u) := fun _ _ σ ρ _ => by
  rw [rawInterpret_sort, RawFamily.sort_value, rawInterpret_quot _ h, RawFamily.quot_value,
    rawExtend_toLower, piLimit_extend_sort]
  exact congrArg Subtype.val (universeIdeal_principal (Shape.IsCode.quot _ rfl))

namespace RawInterpretationProperties

theorem quot (h : QuotTyping Γ₁ u α r) : RawInterpretationProperties Γ₁ (.quot η u α r) where
  ideal _ σ ρ _ := by
    rw [rawInterpret_quot _ h, RawFamily.quot_value]
    exact (principalIdeal _).property
  subst _ _ σ₁ σ₂ _ _ _ _ := by
    change (rawInterpret (piLimit E ℓ) _ (.quot η u (α.subst σ₁.subst) (r.subst σ₁.subst))).app _
      σ₂.op _ = _
    rw [rawInterpret_quot _ (h.subst σ₁), rawInterpret_quot _ h, RawFamily.quot_value,
      RawFamily.quot_value, QuotCode.map_comp_hom, h.code_map]

theorem quotMk (ha : E[Γ₁.as.ctx] ⊢ₛ a : α) (pa : RawInterpretationProperties Γ₁ a) :
    RawInterpretationProperties Γ₁ (.quotMk η u α r a) where
  ideal _ σ ρ hρ := by
    rw [rawInterpret_quotMk_app ha]
    cases u.rel
    · exact ΩLower.isDirected_bot
    · exact RawValue.quotMk_isDirected _ _ (pa.ideal σ ρ hρ)
  subst _ _ σ₁ σ₂ ρ₁ ρ₂ hσ hρ := by
    change (rawInterpret (piLimit E ℓ) _
      (.quotMk η u (α.subst σ₁.subst) (r.subst σ₁.subst) (a.subst σ₁.subst))).app _ σ₂.op ρ₂ = _
    rw [rawInterpret_quotMk_app (ha.substitution σ₁.typed), rawInterpret_quotMk_app ha,
      pa.subst σ₁ σ₂ ρ₁ ρ₂ hσ hρ, op_comp, Functor.map_comp_apply, Tm.map_label]

theorem quotLift (hlift : E[Γ₁.as.ctx] ⊢ₛ .quotLift η u v α r β f h a : β)
    (pα : RawInterpretationProperties Γ₁ α) (pβ : RawInterpretationProperties Γ₁ β)
    (pf : RawInterpretationProperties Γ₁ f) (pa : RawInterpretationProperties Γ₁ a) :
    RawInterpretationProperties Γ₁ (.quotLift η u v α r β f h a) where
  ideal _ σ ρ hρ := by
    rw [rawInterpret_quotLift_app hlift]
    apply (piLimit E ℓ).rawExtend_isDirected _ (pβ.ideal σ ρ hρ)
    cases hu : u.rel
    · exact RawFamily.proofApplication_isDirected
        (Tm.subsingleton_of_prop _ (by simpa using hu)) _ σ ρ (pf.ideal σ ρ hρ)
    · exact rawQuotLift_isDirected _ _ (pα.ideal σ ρ hρ) (pf.ideal σ ρ hρ) (pa.ideal σ ρ hρ)
  subst _ _ σ₁ σ₂ ρ₁ ρ₂ hσ hρ := by
    change (rawInterpret (piLimit E ℓ) _ (.quotLift η u v (α.subst σ₁.subst) (r.subst σ₁.subst)
      (β.subst σ₁.subst) (f.subst σ₁.subst) (h.subst σ₁.subst) (a.subst σ₁.subst))).app _
        σ₂.op ρ₂ = _
    rw [rawInterpret_quotLift_app (hlift.substitution σ₁.typed), rawInterpret_quotLift_app hlift,
      pα.subst σ₁ σ₂ ρ₁ ρ₂ hσ hρ, pβ.subst σ₁ σ₂ ρ₁ ρ₂ hσ hρ, pf.subst σ₁ σ₂ ρ₁ ρ₂ hσ hρ,
      pa.subst σ₁ σ₂ ρ₁ ρ₂ hσ hρ, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    rfl

theorem quotInd (η : Head ζ .quot) (u : Level ℓ) (α r β f a : Expr ζ ℓ Γ₁.as.len) :
    RawInterpretationProperties Γ₁ (.quotInd η u α r β f a) where
  ideal _ _ _ _ := by
    rw [rawInterpret_quotInd]
    exact ΩLower.isDirected_bot
  subst _ _ _ _ _ _ _ _ := by
    simp only [Expr.subst, rawInterpret_quotInd]
    rfl

end RawInterpretationProperties

namespace RawJudgment

theorem quotDF :
    RawJudgment Γ₁ α α' (.sort u) →
    RawJudgment Γ₁ r r' (Quot.relType α) →
    RawJudgment Γ₁ (.quot η u α r) (.quot η u α' r') (.sort u) := by
  intro pα pr
  have h := QuotTyping.left pα.syntactic pr.syntactic
  have h' := QuotTyping.right pα.syntactic pr.syntactic
  exact {
    syntactic := .quotDF pα.syntactic pr.syntactic
    type := RawInterpretationProperties.sort Γ₁ u
    left := RawInterpretationProperties.quot h
    right := RawInterpretationProperties.quot h'
    equal _ _ _ _ := by
      rw [rawInterpret_quot _ h, rawInterpret_quot _ h', h.code_congr pα.syntactic pr.syntactic h' η]
    fixed := HasFixedness.quot h }

theorem quotMkDF :
    RawJudgment Γ₁ α α' (.sort u) →
    RawJudgment Γ₁ r r' (Quot.relType α) →
    RawJudgment Γ₁ a₁ a₂ α →
    RawJudgment Γ₁ (.quotMk η u α r a₁) (.quotMk η u α' r' a₂) (.quot η u α r) := by
  intro pα pr pa
  have h := QuotTyping.left pα.syntactic pr.syntactic
  have ha₁ := pa.syntactic.left
  have ha₂ : E[Γ₁.as.ctx] ⊢ₛ a₂ : α' := .defeqDF pα.syntactic pa.syntactic.right
  exact {
    syntactic := .quotMkDF pα.syntactic pr.syntactic pa.syntactic
    type := RawInterpretationProperties.quot h
    left := RawInterpretationProperties.quotMk ha₁ pa.left
    right := RawInterpretationProperties.quotMk ha₂ pa.right
    equal _ σ ρ hρ := by
      rw [rawInterpret_quotMk_app ha₁, rawInterpret_quotMk_app ha₂, pa.equal σ ρ hρ,
        Tm.label_eq (.ofDefEq pα.syntactic) pa.syntactic]
    fixed _ _ σ ρ _ := by
      rw [rawInterpret_quotMk_app ha₁, rawInterpret_quot _ h, RawFamily.quot_value]
      cases hrel : u.rel
      · exact rawExtend_bottom_payload piLimit_isPayloadStrict _ _
      · rw [piLimit_rawExtend_quot _ hrel]
        exact RawValue.quotProjection_quotMk _ _ _ }

theorem quotLiftDF :
    RawJudgment Γ₁ α α' (.sort u) →
    RawJudgment Γ₁ r r' (Quot.relType α) →
    RawJudgment Γ₁ β β' (.sort v) →
    RawJudgment Γ₁ f f' (.forallE α β.wk) →
    RawJudgment Γ₁ h h' (Quot.compatType (E.get η).eqHead v α r β f) →
    RawJudgment Γ₁ a₁ a₂ (.quot η u α r) →
    RawJudgment Γ₁ (.quotLift η u v α r β f h a₁) (.quotLift η u v α' r' β' f' h' a₂) β := by
  intro pα pr pβ pf ph pa
  have hsyn : E[Γ₁.as.ctx] ⊢ₛ .quotLift η u v α r β f h a₁ ≡
      .quotLift η u v α' r' β' f' h' a₂ : β :=
    .quotLiftDF pα.syntactic pr.syntactic pβ.syntactic pf.syntactic ph.syntactic pa.syntactic
  have hl' : E[Γ₁.as.ctx] ⊢ₛ .quotLift η u v α' r' β' f' h' a₂ : β' :=
    .defeqDF pβ.syntactic hsyn.right
  exact {
    syntactic := hsyn
    type := pβ.left
    left := RawInterpretationProperties.quotLift hsyn.left pα.left pβ.left pf.left pa.left
    right := RawInterpretationProperties.quotLift hl' pα.right pβ.right pf.right pa.right
    equal _ σ ρ hρ := by
      rw [rawInterpret_quotLift_app hsyn.left, rawInterpret_quotLift_app hl', pα.equal σ ρ hρ,
        pβ.equal σ ρ hρ, pf.equal σ ρ hρ, pa.equal σ ρ hρ,
        Tm.label_eq (.ofDefEq pβ.syntactic) hsyn,
        show Ty.ofTyping Γ₁.as pα.syntactic.left = Ty.ofTyping Γ₁.as pα.syntactic.right from
          Quotient.sound (IsTypeEq.ofDefEq pα.syntactic)]
    fixed _ _ σ ρ hρ := by
      rw [rawInterpret_quotLift_app hsyn.left]
      apply (piLimit E ℓ).rawExtend_idempotent piLimit_isIdempotent _ (pβ.left.ideal σ ρ hρ)
      cases hu : u.rel
      · exact RawFamily.proofApplication_isDirected
          (Tm.subsingleton_of_prop _ (by simpa using hu)) _ σ ρ (pf.left.ideal σ ρ hρ)
      · exact rawQuotLift_isDirected _ _ (pα.left.ideal σ ρ hρ) (pf.left.ideal σ ρ hρ) (pa.left.ideal σ ρ hρ) }

theorem quotIndDF :
    RawJudgment Γ₁ α α' (.sort u) →
    RawJudgment Γ₁ r r' (Quot.relType α) →
    RawJudgment Γ₁ β β' (Quot.motiveType η u α r) →
    RawJudgment Γ₁ f f' (Quot.minorType η u α r β) →
    RawJudgment Γ₁ a₁ a₂ (.quot η u α r) →
    RawJudgment Γ₁ (.app β a₁) (.app β' a₂) .prop →
    RawJudgment Γ₁ (.quotInd η u α r β f a₁) (.quotInd η u α' r' β' f' a₂) (.app β a₁) := by
  intro pα pr pβ pf pa presult
  exact {
    syntactic := .quotIndDF pα.syntactic pr.syntactic pβ.syntactic pf.syntactic pa.syntactic
      presult.syntactic
    type := presult.left
    left := RawInterpretationProperties.quotInd η u α r β f a₁
    right := RawInterpretationProperties.quotInd η u α' r' β' f' a₂
    equal _ := by simp
    fixed _ _ _ _ _ := by
      rw [rawInterpret_quotInd]
      exact rawExtend_bottom_payload piLimit_isPayloadStrict _ _ }

theorem quotIota :
    RawJudgment Γ₁ α α (.sort u) →
    RawJudgment Γ₁ r r (Quot.relType α) →
    RawJudgment Γ₁ β β (.sort v) →
    RawJudgment Γ₁ f f (.forallE α β.wk) →
    RawJudgment Γ₁ h h (Quot.compatType (E.get η).eqHead v α r β f) →
    RawJudgment Γ₁ a a α →
    RawJudgment Γ₁ (.app f a) (.app f a) β →
    RawJudgment Γ₁ (.quotLift η u v α r β f h (.quotMk η u α r a)) (.app f a) β := by
  intro pα pr pβ pf ph pa prhs
  have plhs := (quotLiftDF pα pr pβ pf ph (quotMkDF (η := η) pα pr pa)).leftRefl
  have hiota := DefeqStrong.quotIota pα.syntactic pr.syntactic pβ.syntactic pf.syntactic
    ph.syntactic pa.syntactic plhs.syntactic prhs.syntactic
  refine of_typings hiota plhs prhs fun _ σ ρ hρ => ?_
  have hα := pα.syntactic.left
  have ha := pa.syntactic.left
  have happ := (pf.toRawTyped.app hα (pβ.syntactic.left.wk α)
    (pβ.left.wk hα) pa.toRawTyped (by simpa using pβ.left)).2 σ ρ hρ
  rw [← rawApplication_singleton] at happ
  rw [rawInterpret_quotLift_app plhs.syntactic, rawInterpret_quotMk_app ha,
    Tm.label_eq (he₂ := prhs.syntactic) (.ofDefEq pβ.syntactic) hiota,
    ← prhs.fixed prhs.syntactic σ ρ hρ, happ]
  congr 1
  cases hu : u.rel
  · obtain rfl : u = .zero := by simpa using hu
    have hαfixed := pα.fixed hα σ ρ hρ
    rw [rawInterpret_sort] at hαfixed
    have hbottom : (rawInterpret (piLimit E ℓ) Γ₁ a).app _ σ.op ρ = ⊥ :=
      (pa.fixed ha σ ρ hρ).symm.trans (piLimit_rawExtend_prop _ hαfixed _ _)
    change _ = rawApplication ((rawInterpret (piLimit E ℓ) Γ₁ f).app _ σ.op ρ) _
      ((rawInterpret (piLimit E ℓ) Γ₁ a).app _ σ.op ρ)
    rw [hbottom, ← RawFamily.proofApplication_eq (Tm.subsingleton_of_prop hα rfl) _
      (Tm.label Γ₁.as ha) rfl]
    rfl
  · change rawQuotLift (piLimit E ℓ) η (hρ.eval pα.left.ideal).val (hρ.eval pf.left.ideal).val
      (RawValue.quotMk η _ (hρ.eval pa.left.ideal).val) = _
    rw [rawQuotLift_quotMk]
    change _ = rawApplication _ _ ((rawInterpret (piLimit E ℓ) Γ₁ a).app _ σ.op ρ)
    rw [← pa.fixed ha σ ρ hρ]
    rfl

end RawJudgment

end Metalean.CoherentShape
