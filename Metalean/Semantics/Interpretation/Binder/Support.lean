/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Domain.Decoder.Stages
public import Metalean.Semantics.Interpretation.Binder.Basic
public import Metalean.Semantics.Interpretation.Family.Application
public import Metalean.TypeTheory.Syntactic.Comprehension
import Metalean.Strong
import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Interpretation.Binder.Abstraction

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ ΓA : CtxCat E ℓ}

theorem RawAction.rawApplication_abstraction_eq_value (F : RawAction Γ₁)
    (hF : F.IsFinitary) (hD : F.IsIdealValued)
    (X : Domain Γ₁)
    (Q : Set (Tm_ Γ₁)) (label : Tm_ Γ₁) (hlabel : label ∈ Q)
    (hsupport : ∀ {Γ₂} (σ : Γ₂ ⟶ Γ₁) (label' : Tm_ Γ₂),
      label' ∈ (Tm E ℓ).map σ.op '' Q →
      ∀ {x y : CoherentShape Γ₂},
      OutputAtom (F.abstraction.pullback σ) label' x y →
      y ≤ ⊥ ∨ label' = (Tm E ℓ).map σ.op label) :
    rawApplication F.abstraction Q X.val = F.app _ ((𝟙 Γ₁).op, label) X.val := by
  ext Γ₂ σ y
  let label' := (Tm E ℓ).map σ.op label
  let Y := F.app _ (σ.op, label') (X.pullback σ).val
  have hvalue : (F.app _ ((𝟙 Γ₁).op, label) X.val).mem σ y ↔ Y.mem (𝟙 Γ₂) y := by
    rw [← ΩLower.presheaf_map_mem_id, ← F.app_pullback, op_id, Category.id_comp]
    rfl
  rw [hvalue, mem_rawApplication]
  constructor
  · rintro (hbot | ⟨name, hname, u, x, hu, hx, x', hx', hy⟩)
    · exact Y.lower (𝟙 Γ₂) hbot (Y.bottom (𝟙 Γ₂))
    simp at hy
    apply hy.mem_of_outputAtom (hD σ label' (X.pullback σ))
    intro w hw'
    have hatom : OutputAtom (F.abstraction.pullback σ) ((Tm E ℓ).map σ.op name) x' w :=
      hw'.mono_function (ΩLower.principal_le_iff.mpr (by simpa using hu))
    rcases hsupport σ _ ⟨name, hname, rfl⟩ hatom with hbottom | hname'
    · exact Y.lower (𝟙 Γ₂) hbottom (Y.bottom (𝟙 Γ₂))
    rw [hname'] at hatom
    exact (F.app _ (σ.op, label')).hom.monotone
      (ΩLower.principal_le_iff.mpr
        ((X.pullback σ).lower (𝟙 Γ₂) (by simpa using hx') (by simpa using hx)))
      (𝟙 Γ₂) w (BasisAction.mem_value_of_outputAtom hatom)
  · intro hy
    have ⟨x, hx, hy'⟩ := hF.exists_principal σ label' (X.pullback σ) hy
    have ⟨g, e, hg, hlab, hin, hout⟩ := BasisAction.outputAtom_of_mem_value (F := F.onBasis) hy'
    exact Or.inr ⟨label, hlabel, g.lamGenerator, x, by simpa using hg, by simpa using hx,
      OutputAtom.mem_application ⟨g, e, by simp, hlab, hin, hout⟩ (by simp)⟩

namespace RawFamily

variable (D : CodeAssignment E ℓ)

theorem rawApplication_normalizedAbstraction_eq_value
    (hA : ℒ.Comprehension Γ₁ ΓA) (C : RawFamily Γ₁)
    {B : RawFamily ΓA} (hB : B.IsFinitary)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hD : (normalizedBodyAction D hA C B σ₁ ρ).IsIdealValued)
    (X : Domain Γ₂)
    (Q : Set (Tm_ Γ₂)) (label : Tm_ Γ₂) (hlabel : label ∈ Q)
    (hsections : ∀ {Γ₃} (σ₂ : Γ₃ ⟶ Γ₂) (label' : Tm_ Γ₃),
      label' ∈ (Tm E ℓ).map σ₂.op '' Q →
      Nonempty (hA.Section (σ₂ ≫ σ₁) label') →
      label' = (Tm E ℓ).map σ₂.op label) :
    rawApplication (normalizedBodyAction D hA C B σ₁ ρ).abstraction Q X.val =
      sectionValue hA B σ₁ ρ label (D.rawExtend (C.app _ σ₁.op ρ) label X.val) := by
  have hcollapse := RawAction.rawApplication_abstraction_eq_value
    (normalizedBodyAction D hA C B σ₁ ρ)
    (normalizedBodyAction_isFinitary D hA C hB σ₁ ρ) hD X Q label hlabel (by
      intro Γ₃ σ₂ label' hlabel' x y hy
      by_cases hbottom : y ≤ ⊥
      · exact Or.inl hbottom
      · exact Or.inr (hsections σ₂ label' hlabel'
          (sectionValue_support hA B (σ₂ ≫ σ₁) (ρ.pullback σ₂) label' _
            (BasisAction.mem_value_of_outputAtom hy) hbottom)))
  change _ = sectionValue hA B (𝟙 _ ≫ σ₁) (ρ.pullback (𝟙 _)) label
    (D.rawExtend (C.app _ (𝟙 _ ≫ σ₁).op (ρ.pullback (𝟙 _))) label X.val) at hcollapse
  simpa using hcollapse

variable {t e : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}

theorem sourceQuery_eq_of_section (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (he : E[Γ₁.as.ctx] ⊢ₛ e : t) (σ : Γ₂ ⟶ Γ₁) {label : Tm_ Γ₂}
    (hlabel : label ∈ (Tm E ℓ).map σ.op '' sourceQuery Γ₁ e)
    (hs : Nonempty (Raw.ContextSection ht σ label)) :
    label = (Tm E ℓ).map σ.op (Tm.label Γ₁.as he) := by
  obtain ⟨_, ⟨t₁, he₁, rfl⟩, rfl⟩ := hlabel
  have ⟨s⟩ := hs
  have htype := s.type_eq
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  rw [Equiv.apply_symm_apply] at htype
  change Ty.ofTyping Γ₂.as (he₁.substitution σ.typed).regular.choose_spec =
    (Ty E ℓ).map (RawCtx.toCtx.map σ).op (Ty.ofTyping Γ₁.as ht) at htype
  rw [Ty.map_ofTyping] at htype
  exact Tm.label_eq ((Ty.ofTyping_eq_iff Γ₂.as _ _).mp htype) (he₁.substitution σ.typed)

theorem rawApplication_eq_of_sections (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (he : E[Γ₁.as.ctx] ⊢ₛ e : t) (σ₁ : Γ₂ ⟶ Γ₁) (F X : Domain Γ₂)
    (hsupport : ∀ {Γ₃ : CtxCat E ℓ} (σ₂ : Γ₃ ⟶ Γ₂) (name : Tm_ Γ₃)
      {x y : CoherentShape Γ₃}, OutputAtom (F.pullback σ₂).val name x y →
        y ≤ ⊥ ∨ Nonempty (Raw.ContextSection ht (σ₂ ≫ σ₁) name)) :
    rawApplication F.val ((Tm E ℓ).map σ₁.op '' sourceQuery Γ₁ e) X.val =
      (CoherentShape.application F ((Tm E ℓ).map σ₁.op (Tm.label Γ₁.as he)) X).val :=
  rawApplication_eq_of_support F X _ ⟨Tm.label Γ₁.as he, label_mem_sourceQuery he, rfl⟩
    fun {_} σ₂ name hname _ _ hy => (hsupport σ₂ name hy).imp_right fun hs => by
      rw [← Functor.map_comp_apply]
      exact sourceQuery_eq_of_section ht he (σ₂ ≫ σ₁) (by simpa using hname) hs

theorem rawApplication_singleton_abstraction_eq_body
    (hA : ℒ.Comprehension Γ₁ ΓA) (C : RawFamily Γ₁)
    {B : RawFamily ΓA} (hB : B.IsFinitary) (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (hD : (normalizedBodyAction D hA C B σ₁ ρ).IsIdealValued) (X : Domain Γ₂)
    {label : Tm_ Γ₂} (sect : hA.Section σ₁ label) :
    rawApplication (normalizedBodyAction D hA C B σ₁ ρ).abstraction {label} X.val =
      B.app _ sect.hom.op (ρ.push (D.rawExtend (C.app _ σ₁.op ρ) label X.val)) := by
  rw [rawApplication_normalizedAbstraction_eq_value D hA C hB σ₁ ρ hD X {label} label rfl
    fun σ₂ label' hlabel' _ => by simpa using hlabel']
  exact sectionValue_eq_value hA B σ₁ ρ label _ sect

end RawFamily

end Metalean.CoherentShape
