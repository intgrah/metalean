module

public import Metalean.Semantics.Domain.Decoder.Stages
public import Metalean.Semantics.Interpretation.Binder.Abstraction
public import Metalean.Semantics.Interpretation.Binder.Pi

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {Γ₁ Γ₂ Γ₃ ΓA ΓA' : CtxCat E ℓ} {σ₁ : Γ₂ ⟶ Γ₁} {f : ΓA' ⟶ ΓA}

namespace RawFamily

open CodeAssignment

def BodyAgreesOnFixed (hA' : Comprehension (Ty E ℓ) Γ₂ ΓA') (σ₁ : Γ₂ ⟶ Γ₁) (f : ΓA' ⟶ ΓA)
    (C : RawFamily Γ₁) (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₂ : Γ₃ ⟶ Γ₂) (ρ ρ' : RawValuation Γ₃) : Prop :=
  ∀ ⦃Γ₄ : CtxCat E ℓ⦄ (σ₃ : Γ₄ ⟶ Γ₃) (name : Tm_ Γ₄)
    (s : hA'.Section (σ₃ ≫ σ₂) name)
    (J : Domain Γ₄),
    (piLimit E ℓ).rawExtend
        (C.app _ ((σ₃ ≫ σ₂) ≫ σ₁).op (ρ.pullback σ₃)) name J.val = J.val →
    B.app _ (s.hom ≫ f).op ((ρ.pullback σ₃).push J.val) =
      B'.app _ s.hom.op ((ρ'.pullback σ₃).push J.val)

theorem normalizedBodyAction_substitution_eq_on_ideals
    (hA : Comprehension (Ty E ℓ) Γ₁ ΓA) (hA' : Comprehension (Ty E ℓ) Γ₂ ΓA')
    (hπ : IsPullback f hA'.disp hA.disp σ₁)
    (hq : (Tm E ℓ).map f.op hA.generic = hA'.generic)
    (C : RawFamily Γ₁) (C' : RawFamily Γ₂)
    (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₂ : Γ₃ ⟶ Γ₂) (ρ ρ' : RawValuation Γ₃)
    (hC : (C.app _ (σ₂ ≫ σ₁).op ρ).IsDirected)
    (hcode : C.app _ (σ₂ ≫ σ₁).op ρ = C'.app _ σ₂.op ρ')
    (hbody : BodyAgreesOnFixed hA' σ₁ f C B B' σ₂ ρ ρ')
    {Γ₄ : CtxCat E ℓ} (σ₃ : Γ₄ ⟶ Γ₃) (label : Tm_ Γ₄)
    (I : Domain Γ₄) :
    (normalizedBodyAction (piLimit E ℓ) hA C B (σ₂ ≫ σ₁) ρ).app _ (σ₃.op, label) I.val =
      (normalizedBodyAction (piLimit E ℓ) hA' C' B' σ₂ ρ').app _ (σ₃.op, label) I.val := by
  change sectionValue hA B (σ₃ ≫ σ₂ ≫ σ₁) (ρ.pullback σ₃) label
      ((piLimit E ℓ).rawExtend (C.app _ (σ₃ ≫ σ₂ ≫ σ₁).op (ρ.pullback σ₃)) label I.val) =
    sectionValue hA' B' (σ₃ ≫ σ₂) (ρ'.pullback σ₃) label
      ((piLimit E ℓ).rawExtend (C'.app _ (σ₃ ≫ σ₂).op (ρ'.pullback σ₃)) label I.val)
  rw [← Category.assoc]
  have hCυ : (C.app _ ((σ₃ ≫ σ₂) ≫ σ₁).op (ρ.pullback σ₃)).IsDirected := by
    rw [Category.assoc, op_comp, ← C.app_pullback]
    exact hC.pullback σ₃
  have hcodeυ : C.app _ ((σ₃ ≫ σ₂) ≫ σ₁).op (ρ.pullback σ₃) =
      C'.app _ (σ₃ ≫ σ₂).op (ρ'.pullback σ₃) := by
    rw [Category.assoc, op_comp, ← C.app_pullback, op_comp (g := σ₂), ← C'.app_pullback, hcode]
  have hbodyυ : BodyAgreesOnFixed hA' σ₁ f C B B' (σ₃ ≫ σ₂) (ρ.pullback σ₃) (ρ'.pullback σ₃) := by
    intro Γ₅ σ₄ name s J hfixed
    simp_rw [RawValuation.pullback_comp] at hfixed ⊢
    have hbody' := hbody (σ₄ ≫ σ₃) name
    rw [Category.assoc] at hbody'
    exact hbody' s J hfixed
  rw [← hcodeυ]
  apply (bodySection hA' B' (σ₃ ≫ σ₂) (ρ'.pullback σ₃) label _).eq_extend
  · intro Γ₅ σ₄ y hy hne
    have ⟨s⟩ := (bodySection hA B ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback σ₃) label _).support hy hne
    exact ⟨Section.lift (h := hA.isPullback) hπ hq {
      hom := s.hom
      over := s.over.trans (Category.assoc _ _ _).symm
      generic := s.generic }⟩
  · intro Γ₅ σ₄ s
    let t : hA.Section _ _ := s.map f (by rw [hπ.w, ← Category.assoc, s.over]) hq
    let t' : (sectionDomain hA ((σ₃ ≫ σ₂) ≫ σ₁) label).Witness σ₄ := {
      hom := t.hom
      over := t.over.trans (Category.assoc _ _ _)
      generic := t.generic }
    rw [sectionValue, (bodySection hA B ((σ₃ ≫ σ₂) ≫ σ₁) (ρ.pullback σ₃) label _).pullback_extend σ₄ t']
    have hCσ : (C.app _ ((σ₄ ≫ σ₃ ≫ σ₂) ≫ σ₁).op ((ρ.pullback σ₃).pullback σ₄)).IsDirected := by
      rw [Category.assoc, op_comp, ← C.app_pullback]
      exact hCυ.pullback σ₄
    change B.app _ (s.hom ≫ f).op (((ρ.pullback σ₃).pullback σ₄).push
        (((piLimit E ℓ).rawExtend (C.app _ ((σ₃ ≫ σ₂) ≫ σ₁).op (ρ.pullback σ₃)) label I.val).pullback σ₄)) =
      B'.app _ s.hom.op (((ρ'.pullback σ₃).pullback σ₄).push
        (((piLimit E ℓ).rawExtend (C.app _ ((σ₃ ≫ σ₂) ≫ σ₁).op (ρ.pullback σ₃)) label I.val).pullback σ₄))
    rw [(piLimit E ℓ).pullback_rawExtend, C.app_pullback, ← op_comp,
      ← Category.assoc σ₄ (σ₃ ≫ σ₂) σ₁]
    exact hbodyυ σ₄ ((Tm E ℓ).map σ₄.op label) s
      ⟨_, (piLimit E ℓ).rawExtend_isDirected _ hCσ (I.pullback σ₄).property⟩
      ((piLimit E ℓ).rawExtend_idempotent piLimit_isIdempotent _ hCσ (I.pullback σ₄).property)

end RawFamily

theorem rawPi_eq_of_eq_on_ideals (label : Ty.Pair Γ₁) (C : RawValue Γ₁)
    {F G : RawAction Γ₁}
    (h : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (name : Tm_ Γ₂)
      (I : Domain Γ₂),
      F.app _ (σ.op, name) I.val = G.app _ (σ.op, name) I.val) :
    rawPi label C F = rawPi label C G :=
  congrArg (BasisAction.pi label C) (RawAction.onBasis_eq_of_eq_on_ideals h)

namespace RawFamily

open CodeAssignment

theorem abstraction_substitution_eq
    (hA : Comprehension (Ty E ℓ) Γ₁ ΓA) (hA' : Comprehension (Ty E ℓ) Γ₂ ΓA')
    (hπ : IsPullback f hA'.disp hA.disp σ₁)
    (hq : (Tm E ℓ).map f.op hA.generic = hA'.generic)
    (C : RawFamily Γ₁) (C' : RawFamily Γ₂)
    (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₂ : Γ₃ ⟶ Γ₂) (ρ ρ' : RawValuation Γ₃)
    (hC : (C.app _ (σ₂ ≫ σ₁).op ρ).IsDirected)
    (hcode : C.app _ (σ₂ ≫ σ₁).op ρ = C'.app _ σ₂.op ρ')
    (hbody : BodyAgreesOnFixed hA' σ₁ f C B B' σ₂ ρ ρ') :
    (abstraction (piLimit E ℓ) hA C B).app _ (σ₂ ≫ σ₁).op ρ =
      (abstraction (piLimit E ℓ) hA' C' B').app _ σ₂.op ρ' :=
  RawAction.abstraction_eq_of_eq_on_ideals (normalizedBodyAction_substitution_eq_on_ideals
    hA hA' hπ hq C C' B B' σ₂ ρ ρ' hC hcode hbody)

theorem pi_substitution_eq
    (hA : Comprehension (Ty E ℓ) Γ₁ ΓA) (hA' : Comprehension (Ty E ℓ) Γ₂ ΓA')
    (hπ : IsPullback f hA'.disp hA.disp σ₁)
    (hq : (Tm E ℓ).map f.op hA.generic = hA'.generic)
    (label : Ty.Pair Γ₁) (C : RawFamily Γ₁) (C' : RawFamily Γ₂)
    (B : RawFamily ΓA)
    (B' : RawFamily ΓA')
    (σ₂ : Γ₃ ⟶ Γ₂) (ρ ρ' : RawValuation Γ₃)
    (hC : (C.app _ (σ₂ ≫ σ₁).op ρ).IsDirected)
    (hcode : C.app _ (σ₂ ≫ σ₁).op ρ = C'.app _ σ₂.op ρ')
    (hbody : BodyAgreesOnFixed hA' σ₁ f C B B' σ₂ ρ ρ') :
    (pi (piLimit E ℓ) hA label C B).app _ (σ₂ ≫ σ₁).op ρ =
      (pi (piLimit E ℓ) hA'
        ((Ty.pairPresheaf E ℓ).map σ₁.op label) C' B').app _ σ₂.op ρ' := by
  rw [pi_value, pi_value, op_comp, Functor.map_comp_apply, ← hcode]
  exact rawPi_eq_of_eq_on_ideals _ _ (normalizedBodyAction_substitution_eq_on_ideals hA hA' hπ hq C C'
    B B' σ₂ ρ ρ' hC hcode hbody)

end RawFamily

end Metalean.CoherentShape
