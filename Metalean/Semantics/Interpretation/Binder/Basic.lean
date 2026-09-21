/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Subfunctor.Image
public import Metalean.CategoryTheory.Functor.FunctorHom
public import Metalean.Order.Presheaf.Partial
public import Metalean.Semantics.Domain.Decoder.Extension
public import Metalean.Semantics.Interpretation.Family.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Finite
import Metalean.Semantics.Interpretation.Family.Substitution

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Opposite MonoidalCategory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ ΓA : CtxCat E ℓ}

abbrev RawActionFamily (Γ₁ : CtxCat E ℓ) :=
  Functor.HomObj (RawValuation.presheaf E ℓ) (RawAction.presheaf E ℓ)
    (coyoneda.obj (op (op Γ₁)))

noncomputable instance {Γ₁ : CtxCat E ℓ} : PartialOrder (RawActionFamily Γ₁) :=
  inferInstanceAs (PartialOrder (Functor.HomObj _ _ _))

noncomputable instance {Γ₁ : CtxCat E ℓ} : SupSet (RawActionFamily Γ₁) := ⟨fun S => {
  app X σ := Preord.ofHom {
    toFun ρ := (⨆ B ∈ S, B.app X σ ρ : RawAction X.unop)
    monotone' ρ ρ' h :=
      have hmono : ∀ B ∈ S, B.app X σ ρ ≤ B.app X σ ρ' :=
        fun B _ => (B.app X σ).hom.monotone h
      iSup₂_mono hmono }
  naturality f σ := Preord.ext fun ρ => by
    change (⨆ B ∈ S, B.app _ (σ ≫ f) (ρ.pullback f.unop) : RawAction _) =
      (RawAction.presheaf E ℓ).map f (⨆ B ∈ S, B.app _ σ ρ)
    rw [RawAction.map_iSup]
    refine iSup_congr fun B => ?_
    rw [RawAction.map_iSup]
    exact iSup_congr fun _ => B.naturality_apply f σ ρ }⟩

namespace RawActionFamily

theorem app_sSup {Γ₁ : CtxCat E ℓ} (S : Set (RawActionFamily Γ₁)) (X : (CtxCat E ℓ)ᵒᵖ)
    (σ : op Γ₁ ⟶ X) (ρ : RawValuation X.unop) :
    (sSup S).app X σ ρ = ⨆ B ∈ S, B.app X σ ρ := rfl

@[simp] theorem iSup_app {ι : Sort*} {Γ₁ : CtxCat E ℓ} (B : ι → RawActionFamily Γ₁)
    (X : (CtxCat E ℓ)ᵒᵖ) (σ : op Γ₁ ⟶ X) (ρ : RawValuation X.unop) :
    (⨆ i, B i).app X σ ρ = ⨆ i, (B i).app X σ ρ := by
  change (sSup (Set.range B)).app X σ ρ = _
  rw [app_sSup, iSup_range]

end RawActionFamily

noncomputable instance {Γ₁ : CtxCat E ℓ} : CompleteLattice (RawActionFamily Γ₁) where
  bot := {
    app _ _ := Preord.ofHom (OrderHom.const _ ⊥)
    naturality f _ := Preord.ext fun _ => RawAction.ext fun _ _ _ => rfl }
  bot_le B := fun X σ ρ => @bot_le (RawAction X.unop) _ _ (B.app X σ ρ)
  __ := completeLatticeOfSup (RawActionFamily Γ₁) fun S => by
    constructor
    · intro B hB X σ ρ
      apply le_iSup₂_of_le B hB le_rfl
    · intro B hB X σ ρ
      apply iSup₂_le
      intro C hC
      apply hB hC

variable (D : CodeAssignment E ℓ)

namespace RawFamily

def sectionDomain (hA : ℒ.Comprehension Γ₁ ΓA)
    (σ₁ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂) : PartialDomain Γ₂ where
  Witness σ₂ := hA.Section (σ₂ ≫ σ₁) ((Tm E ℓ).map σ₂.op label)
  pullback s σ₂ := {
    hom := σ₂ ≫ s.hom
    over := by simp [s.over]
    generic := by simp [s.generic] }

noncomputable def bodySection (hA : ℒ.Comprehension Γ₁ ΓA)
    (B : RawFamily ΓA)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (label : Tm_ Γ₂)
    (I : RawValue Γ₂) : PartialSection (pointedOrder E ℓ) (sectionDomain hA σ₁ label) where
  value σ₂ s := B.app _ s.hom.op ((ρ.pullback σ₂).push (I.pullback σ₂))
  natural σ₂ σ₃ s t := by
    rw [B.app_pullback, RawValuation.pullback_push, RawValuation.pullback_comp,
      ΩLower.pullback_pullback]
    have h : σ₃ ≫ s.hom = t.hom := Section.hom_eq ((sectionDomain hA σ₁ label).pullback s σ₃) t
    rw [← op_comp, h]

noncomputable def sectionValue (hA : ℒ.Comprehension Γ₁ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (label : Tm_ Γ₂)
    (I : RawValue Γ₂) : RawValue Γ₂ :=
  (bodySection hA B σ ρ label I).extend

@[simp] theorem mem_sectionValue
    (hA : ℒ.Comprehension Γ₁ ΓA) (B : RawFamily ΓA)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (label : Tm_ Γ₂)
    (I : RawValue Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) (y : CoherentShape Γ₃) :
    (sectionValue hA B σ₁ ρ label I).mem σ₂ y ↔ y ≤ ⊥ ∨
      ∃ s : hA.Section (σ₂ ≫ σ₁) ((Tm E ℓ).map σ₂.op label),
        (B.app _ s.hom.op ((ρ.pullback σ₂).push (I.pullback σ₂))).mem (𝟙 Γ₃) y :=
  Iff.rfl

theorem sectionValue_eq_value (hA : ℒ.Comprehension Γ₁ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (label : Tm_ Γ₂)
    (I : RawValue Γ₂) (s : hA.Section σ label) :
    sectionValue hA B σ ρ label I = B.app _ s.hom.op (ρ.push I) := by
  let s' : (sectionDomain hA σ label).Witness (𝟙 Γ₂) := {
    hom := s.hom
    over := by simpa using s.over
    generic := by simpa using s.generic }
  simpa [sectionValue, bodySection] using
    (bodySection hA B σ ρ label I).pullback_extend (𝟙 Γ₂) s'

theorem sectionValue_mono (hA : ℒ.Comprehension Γ₁ ΓA)
    {B B' : RawFamily ΓA} (hB : B ≤ B') (σ₁ : Γ₂ ⟶ Γ₁) {ρ ρ' : RawValuation Γ₂} (hρ : ρ ≤ ρ') (label : Tm_ Γ₂)
    {I I' : RawValue Γ₂} (hI : I ≤ I') :
    sectionValue hA B σ₁ ρ label I ≤ sectionValue hA B' σ₁ ρ' label I' := by
  apply PartialSection.extend_mono
  intro Γ₃ σ₂ s _ f a ha
  exact (B'.app _ s.hom.op).hom.monotone
    (RawValuation.push_mono (RawValuation.pullback_mono hρ σ₂) (ΩLower.pullback_mono hI σ₂)) f a
    (hB _ s.hom.op _ f a ha)

noncomputable def bodyHom (hA : ℒ.Comprehension Γ₁ ΓA) (B : RawFamily ΓA) :
    Functor.HomObj ((RawValuation.presheaf E ℓ) ⊗ ΩLower.presheaf (pointedOrder E ℓ))
      (ΩLower.presheaf (pointedOrder E ℓ)) (coyoneda.obj (op (op Γ₁)) ⊗ (Tm E ℓ)) where
  app _ := fun (σ₁, label) => Preord.ofHom {
    toFun := fun (ρ, I) => sectionValue hA B σ₁.unop ρ label I
    monotone' := by
      rintro ⟨ρ, I⟩ ⟨ρ', I'⟩ ⟨hρ, hI⟩
      exact sectionValue_mono hA le_rfl σ₁.unop hρ label hI }
  naturality := by
    rintro ⟨Γ₂⟩ ⟨Γ₃⟩ ⟨σ₂⟩ ⟨⟨σ₁⟩, label⟩
    apply Preord.ext
    intro ⟨ρ, I⟩
    change (_ : RawValue Γ₃) = _
    ext Γ₄ σ₃ (y : CoherentShape Γ₄)
    change (sectionValue hA B (σ₂ ≫ σ₁) (ρ.pullback σ₂)
      ((Tm E ℓ).map σ₂.op label) (I.pullback σ₂)).mem σ₃ y ↔
        ((sectionValue hA B σ₁ ρ label I).pullback σ₂).mem σ₃ y
    rw [ΩLower.presheaf_map_mem, mem_sectionValue, mem_sectionValue,
      Category.assoc, op_comp, Functor.map_comp_apply,
      RawValuation.pullback_comp, ΩLower.pullback_pullback]

theorem sectionValue_finitary (hA : ℒ.Comprehension Γ₁ ΓA)
    {B : RawFamily ΓA} (hB : B.IsFinitary)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (label : Tm_ Γ₂) :
    ΩLower.IsFinitary (sectionValue hA B σ ρ label) := by
  intro I y hy
  simp_rw [mem_sectionValue] at hy ⊢
  rcases hy with hy | ⟨s, hy⟩
  · exact ⟨∅, by simp, Or.inl hy⟩
  · simp at hy
    have ⟨l, hl, hy⟩ := hB.head s.hom ρ I hy
    exact ⟨l, hl, Or.inr ⟨s, by simpa using hy⟩⟩

theorem sectionValue_support (hA : ℒ.Comprehension Γ₁ ΓA)
    (B : RawFamily ΓA)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (label : Tm_ Γ₂)
    (I : RawValue Γ₂) {y : CoherentShape Γ₂}
    (hy : (sectionValue hA B σ ρ label I).mem (𝟙 Γ₂) y)
    (hne : ¬ y ≤ ⊥) :
    Nonempty (hA.Section σ label) := by
  simpa [sectionDomain] using (bodySection hA B σ ρ label I).support hy hne

end RawFamily

namespace RawActionFamily

noncomputable def normalizedBody
    (hA : ℒ.Comprehension Γ₁ ΓA) (C : RawFamily Γ₁) (B : RawFamily ΓA) : RawActionFamily Γ₁ :=
  let f : Functor.HomObj ((RawValuation.presheaf E ℓ) ⊗ ΩLower.presheaf (pointedOrder E ℓ))
      (ΩLower.presheaf (pointedOrder E ℓ)) (coyoneda.obj (op (op Γ₁)) ⊗ (Tm E ℓ)) :=
    (Functor.HomObj.fst.pair
      (((Functor.HomObj.fst.comp (C.map { app _ := ↾Prod.fst })).pair .snd).comp
        (D.rawExtendHom.map { app _ := ↾Prod.snd }))).comp (RawFamily.bodyHom hA B)
  let p : (RawAction.arguments E ℓ) ⊗ (((RawValuation.presheaf E ℓ) ⋙ forget Preord) ⊗ coyoneda.obj (op (op Γ₁))) ⟶
      (ΩLower.presheaf (pointedOrder E ℓ) ⋙ forget Preord) :=
    { app _ := ↾fun ((label, I), ρ, σ₁) => ((ρ, I), σ₁, label) } ≫
      Functor.homObjEquiv _ _ _ f.toTypes
  let q := Subfunctor.lift (MonoidalClosed.curry p) (by
    rintro X _ ⟨⟨ρ, σ₁⟩, rfl⟩ Y σ₂ label
    exact (f.app Y (σ₁ ≫ σ₂, label)).hom.monotone.comp
      ((monotone_const (β := RawValuation Y.unop)).prodMk (β := RawValue Y.unop) monotone_id))
  ((Functor.homObjEquiv _ _ _).symm q).ofTypes (by
    intro X σ₁ ρ ρ' h Y ⟨σ₂, label⟩ I
    exact (f.app Y (σ₁ ≫ σ₂, label)).hom.monotone
      ⟨RawValuation.pullback_mono h σ₂.unop, by rfl⟩)

end RawActionFamily

namespace RawFamily

noncomputable def normalizedBodyAction (hA : ℒ.Comprehension Γ₁ ΓA)
    (C : RawFamily Γ₁) (B : RawFamily ΓA)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) : RawAction Γ₂ :=
  (RawActionFamily.normalizedBody D hA C B).app _ σ.op ρ

theorem normalizedBodyAction_mono (hA : ℒ.Comprehension Γ₁ ΓA)
    {C C' : RawFamily Γ₁} (hC : C ≤ C') {B B' : RawFamily ΓA} (hB : B ≤ B')
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    normalizedBodyAction D hA C B σ ρ ≤ normalizedBodyAction D hA C' B' σ ρ :=
  fun _ p _ => sectionValue_mono hA hB (p.1.unop ≫ σ) le_rfl p.2
    (D.rawExtend_mono (hC _ (p.1.unop ≫ σ).op (ρ.pullback p.1.unop)) (@le_rfl _ _ _))

theorem normalizedBodyAction_isFinitary
    (hA : ℒ.Comprehension Γ₁ ΓA) (C : RawFamily Γ₁)
    {B : RawFamily ΓA} (hB : B.IsFinitary)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (normalizedBodyAction D hA C B σ₁ ρ).IsFinitary := by
  intro _ σ₂ label
  exact show ΩLower.IsFinitary fun I => sectionValue hA B (σ₂ ≫ σ₁) (ρ.pullback σ₂) label
      (D.rawExtend (C.app _ (σ₂ ≫ σ₁).op (ρ.pullback σ₂)) label I) from
    ΩLower.IsFinitary.comp (sectionValue_finitary hA hB (σ₂ ≫ σ₁) (ρ.pullback σ₂) label)
      (.of_eventually fun _ _ h => D.rawExtend_eventually label
        (fun {_} hc => Filter.Eventually.of_forall fun _ => hc) ΩLower.eventually_mem h)
      (((bodyHom hA B).app _ ((σ₂ ≫ σ₁).op, label)).hom.monotone.comp
        (monotone_const.prodMk monotone_id))
      fun _ _ h => D.rawExtend_mono_right label h

theorem sectionValue_iSup_le (hA : ℒ.Comprehension Γ₁ ΓA) (B : Nat → RawFamily ΓA)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (label : Tm_ Γ₂) (I : RawValue Γ₂) :
    sectionValue hA (⨆ n, B n) σ₁ ρ label I ≤ ⨆ n, sectionValue hA (B n) σ₁ ρ label I := by
  intro Γ₃ σ₂ y hy
  rw [mem_sectionValue] at hy
  rcases hy with hy | ⟨sec, hy⟩
  · exact (ΩLower.mem_iSup ..).mpr (Or.inl hy)
  · simp only [iSup_app] at hy
    have ⟨n, hy⟩ := (ΩLower.mem_iSup_of_nonempty ..).mp hy
    exact (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨n, Or.inr ⟨sec, hy⟩⟩

end RawFamily

namespace RawActionFamily

@[simp] theorem pullback_app (F : RawActionFamily Γ₁) {Δ : (CtxCat E ℓ)ᵒᵖ} {Γ₂ : CtxCat E ℓ}
    (σ₁ : op Γ₁ ⟶ Δ) (σ₂ : Γ₂ ⟶ Δ.unop) (ρ : RawValuation Δ.unop) :
    RawAction.pullback (F.app Δ σ₁ ρ) σ₂ = F.app (op Γ₂) (σ₁ ≫ σ₂.op) (ρ.pullback σ₂) :=
  (F.naturality_apply σ₂.op σ₁ ρ).symm

def IsFinitary (F : RawActionFamily Γ₁) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (i : ℕ) (ρ : RawValuation Γ₂)
    (X : RawValue Γ₂) (label : Tm_ Γ₂),
    ΩLower.IsFinitary fun I => (F.app _ σ.op (ρ.replace i I)).app _ ((𝟙 Γ₂).op, label) X

theorem IsFinitary.eventually {F : RawActionFamily Γ₁} (hF : F.IsFinitary)
    (σ : Γ₂ ⟶ Γ₁) (i : ℕ) (ρ : RawValuation Γ₂) (I X : RawValue Γ₂)
    (label : Tm_ Γ₂) {y : CoherentShape Γ₂}
    (hy : ((F.app _ σ.op (ρ.replace i I)).app _ ((𝟙 Γ₂).op, label) X).mem (𝟙 Γ₂) y) :
    ∀ᶠ J in I.approximations,
      ((F.app _ σ.op (ρ.replace i J)).app _ ((𝟙 Γ₂).op, label) X).mem (𝟙 Γ₂) y :=
  (hF σ i ρ X label).eventually
    (fun _ _ h => (F.app _ σ.op).hom.monotone
      (RawValuation.replace_mono i le_rfl h) _ ((𝟙 Γ₂).op, label) X)
    ΩLower.eventually_mem hy

theorem IsFinitary.graph_eventually {F : RawActionFamily Γ₁} (hF : F.IsFinitary)
    (σ : Γ₂ ⟶ Γ₁) (i : ℕ) (ρ : RawValuation Γ₂) (I : RawValue Γ₂)
    (f : CoherentGraph Γ₂)
    (hf : RawAction.GraphValid (F.app _ σ.op (ρ.replace i I)) (𝟙 Γ₂) f) :
    ∀ᶠ J in I.approximations,
      RawAction.GraphValid (F.app _ σ.op (ρ.replace i J)) (𝟙 Γ₂) f :=
  Filter.eventually_all.mpr fun j => hF.eventually σ i ρ I _ _ (hf j)

theorem IsFinitary.normalizedBody
    (hA : ℒ.Comprehension Γ₁ ΓA) {C : RawFamily Γ₁} (hC : C.IsFinitary)
    {B : RawFamily ΓA} (hB : B.IsFinitary) :
    (normalizedBody D hA C B).IsFinitary := by
  intro Γ₂ σ i ρ J label
  have hfin : ΩLower.IsFinitary fun I => RawFamily.sectionValue hA B σ (ρ.replace i I) label
      (D.rawExtend (C.app _ σ.op (ρ.replace i I)) label J) := by
    intro I y hy
    simp_rw [RawFamily.mem_sectionValue] at hy ⊢
    rcases hy with hy | ⟨s, hy⟩
    · exact ⟨∅, by simp, Or.inl hy⟩
    · simp at hy
      let X : RawFamily Γ₂ := RawFamily.decode D label (C.pullback σ) (RawFamily.constant J)
      have hX : X.IsFinitary := RawFamily.IsFinitary.decode D
        (RawFamily.IsFinitary.pullback hC σ) (RawFamily.constant_isFinitary J)
      have hxy : (B.app _ s.hom.op
          ((ρ.replace i I).push (X.app _ (𝟙 Γ₂).op (ρ.replace i I)))).mem (𝟙 Γ₂) y := by
        rw [RawFamily.decode_app_hom_coe, RawFamily.constant_app_hom_coe, RawFamily.pullback]
        simpa using hy
      have ⟨l, hl, hy⟩ := hB.compose_value hX (𝟙 Γ₂) s.hom i ρ I hxy
      refine ⟨l, hl, Or.inr ⟨s, ?_⟩⟩
      dsimp only at hy
      rw [RawFamily.decode_app_hom_coe, RawFamily.constant_app_hom_coe, RawFamily.pullback] at hy
      simpa using hy
  change ΩLower.IsFinitary fun I => RawFamily.sectionValue hA B (𝟙 _ ≫ σ)
    ((ρ.replace i I).pullback (𝟙 _)) label
    (D.rawExtend (C.app _ (𝟙 _ ≫ σ).op ((ρ.replace i I).pullback (𝟙 _))) label J)
  simpa using hfin

noncomputable def apply (F : RawActionFamily Γ₁) (X : RawFamily Γ₁) (label : Tm_ Γ₁) :
    RawFamily Γ₁ :=
  let p := CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.snd _ _ ≫ coyonedaEquiv.symm label)
      (Functor.homObjEquiv _ _ _ X.toTypes))
    (Functor.homObjEquiv _ _ _ F.toTypes)
  ((Functor.homObjEquiv _ _ _).symm (p ≫ MonoidalClosed.uncurry (RawAction.monotone E ℓ).ι)).ofTypes
    fun Y σ _ _ h =>
      OrderHom.apply_mono ((F.app Y σ).hom.monotone h Y (𝟙 Y, (Tm E ℓ).map σ label))
        ((X.app Y σ).hom.monotone h)

@[simp] theorem apply_app (F : RawActionFamily Γ₁) (X : RawFamily Γ₁)
    (label : Tm_ Γ₁) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (F.apply X label).app _ σ.op ρ =
      (F.app _ σ.op ρ).app _ ((𝟙 Γ₂).op, (Tm E ℓ).map σ.op label)
        (X.app _ σ.op ρ) := rfl

def IsActionFinitary (F : RawActionFamily Γ₁) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂), (F.app _ σ.op ρ).IsFinitary

theorem IsFinitary.apply {F : RawActionFamily Γ₁} (hF : F.IsFinitary) (hArg : F.IsActionFinitary)
    {X : RawFamily Γ₁} (hX : X.IsFinitary) (label : Tm_ Γ₁) :
    (F.apply X label).IsFinitary :=
  fun Γ₂ σ i ρ => ΩLower.IsFinitary.apply
    (fun J => hF σ i ρ J ((Tm E ℓ).map σ.op label))
    (fun I => hArg σ (ρ.replace i I) (𝟙 Γ₂) ((Tm E ℓ).map σ.op label)) (hX σ i ρ)
    (fun _ _ h J => (F.app _ σ.op).hom.monotone (RawValuation.replace_mono i le_rfl h) _ _ J)
    (fun I => ((F.app _ σ.op (ρ.replace i I)).app _ _).hom.monotone)
    ((X.app _ σ.op).hom.monotone.comp (Function.update_mono (f := ρ) (i := i)))

end RawActionFamily

end Metalean.CoherentShape
