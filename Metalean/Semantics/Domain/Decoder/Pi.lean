/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.CategoryTheory.Functor.FunctorHom
public import Metalean.TypeTheory.Syntactic.Pi.Term
public import Metalean.Semantics.Domain.Decoder.Extension

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ : CtxCat E ℓ}

section Decoder

noncomputable def graphAction (f : CoherentGraph Γ₁) : IdealAction Γ₁ :=
  applicationAction (principalIdeal f.lamGenerator)

@[simp]
theorem graphAction_value (f : CoherentGraph Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (label : Tm_ Γ₂) (X : Domain Γ₂) :
    (graphAction f).val.app _ (σ.op, label) X =
      application (principalIdeal (f.reindex σ).lamGenerator) label X :=
  congrArg (fun I => application I label X)
    (ΩIdeal.presheaf_map_principal (R := pointedOrder E ℓ) f.lamGenerator σ)

theorem pullback_graphAction (f : CoherentGraph Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (graphAction f).pullback σ₁ = graphAction (f.reindex σ₁) := by
  ext Γ₃ ⟨⟨σ₂⟩, label⟩ X
  change application ((principalIdeal f.lamGenerator).pullback (σ₂ ≫ σ₁)) label X =
    application ((principalIdeal (f.reindex σ₁).lamGenerator).pullback σ₂) label X
  rw [← ΩIdeal.pullback_pullback, ΩIdeal.presheaf_map_principal]
  rfl

theorem graphAction_le_of_valid (B : IdealAction Γ₁) (f : CoherentGraph Γ₁)
    (hf : B.onBasis.GraphValid (𝟙 Γ₁) f) (σ₁ : Γ₂ ⟶ Γ₁)
    (label : Tm_ Γ₂) (X : Domain Γ₂) :
    (graphAction f).val.app _ (σ₁.op, label) X ≤ B.val.app _ (σ₁.op, label) X := by
  have hgraph : (IdealAction.abstraction B).mem (𝟙 Γ₁) f.lamGenerator :=
    (IdealAction.mem_abstraction _ _ _).mpr ⟨f, hf, le_rfl⟩
  have hle : application ((principalIdeal f.lamGenerator).pullback σ₁) label X ≤
      application ((IdealAction.abstraction B).pullback σ₁) label X :=
    application_mono (ΩIdeal.pullback_mono (ΩLower.principal_le_iff.mpr hgraph) σ₁) (@le_rfl _ _ _)
  rw [pullback_abstraction, IdealAction.application_abstraction] at hle
  intro Γ₃ σ₂ z hz
  have h := hle σ₂ z hz
  change (B.val.app _ (σ₁.op ≫ (𝟙 Γ₂).op, label) X).mem σ₂ z at h
  simpa using h

namespace CodeAssignment

theorem pairPresheaf_fst (L : Ty.Pair Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    ((Ty.pairPresheaf E ℓ).map σ.op L).1 = yoneda.map σ ≫ L.1 := rfl

theorem map_pair_comp (L : Ty.Pair Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) :
    (Ty.pairPresheaf E ℓ).map σ₂.op ((Ty.pairPresheaf E ℓ).map σ₁.op L) =
      (Ty.pairPresheaf E ℓ).map (σ₂ ≫ σ₁).op L := by
  rw [op_comp, Functor.map_comp_apply]

theorem map_tm_comp (N : Tm_ Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) :
    (Tm E ℓ).map σ₂.op ((Tm E ℓ).map σ₁.op N) = (Tm E ℓ).map (σ₂ ≫ σ₁).op N := by
  rw [op_comp, Functor.map_comp_apply]

theorem map_forallE_cond {label : Ty.Pair Γ₁} {n : Tm_ Γ₁} {σ₁ : Γ₂ ⟶ Γ₁}
    (h : Tm.type ((Tm E ℓ).map σ₁.op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ₁.op label).1
        ((Ty.pairPresheaf E ℓ).map σ₁.op label).2)
    (σ₂ : Γ₃ ⟶ Γ₂) :
    Tm.type ((Tm E ℓ).map (σ₂ ≫ σ₁).op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ σ₁).op label).1
        ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ σ₁).op label).2 := by
  rw [← map_tm_comp, Tm.type_map, h, Ty.map_piApp, ← map_pair_comp]
  rfl

theorem map_dom_cond {label : Ty.Pair Γ₁} {m : Tm_ Γ₂} {σ₁ : Γ₂ ⟶ Γ₁}
    (hm : Tm.type m = yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ₁.op label).1) (σ₂ : Γ₃ ⟶ Γ₂) :
    Tm.type ((Tm E ℓ).map σ₂.op m) =
      yonedaEquiv ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ σ₁).op label).1 := by
  rw [Tm.type_map, hm, ← map_pair_comp]
  exact yonedaEquiv_naturality _ _

variable (F : CodeAssignment E ℓ) (label : Ty.Pair Γ₁) (n : Tm_ Γ₁)
  (A : Domain Γ₁) (B : IdealAction Γ₁)

noncomputable def resultBody (σ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
    (X Y : Domain Γ₂)
    (h : Tm.type ((Tm E ℓ).map σ.op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ.op label).1 ((Ty.pairPresheaf E ℓ).map σ.op label).2)
    (hm : Tm.type m = yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ.op label).1) : Domain Γ₂ :=
  F.extend (B.val.app _ (σ.op, m) X)
    (Tm.apply ((Ty.pairPresheaf E ℓ).map σ.op label).1 ((Ty.pairPresheaf E ℓ).map σ.op label).2
      ((Tm E ℓ).map σ.op n) m h hm) Y

theorem pullback_resultBody (σ₁ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
    (X Y : Domain Γ₂)
    (h : Tm.type ((Tm E ℓ).map σ₁.op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ₁.op label).1
        ((Ty.pairPresheaf E ℓ).map σ₁.op label).2)
    (hm : Tm.type m = yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ₁.op label).1) (σ₂ : Γ₃ ⟶ Γ₂) :
    (F.resultBody label n B σ₁ m X Y h hm).pullback σ₂ =
      F.resultBody label n B (σ₂ ≫ σ₁) ((Tm E ℓ).map σ₂.op m) (X.pullback σ₂) (Y.pullback σ₂)
        (map_forallE_cond h σ₂) (map_dom_cond hm σ₂) := by
  have hlab := map_pair_comp label σ₁ σ₂
  rw [resultBody, resultBody, F.pullback_extend,
    Tm.map_apply ((Ty.pairPresheaf E ℓ).map σ₁.op label).1
      ((Ty.pairPresheaf E ℓ).map σ₁.op label).2 ((Tm E ℓ).map σ₁.op n) m h hm σ₂
      (by
        rw [map_tm_comp]
        refine (map_forallE_cond h σ₂).trans ?_
        rw [← map_pair_comp]
        rfl)
      (by
        refine (map_dom_cond hm σ₂).trans ?_
        rw [← map_pair_comp]
        rfl),
    ← B.app_pullback σ₁.op σ₂ m X, ← op_comp]
  exact congrArg (F.extend _ · _) (Tm.apply_congr hlab (map_tm_comp n σ₁ σ₂) rfl _ _
    (map_forallE_cond h σ₂) (map_dom_cond hm σ₂))

noncomputable def resultIdeal (σ₁ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
    (X Y : Domain Γ₂) : Domain Γ₂ where
  val.mem σ₂ z := z ≤ ⊥ ∨ ∃ (h : Tm.type ((Tm E ℓ).map (σ₂ ≫ σ₁).op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ σ₁).op label).1
        ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ σ₁).op label).2)
      (hm : Tm.type ((Tm E ℓ).map σ₂.op m) =
        yonedaEquiv ((Ty.pairPresheaf E ℓ).map (σ₂ ≫ σ₁).op label).1),
    (F.resultBody label n B (σ₂ ≫ σ₁) ((Tm E ℓ).map σ₂.op m) (X.pullback σ₂)
      (Y.pullback σ₂) h hm).mem (𝟙 _) z
  val.natural σ₂ σ₃ z := by
    rintro (hz | ⟨h, hm, hz⟩)
    · exact Or.inl (Le.reindex σ₃ hz)
    have hmem := (F.resultBody label n B (σ₂ ≫ σ₁) ((Tm E ℓ).map σ₂.op m) (X.pullback σ₂)
      (Y.pullback σ₂) h hm).natural (𝟙 _) σ₃ z hz
    rw [Category.comp_id, ← ΩIdeal.presheaf_map_mem_id, F.pullback_resultBody] at hmem
    rw [Category.assoc, ← map_tm_comp m σ₂ σ₃, ← ΩIdeal.pullback_pullback,
      ← ΩIdeal.pullback_pullback]
    exact Or.inr ⟨_, _, hmem⟩
  val.bottom _ := Or.inl bot_le
  val.lower _ hab hb := by
    rcases hb with hb | ⟨h, hm, hb⟩
    · exact Or.inl (hab.trans hb)
    · exact Or.inr ⟨h, hm, (F.resultBody label n B _ _ _ _ _ hm).lower (𝟙 _) hab hb⟩
  property := by
    rintro Γ₃ σ₂ c d (hc | ⟨h, hm, hc⟩) hd
    · exact ⟨d, hd, hc.trans bot_le, le_rfl⟩
    rcases hd with hd | ⟨h', hm', hd⟩
    · exact ⟨c, Or.inr ⟨h, hm, hc⟩, le_rfl, hd.trans bot_le⟩
    have ⟨w, hw, hcw, hdw⟩ := (F.resultBody label n B _ _ _ _ h hm).property (𝟙 Γ₃) hc hd
    exact ⟨w, Or.inr ⟨h, hm, hw⟩, hcw, hdw⟩

theorem resultIdeal_mono (σ₁ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
    {X Y X' Y' : Domain Γ₂} (hX : X ≤ X') (hY : Y ≤ Y') :
    F.resultIdeal label n B σ₁ m X Y ≤ F.resultIdeal label n B σ₁ m X' Y' := by
  rintro Γ₃ σ₂ z (hz | ⟨h, hm, hz⟩)
  · exact Or.inl hz
  exact Or.inr ⟨h, hm, F.extend_mono ((B.val.app _ _).hom.monotone (ΩIdeal.pullback_mono hX σ₂))
    (ΩIdeal.pullback_mono hY σ₂) (𝟙 Γ₃) z hz⟩

theorem pullback_resultIdeal (σ₁ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
    (X Y : Domain Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) :
    (F.resultIdeal label n B σ₁ m X Y).pullback σ₂ =
      F.resultIdeal label n B (σ₂ ≫ σ₁) ((Tm E ℓ).map σ₂.op m) (X.pullback σ₂)
        (Y.pullback σ₂) := by
  apply ΩIdeal.ext
  intro Γ₄ σ₃ z
  rw [ΩIdeal.presheaf_map_mem]
  dsimp only [resultIdeal, ΩIdeal.mem]
  rw [Category.assoc, map_tm_comp, ΩIdeal.pullback_pullback, ΩIdeal.pullback_pullback]

theorem resultBody_finitary_left (σ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
    (Y : Domain Γ₂)
    (h : Tm.type ((Tm E ℓ).map σ.op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ.op label).1 ((Ty.pairPresheaf E ℓ).map σ.op label).2)
    (hm : Tm.type m = yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ.op label).1) :
    ΩIdeal.IsFinitary fun X => F.resultBody label n B σ m X Y h hm :=
  (F.extend_finitary_left _ _).comp (B.property _ (σ.op, m))
    fun _ _ hle => F.extend_mono hle (@le_rfl _ _ _)

theorem resultIdeal_finitary (σ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂) :
    (∀ Y, ΩIdeal.IsFinitary fun X => F.resultIdeal label n B σ m X Y) ∧
      ∀ X, ΩIdeal.IsFinitary fun Y => F.resultIdeal label n B σ m X Y := by
  constructor <;> rintro _ Z z (hz | ⟨h, hm, hz⟩)
  · exact ⟨⊥, Z.bottom (𝟙 Γ₂), Or.inl hz⟩
  · rw [ΩIdeal.pullback_id] at hz
    have ⟨x, hx, hz⟩ := F.resultBody_finitary_left label n B _ _ _ h hm Z hz
    exact ⟨x, hx, Or.inr ⟨h, hm, by rwa [ΩIdeal.pullback_id]⟩⟩
  · exact ⟨⊥, Z.bottom (𝟙 Γ₂), Or.inl hz⟩
  · rw [ΩIdeal.pullback_id] at hz
    have ⟨y, hy, hz⟩ := F.extend_finitary_right _ _ Z hz
    exact ⟨y, hy, Or.inr ⟨h, hm, by rwa [ΩIdeal.pullback_id]⟩⟩

theorem resultIdeal_pullback (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂)
    (m : Tm_ Γ₃) (X Y : Domain Γ₃) :
    F.resultIdeal ((Ty.pairPresheaf E ℓ).map σ₁.op label) ((Tm E ℓ).map σ₁.op n) (B.pullback σ₁)
        σ₂ m X Y =
      F.resultIdeal label n B (σ₂ ≫ σ₁) m X Y := by
  apply ΩIdeal.ext
  intro Γ₄ σ₃ z
  dsimp only [resultIdeal, ΩIdeal.mem, resultBody, IdealAction.pullback_app]
  rw [map_pair_comp, map_tm_comp n, Category.assoc]

theorem resultIdeal_eq_body (σ₁ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
    (X Y : Domain Γ₂)
    (h : Tm.type ((Tm E ℓ).map σ₁.op n) =
      Ty.piApp ((Ty.pairPresheaf E ℓ).map σ₁.op label).1
        ((Ty.pairPresheaf E ℓ).map σ₁.op label).2)
    (hm : Tm.type m = yonedaEquiv ((Ty.pairPresheaf E ℓ).map σ₁.op label).1) :
    F.resultIdeal label n B σ₁ m X Y = F.resultBody label n B σ₁ m X Y h hm := by
  apply ΩIdeal.ext
  intro Γ₃ σ₂ z
  constructor
  · rintro (hz | ⟨h', hm', hz⟩)
    · exact (F.resultBody label n B σ₁ m X Y h hm).lower σ₂ hz
        ((F.resultBody label n B σ₁ m X Y h hm).bottom σ₂)
    · rw [← ΩIdeal.presheaf_map_mem_id _ σ₂, F.pullback_resultBody]
      exact hz
  · intro hz
    refine Or.inr ⟨map_forallE_cond h σ₂, map_dom_cond hm σ₂, ?_⟩
    rw [← F.pullback_resultBody, ΩIdeal.presheaf_map_mem_id]
    exact hz

theorem resultIdeal_idempotent {F : CodeAssignment E ℓ} (hF : F.IsIdempotent)
    (label : Ty.Pair Γ₁) (n : Tm_ Γ₁) (B : IdealAction Γ₁)
    (σ₁ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂) (X Y : Domain Γ₂) :
    F.resultIdeal label n B σ₁ m X (F.resultIdeal label n B σ₁ m X Y) =
      F.resultIdeal label n B σ₁ m X Y := by
  apply ΩIdeal.ext
  intro Γ₃ σ₂ z
  refine or_congr_right (exists_congr fun h' => exists_congr fun hm' => ?_)
  rw [resultBody, resultBody, F.pullback_resultIdeal,
    F.resultIdeal_eq_body label n B (σ₂ ≫ σ₁) _ _ _ h' hm', resultBody,
    F.extend_idempotent hF]

noncomputable def piBody (G : Domain Γ₁) : IdealAction Γ₁ where
  val.app _ := fun (⟨σ⟩, m) => Preord.ofHom {
    toFun X := F.resultIdeal label n B σ m (F.extend (A.pullback σ) m X)
      (application (G.pullback σ) m (F.extend (A.pullback σ) m X))
    monotone' _ _ h := F.resultIdeal_mono label n B σ m (F.extend_mono (@le_rfl _ _ _) h)
      (application_mono (@le_rfl _ _ _) (F.extend_mono (@le_rfl _ _ _) h)) }
  val.naturality σ₂ := fun (⟨σ₁⟩, m) => Preord.ext fun X => by
    have h := F.pullback_resultIdeal label n B σ₁ m (F.extend (A.pullback σ₁) m X)
      (application (G.pullback σ₁) m (F.extend (A.pullback σ₁) m X)) σ₂.unop
    rw [pullback_application, F.pullback_extend, ΩIdeal.pullback_pullback,
      ΩIdeal.pullback_pullback] at h
    exact h.symm
  property _ := fun (⟨σ⟩, m) => ΩIdeal.IsFinitary.comp₂
    (fun _ _ h => F.resultIdeal_mono label n B σ m h.1 h.2)
    (F.resultIdeal_finitary label n B σ m).1 (F.resultIdeal_finitary label n B σ m).2
    (F.extend_finitary_right _ m)
    ((application_argument_finitary _ m).comp (F.extend_finitary_right _ m)
      fun _ _ h => application_mono (@le_rfl _ _ _) h)
    (fun _ _ h => F.extend_mono (@le_rfl _ _ _) h) fun _ _ h => application_mono (@le_rfl _ _ _) (F.extend_mono (@le_rfl _ _ _) h)

theorem piBody_app_id (G X : Domain Γ₁) (m : Tm_ Γ₁) :
    (F.piBody label n A B G).val.app _ ((𝟙 Γ₁).op, m) X =
      F.resultIdeal label n B (𝟙 Γ₁) m (F.extend A m X) (application G m (F.extend A m X)) := by
  change F.resultIdeal label n B (𝟙 Γ₁) m (F.extend (A.pullback (𝟙 Γ₁)) m X)
    (application (G.pullback (𝟙 Γ₁)) m (F.extend (A.pullback (𝟙 Γ₁)) m X)) = _
  simp

theorem piBody_mono {A A' : Domain Γ₁} {B B' : IdealAction Γ₁} {G G' : Domain Γ₁} (hA : A ≤ A')
    (hB : ∀ {Γ₂ : CtxCat E ℓ} (σ₁ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
      (X : Domain Γ₂), B.val.app _ (σ₁.op, m) X ≤ B'.val.app _ (σ₁.op, m) X) (hG : G ≤ G')
    (σ₁ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂) (X : Domain Γ₂) :
    (F.piBody label n A B G).val.app _ (σ₁.op, m) X ≤
      (F.piBody label n A' B' G').val.app _ (σ₁.op, m) X := by
  have hA : A.pullback σ₁ ≤ A'.pullback σ₁ := ΩIdeal.pullback_mono hA σ₁
  have harg : F.extend (A.pullback σ₁) m X ≤ F.extend (A'.pullback σ₁) m X :=
    F.extend_mono hA (@le_rfl _ _ _)
  rintro Γ₃ σ₂ z (hz | ⟨h, hm, hz⟩)
  · exact Or.inl hz
  exact Or.inr ⟨h, hm, F.extend_mono (fun σ₃ y hy => (B'.val.app _ _).hom.monotone
    (ΩIdeal.pullback_mono harg σ₂) σ₃ y (hB _ _ _ σ₃ y hy))
    (ΩIdeal.pullback_mono (application_mono (ΩIdeal.pullback_mono hG σ₁) harg) σ₂) (𝟙 Γ₃) z hz⟩

theorem application_abstraction_piBody (G : Domain Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (m : Tm_ Γ₂) (X : Domain Γ₂) :
    application ((IdealAction.abstraction (F.piBody label n A B G)).pullback σ) m X =
      F.resultIdeal label n B σ m (F.extend (A.pullback σ) m X)
        (application (G.pullback σ) m (F.extend (A.pullback σ) m X)) := by
  rw [pullback_abstraction, IdealAction.application_abstraction]
  change F.resultIdeal label n B (𝟙 Γ₂ ≫ σ) m (F.extend (A.pullback (𝟙 Γ₂ ≫ σ)) m X)
    (application (G.pullback (𝟙 Γ₂ ≫ σ)) m (F.extend (A.pullback (𝟙 Γ₂ ≫ σ)) m X)) = _
  simp

theorem application_eq_of_piBody_fixed {G : Domain Γ₁}
    (hG : IdealAction.abstraction (F.piBody label n A B G) = G) (σ : Γ₂ ⟶ Γ₁)
    (m : Tm_ Γ₂) (X : Domain Γ₂) :
    application (G.pullback σ) m X =
      F.resultIdeal label n B σ m (F.extend (A.pullback σ) m X)
        (application (G.pullback σ) m (F.extend (A.pullback σ) m X)) := by
  conv_lhs => rw [← hG]
  exact F.application_abstraction_piBody label n A B G σ m X

theorem pullback_piBody (G : Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (F.piBody label n A B G).pullback σ =
      F.piBody ((Ty.pairPresheaf E ℓ).map σ.op label) ((Tm E ℓ).map σ.op n) (A.pullback σ)
        (B.pullback σ) (G.pullback σ) := by
  ext Γ₃ ⟨⟨σ₂⟩, m⟩ X
  change F.resultIdeal label n B (σ₂ ≫ σ) m (F.extend (A.pullback (σ₂ ≫ σ)) m X)
      (application (G.pullback (σ₂ ≫ σ)) m (F.extend (A.pullback (σ₂ ≫ σ)) m X)) =
    F.resultIdeal ((Ty.pairPresheaf E ℓ).map σ.op label) ((Tm E ℓ).map σ.op n) (B.pullback σ)
      σ₂ m (F.extend ((A.pullback σ).pullback σ₂) m X)
      (application ((G.pullback σ).pullback σ₂) m (F.extend ((A.pullback σ).pullback σ₂) m X))
  rw [resultIdeal_pullback, ΩIdeal.pullback_pullback, ΩIdeal.pullback_pullback]

theorem piBody_finitary (G X : Domain Γ₁) (m : Tm_ Γ₁) {y : CoherentShape Γ₁}
    (hy : ((F.piBody label n A B G).val.app _ ((𝟙 Γ₁).op, m) X).mem (𝟙 Γ₁) y) :
    ∃ g, G.mem (𝟙 Γ₁) g ∧
      ((F.piBody label n A B (principalIdeal g)).val.app _ ((𝟙 Γ₁).op, m) X).mem (𝟙 Γ₁) y := by
  rw [piBody_app_id] at hy
  rcases hy with hy | ⟨hc, hm, hy⟩
  · exact ⟨⊥, G.bottom (𝟙 _), by rw [piBody_app_id]; exact Or.inl hy⟩
  rw [resultBody, ΩIdeal.pullback_id, ΩIdeal.pullback_id] at hy
  have ⟨c, hc', hy⟩ := F.extend_finitary_right _ _ _ hy
  have ⟨g, hg, hc'⟩ := application_function_finitary G m hc'
  refine ⟨g, hg, ?_⟩
  rw [piBody_app_id]
  refine Or.inr ⟨hc, hm, ?_⟩
  rw [resultBody, ΩIdeal.pullback_id, ΩIdeal.pullback_id]
  exact F.extend_mono (@le_rfl _ _ _) (ΩLower.principal_le_iff.mpr hc') (𝟙 _) y hy

noncomputable def piAction : IdealAction Γ₁ where
  val.app _ p := Preord.ofHom {
    toFun G := IdealAction.abstraction (F.piBody ((Ty.pairPresheaf E ℓ).map p.1.unop.op label) p.2
      (A.pullback p.1.unop) (B.pullback p.1.unop) G)
    monotone' _ _ hG := IdealAction.abstraction_mono fun σ m X =>
      F.piBody_mono _ _ (@le_rfl _ _ _) (fun _ _ _ => @le_rfl _ _ _) hG σ m X }
  val.naturality σ p := Preord.ext fun G => by
    change IdealAction.abstraction (F.piBody ((Ty.pairPresheaf E ℓ).map (p.1 ≫ σ).unop.op label)
        ((Tm E ℓ).map σ p.2) (A.pullback (p.1 ≫ σ).unop) (B.pullback (p.1 ≫ σ).unop)
        (G.pullback σ.unop)) =
      (IdealAction.abstraction (F.piBody ((Ty.pairPresheaf E ℓ).map p.1.unop.op label) p.2
        (A.pullback p.1.unop) (B.pullback p.1.unop) G)).pullback σ.unop
    rw [pullback_abstraction, pullback_piBody, ΩIdeal.pullback_pullback,
      IdealAction.pullback_pullback, unop_comp, op_comp]
    simp only [Functor.map_comp_apply, Quiver.Hom.op_unop]
  property _ p := IdealAction.abstraction_finitary
    (fun G => F.piBody ((Ty.pairPresheaf E ℓ).map p.1.unop.op label) p.2
      (A.pullback p.1.unop) (B.pullback p.1.unop) G)
    (fun hG m X => F.piBody_mono _ _ (@le_rfl _ _ _) (fun _ _ _ => @le_rfl _ _ _) hG (𝟙 _) m X)
    fun G m X _ hy => F.piBody_finitary _ _ _ _ G X m hy

@[simp] theorem piAction_app_id (G : Domain Γ₁) :
    (F.piAction label A B).val.app _ ((𝟙 Γ₁).op, n) G =
      IdealAction.abstraction (F.piBody label n A B G) := by
  change IdealAction.abstraction (F.piBody ((Ty.pairPresheaf E ℓ).map (𝟙 Γ₁).op label) n
    (A.pullback (𝟙 Γ₁)) (B.pullback (𝟙 Γ₁)) G) = _
  simp [IdealAction.pullback_id]

theorem pullback_piAction (σ : Γ₂ ⟶ Γ₁) :
    (F.piAction label A B).pullback σ =
      F.piAction ((Ty.pairPresheaf E ℓ).map σ.op label) (A.pullback σ) (B.pullback σ) := by
  ext Γ₃ p G
  change IdealAction.abstraction (F.piBody ((Ty.pairPresheaf E ℓ).map (p.1.unop ≫ σ).op label) p.2
      (A.pullback (p.1.unop ≫ σ)) (B.pullback (p.1.unop ≫ σ)) G) =
    IdealAction.abstraction (F.piBody
      ((Ty.pairPresheaf E ℓ).map p.1.unop.op ((Ty.pairPresheaf E ℓ).map σ.op label)) p.2
      ((A.pullback σ).pullback p.1.unop) ((B.pullback σ).pullback p.1.unop) G)
  rw [ΩIdeal.pullback_pullback, IdealAction.pullback_pullback, map_pair_comp]

theorem piAction_mono {A A' : Domain Γ₁} (hA : A ≤ A') {B B' : IdealAction Γ₁}
    (hB : ∀ {Γ₂ : CtxCat E ℓ} (σ₁ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
      (X : Domain Γ₂), B.val.app _ (σ₁.op, m) X ≤ B'.val.app _ (σ₁.op, m) X) :
    F.piAction label A B ≤ F.piAction label A' B' := fun _ p _ =>
  IdealAction.abstraction_mono fun σ₂ m X =>
    F.piBody_mono _ p.2 (ΩIdeal.pullback_mono hA _) (fun σ₁ m X => hB (σ₁ ≫ p.1.unop) m X) (@le_rfl _ _ _)
      σ₂ m X

theorem piAction_isIdempotent {F : CodeAssignment E ℓ} (hF : F.IsIdempotent)
    (label : Ty.Pair Γ₁) (A : Domain Γ₁) (B : IdealAction Γ₁) :
    (F.piAction label A B).IsIdempotent := by
  intro Γ₂ σ n G
  refine congrArg IdealAction.abstraction ?_
  ext Γ₃ ⟨⟨σ₂⟩, m⟩ X
  change F.resultIdeal _ n _ σ₂ m (F.extend _ m X) (application
    ((IdealAction.abstraction (F.piBody _ n _ _ G)).pullback σ₂) m (F.extend _ m X)) = _
  rw [application_abstraction_piBody, F.extend_idempotent hF, resultIdeal_idempotent hF]
  rfl

end CodeAssignment

end Decoder

section Support

variable (F : CodeAssignment E ℓ) {z : CoherentShape Γ₁}

theorem applicationAction_abstraction (B : IdealAction Γ₁) :
    applicationAction (IdealAction.abstraction B) = B := by
  ext ⟨Γ₂⟩ ⟨⟨σ⟩, label⟩ X
  change application ((IdealAction.abstraction B).pullback σ) label X = _
  refine (congrArg (fun I => application I label X) (pullback_abstraction B σ)).trans ?_
  rw [IdealAction.application_abstraction]
  change B.val.app _ (σ.op ≫ (𝟙 Γ₂).op, label) X = _
  simp
  rfl

namespace CodeAssignment

theorem piAction_domain_finitary (label : Ty.Pair Γ₁)
    (n : Tm_ Γ₁) (A : Domain Γ₁) (B : IdealAction Γ₁) (G : Domain Γ₁)
    (hz : ((F.piAction label A B).val.app _ ((𝟙 Γ₁).op, n) G).mem (𝟙 Γ₁) z) :
    ∃ a, A.mem (𝟙 Γ₁) a ∧
      ((F.piAction label (principalIdeal a) B).val.app _ ((𝟙 Γ₁).op, n) G).mem (𝟙 Γ₁) z := by
  simp only [piAction_app_id] at hz ⊢
  refine IdealAction.abstraction_finitary (fun A ↦ F.piBody label n A B G)
    (fun h m X ↦ F.piBody_mono label n h (fun _ _ _ => @le_rfl _ _ _) (@le_rfl _ _ _) (𝟙 Γ₁) m X)
    (fun A' m X _ hz ↦ ?_) A hz
  simp only [piBody_app_id] at hz ⊢
  exact ΩIdeal.IsFinitary.comp₂
    (fun _ _ ⟨hU, hV⟩ => F.resultIdeal_mono label n B (𝟙 Γ₁) m hU hV)
    (F.resultIdeal_finitary label n B (𝟙 Γ₁) m).1 (F.resultIdeal_finitary label n B (𝟙 Γ₁) m).2
    (F.extend_finitary_left m X)
    ((application_argument_finitary G m).comp (F.extend_finitary_left m X)
      fun _ _ h => application_mono (@le_rfl _ _ _) h)
    (fun _ _ h => F.extend_mono h (@le_rfl _ _ _))
    (fun _ _ h => application_mono (@le_rfl _ _ _) (F.extend_mono h (@le_rfl _ _ _))) A' hz

theorem piAction_body_finitary (label : Ty.Pair Γ₁)
    (n : Tm_ Γ₁) (A H G : Domain Γ₁)
    (hz : ((F.piAction label A (applicationAction H)).val.app _
      ((𝟙 Γ₁).op, n) G).mem (𝟙 Γ₁) z) :
    ∃ h, H.mem (𝟙 Γ₁) h ∧
      ((F.piAction label A (applicationAction
        (principalIdeal h))).val.app _ ((𝟙 Γ₁).op, n) G).mem (𝟙 Γ₁) z := by
  simp only [piAction_app_id] at hz ⊢
  refine IdealAction.abstraction_finitary (fun H ↦ F.piBody label n A (applicationAction H) G)
    (fun hle m X ↦ F.piBody_mono label n (@le_rfl _ _ _)
      (fun σ m X => application_mono (ΩIdeal.pullback_mono hle σ) (@le_rfl _ _ _)) (@le_rfl _ _ _) (𝟙 Γ₁) m X)
    (fun H' m X y hy ↦ ?_) H hz
  rw [piBody_app_id] at hy
  rcases hy with hy | ⟨hc, hm, hy⟩
  · exact ⟨⊥, H'.bottom (𝟙 Γ₁), by rw [piBody_app_id]; exact Or.inl hy⟩
  rw [ΩIdeal.pullback_id] at hy
  change (F.extend (application (H'.pullback (𝟙 Γ₁)) _ _) _ _).mem (𝟙 Γ₁) y at hy
  rw [ΩIdeal.pullback_id] at hy
  have ⟨b, hb, hy⟩ := F.extend_finitary_left _ _ _ hy
  have ⟨h, hh, hb⟩ := application_function_finitary H' _ hb
  refine ⟨h, hh, ?_⟩
  rw [piBody_app_id]
  refine Or.inr ⟨hc, hm, ?_⟩
  rw [ΩIdeal.pullback_id]
  change (F.extend (application ((principalIdeal h).pullback (𝟙 Γ₁)) _ _) _ _).mem (𝟙 Γ₁) y
  rw [ΩIdeal.pullback_id]
  exact F.extend_mono (ΩLower.principal_le_iff.mpr hb) (@le_rfl _ _ _) (𝟙 Γ₁) y hy

end CodeAssignment

end Support

end Metalean.CoherentShape
