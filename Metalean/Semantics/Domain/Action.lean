/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Domain.Application
import Mathlib.Data.Fintype.Order

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

open CategoryTheory Opposite Presheaf

noncomputable abbrev BasisAction.presheaf (E : Env ζ) (ℓ : Nat) := Functor.parameterizedHom (order E ℓ)
  (ΩLower.presheaf (pointedOrder E ℓ)) (Tm E ℓ)

abbrev BasisAction (Γ₁ : CtxCat E ℓ) : Type := (BasisAction.presheaf E ℓ).obj (op Γ₁)

namespace BasisAction

def IsIdealValued (F : BasisAction Γ₁) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂) (x : CoherentShape Γ₂),
    (F.app _ (σ.op, label) x).IsDirected

def GraphValid (F : BasisAction Γ₁) (σ : Γ₂ ⟶ Γ₁) (f : CoherentGraph Γ₂) : Prop :=
  ∀ i, (F.app _ (σ.op, f.1.names i) (f.input i)).mem (𝟙 Γ₂) (f.output i)

namespace GraphValid

theorem mono {F G : BasisAction Γ₁} (hFG : F ≤ G) {σ : Γ₂ ⟶ Γ₁} {f : CoherentGraph Γ₂}
    (hf : GraphValid F σ f) : GraphValid G σ f :=
  fun i => hFG _ (σ.op, f.1.names i) _ (𝟙 Γ₂) _ (hf i)

theorem reindex {F : BasisAction Γ₁} {σ₁ : Γ₂ ⟶ Γ₁} {f : CoherentGraph Γ₂} (hf : GraphValid F σ₁ f)
    (σ₂ : Γ₃ ⟶ Γ₂) : GraphValid F (σ₂ ≫ σ₁) (f.reindex σ₂) := by
  intro i
  have hB' : ((F.app _ (σ₁.op, f.1.names i) (f.input i)).pullback σ₂).mem (𝟙 Γ₃)
      (CoherentShape.reindex σ₂ (f.output i)) := by
    simpa using (F.app _ (σ₁.op, f.1.names i) (f.input i)).natural (𝟙 Γ₂) σ₂ (f.output i) (hf i)
  exact congrArg (fun L : ΩLower (pointedOrder E ℓ) Γ₃ =>
    L.mem (𝟙 Γ₃) (CoherentShape.reindex σ₂ (f.output i)))
    (F.naturality_apply σ₂.op (σ₁.op, f.1.names i) (f.input i)).symm ▸ hB'

theorem append {F : BasisAction Γ₁} {σ : Γ₂ ⟶ Γ₁} {f g : CoherentGraph Γ₂} (hf : GraphValid F σ f)
    (hg : GraphValid F σ g) (hfg : Graph.Compatible (𝟙 Γ₂) f.1 g.1) :
    GraphValid F σ (f.append g hfg) := fun i =>
  Fin.addCases
    (fun i => by simpa [CoherentGraph.input, CoherentGraph.output, CoherentGraph.append] using hf i)
    (fun i => by
      simpa [CoherentGraph.input, CoherentGraph.output, CoherentGraph.append] using hg i) i

theorem internallyCompatible {F : BasisAction Γ₁} {σ₁ : Γ₂ ⟶ Γ₁} {f g : CoherentGraph Γ₂}
    (hF : F.IsIdealValued) (hf : GraphValid F σ₁ f) (hg : GraphValid F σ₁ g) :
    Graph.Compatible (𝟙 Γ₂) f.1 g.1 := by
  intro i j Γ₃ σ₂ hlabel hinput
  simp at hlabel hinput ⊢
  have hfi := hf.reindex σ₂ i
  have hgj := hg.reindex σ₂ j
  have ⟨c, hac, hbc⟩ := upper_of_compatible (a := CoherentShape.reindex σ₂ (f.input i))
    (b := CoherentShape.reindex σ₂ (g.input j)) ((Shape.Compatible.reindexHom_iff σ₂ (f.input i).1 (g.input j).1 (𝟙 _)).mpr
      (by rw [Category.id_comp]; exact hinput))
  have hfi' := (F.app _ ((σ₂ ≫ σ₁).op, (f.reindex σ₂).1.names i)).hom.monotone hac (𝟙 Γ₃) _ hfi
  have hgj' := (F.app _ ((σ₂ ≫ σ₁).op, (g.reindex σ₂).1.names j)).hom.monotone hbc (𝟙 Γ₃) _ hgj
  have hlabel' : (f.reindex σ₂).1.names i = (g.reindex σ₂).1.names j := hlabel
  rw [← hlabel'] at hgj'
  have ⟨d, _, hpd, hqd⟩ := hF (σ₂ ≫ σ₁) _ c (𝟙 Γ₃) hfi' hgj'
  have h := (Shape.Compatible.reindexHom_iff σ₂ (f.output i).1 (g.output j).1 (𝟙 _)).mp
    (compatible_of_le hpd hqd (𝟙 _))
  rw [Category.id_comp] at h
  exact h

end GraphValid

def abstraction (F : BasisAction Γ₁) : ΩLower (pointedOrder E ℓ) Γ₁ where
  mem σ q := ∃ f : CoherentGraph _, GraphValid F σ f ∧ q ≤ f.lamGenerator
  natural _ σ _ := fun ⟨f, hf, hqf⟩ => ⟨f.reindex σ, hf.reindex σ, Le.reindex σ hqf⟩
  bottom _ := ⟨CoherentGraph.nil _, fun i => i.elim0, bot_le⟩
  lower _ hqr := fun ⟨f, hf, hrf⟩ => ⟨f, hf, hqr.trans hrf⟩

@[simp] theorem mem_abstraction (F : BasisAction Γ₂)
    (σ : Γ₁ ⟶ Γ₂) (q : CoherentShape Γ₁) :
    F.abstraction.mem σ q ↔ ∃ f : CoherentGraph Γ₁, GraphValid F σ f ∧ q ≤ f.lamGenerator :=
  Iff.rfl

@[simp]
theorem pullback_abstraction (F : BasisAction Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    F.abstraction.pullback σ = abstraction ((presheaf E ℓ).map σ.op F) := by
  rfl

theorem abstraction_isDirected {F : BasisAction Γ₁} (hF : F.IsIdealValued) :
    F.abstraction.IsDirected := by
  intro Γ₂ σ q r ⟨f, hf, hqf⟩ ⟨g, hg, hrg⟩
  have hfg := hf.internallyCompatible hF hg
  exact ⟨(f.append g hfg).lamGenerator, ⟨f.append g hfg, hf.append hg hfg, le_rfl⟩,
    hqf.trans (Basis.Le.lam (Graph.Le.append_left f.1 g.1)),
    hrg.trans (Basis.Le.lam (Graph.Le.append_right f.1 g.1))⟩

theorem abstraction_mono {F G : BasisAction Γ₁} (h : F ≤ G) : F.abstraction ≤ G.abstraction :=
  fun _ _ ⟨f, hf, hqf⟩ => ⟨f, hf.mono h, hqf⟩

theorem mem_value_of_outputAtom {F : BasisAction Γ₁} {σ : Γ₂ ⟶ Γ₁} {label : Tm_ Γ₂}
    {x y : CoherentShape Γ₂} (h : OutputAtom ((abstraction F).pullback σ) label x y) :
    (F.app _ (σ.op, label) x).mem (𝟙 Γ₂) y := by
  obtain ⟨f, i, hf, hlabel, hix, rfl⟩ := h
  have hf' : (abstraction F).mem σ f.lamGenerator :=
    (ΩLower.presheaf_map_mem_id (abstraction F) σ f.lamGenerator).mp hf
  have ⟨g, hg, hfg⟩ := (mem_abstraction F σ f.lamGenerator).mp hf'
  rcases CoherentGraph.lamGenerator_le_iff.mp hfg i with hbot | ⟨j, hname, hin, hout⟩
  · exact (F.app _ (σ.op, label) x).lower (𝟙 Γ₂)
      (le_bot_iff.mpr hbot) ((F.app _ (σ.op, label) x).bottom (𝟙 Γ₂))
  · have hj := hg j
    rw [hname, hlabel] at hj
    exact (F.app _ (σ.op, label) x).lower (𝟙 Γ₂) hout
      ((F.app _ (σ.op, label)).hom.monotone (hin.trans hix) (𝟙 Γ₂) _ hj)

theorem outputAtom_of_mem_value {F : BasisAction Γ₁} {σ : Γ₂ ⟶ Γ₁} {label : Tm_ Γ₂}
    {x y : CoherentShape Γ₂} (h : (F.app _ (σ.op, label) x).mem (𝟙 Γ₂) y) :
    OutputAtom ((abstraction F).pullback σ) label x y :=
  let f := CoherentGraph.single label x y
  ⟨f, ⟨0, Nat.one_pos⟩, (ΩLower.presheaf_map_mem_id _ _ _).mpr ⟨f, fun _ => h, le_rfl⟩,
    rfl, le_rfl, rfl⟩

end BasisAction

noncomputable abbrev IdealAction.operations (E : Env ζ) (ℓ : Nat) := Functor.parameterizedHom
  (ΩIdeal.presheaf (pointedOrder E ℓ)) (ΩIdeal.presheaf (pointedOrder E ℓ))
  (Tm E ℓ)

@[implicit_reducible] def IdealAction.finitary (E : Env ζ) (ℓ : Nat) : Subfunctor (operations E ℓ ⋙ forget Preord) where
  obj _ := {F | ΩIdeal.Finitary F}
  map _ _ h := h.map _

noncomputable abbrev IdealAction.presheaf (E : Env ζ) (ℓ : Nat) := (finitary E ℓ).toPreord

abbrev IdealAction (Γ₁ : CtxCat E ℓ) : Type := (IdealAction.presheaf E ℓ).obj (op Γ₁)

noncomputable def IdealAction.pullback (F : IdealAction Γ₁) (σ : Γ₂ ⟶ Γ₁) : IdealAction Γ₂ :=
  (IdealAction.presheaf E ℓ).map σ.op F

namespace IdealAction

@[simp] theorem app_pullback (F : IdealAction Γ₁)
    (σ₁ : op Γ₁ ⟶ op Γ₂) (σ₂ : Γ₃ ⟶ Γ₂) (label : Tm_ Γ₂) (I : Domain Γ₂) :
    F.val.app _ (σ₁ ≫ σ₂.op, (Tm E ℓ).map σ₂.op label) (I.pullback σ₂) = (F.val.app _ (σ₁, label) I).pullback σ₂ :=
  F.val.naturality_apply σ₂.op (σ₁, label) I

theorem pullback_id (P : IdealAction Γ₁) : P.pullback (𝟙 Γ₁) = P :=
  (IdealAction.presheaf E ℓ).map_id_apply (op Γ₁) P

theorem pullback_pullback (P : IdealAction Γ₁) (σ₁ : Γ₂ ⟶ Γ₁)
    (σ₂ : Γ₃ ⟶ Γ₂) : (P.pullback σ₁).pullback σ₂ = P.pullback (σ₂ ≫ σ₁) :=
  ((IdealAction.presheaf E ℓ).map_comp_apply σ₁.op σ₂.op P).symm

theorem pullback_app (B : IdealAction Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂)
    (label : Tm_ Γ₃) (X : Domain Γ₃) :
    (B.pullback σ₁).val.app _ (σ₂.op, label) X = B.val.app _ ((σ₂ ≫ σ₁).op, label) X := rfl

noncomputable def bottom : IdealAction Γ₁ where
  val.app Γ₂ _ := Preord.ofHom (OrderHom.const _ (⊥ : Domain Γ₂.unop))
  val.naturality σ _ := Preord.ext fun _ => (ΩIdeal.pullback_bot σ.unop).symm
  property _ _ I _ h := ⟨⊥, I.bottom (𝟙 _), h⟩

theorem bottom_le (F : IdealAction Γ₁) : bottom ≤ F :=
  fun _ p I ↦ @bot_le (Domain _) _ _ (F.val.app _ p I)

def IsIdempotent (P : IdealAction Γ₁) : Prop :=
  ∀ ⦃Γ₂ : CtxCat E ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (n : Tm_ Γ₂) (X : Domain Γ₂),
    P.val.app _ (σ.op, n) (P.val.app _ (σ.op, n) X) = P.val.app _ (σ.op, n) X

noncomputable abbrev onBasis (F : IdealAction Γ₁) : BasisAction Γ₁ :=
  (Functor.HomObj.ofNatTrans (ΩIdeal.principalNatTrans (pointedOrder E ℓ))).comp F.val |>.comp
    (Functor.HomObj.ofNatTrans (ΩIdeal.toLowerNatTrans (pointedOrder E ℓ)))

theorem onBasis_isIdealValued (F : IdealAction Γ₁) : F.onBasis.IsIdealValued :=
  fun _ σ label x => (F.val.app _ (σ.op, label) (principalIdeal x)).property

noncomputable def abstraction (F : IdealAction Γ₁) : Domain Γ₁ :=
  F.onBasis.abstraction.toIdeal (BasisAction.abstraction_isDirected F.onBasis_isIdealValued)

@[simp] theorem mem_abstraction (F : IdealAction Γ₂)
    (σ : Γ₁ ⟶ Γ₂) (q : CoherentShape Γ₁) :
    (abstraction F).mem σ q ↔ ∃ f : CoherentGraph Γ₁, F.onBasis.GraphValid σ f ∧ q ≤ f.lamGenerator :=
  BasisAction.mem_abstraction F.onBasis σ q

theorem abstraction_mono {F G : IdealAction Γ₁}
    (h : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (label : Tm_ Γ₂)
      (I : Domain Γ₂), F.val.app _ (σ.op, label) I ≤ G.val.app _ (σ.op, label) I) :
    abstraction F ≤ abstraction G :=
  BasisAction.abstraction_mono fun _ ⟨⟨σ⟩, label⟩ x => h σ label (principalIdeal x)

@[simp]
theorem application_abstraction (F : IdealAction Γ₁) (label : Tm_ Γ₁)
    (X : Domain Γ₁) :
    application (abstraction F) label X = F.val.app _ ((𝟙 Γ₁).op, label) X := by
  ext Γ₂ σ y
  have hnatural : (F.val.app _ ((𝟙 Γ₁).op, label) X).pullback σ =
      F.val.app _ (σ.op, (Tm E ℓ).map σ.op label) (X.pullback σ) := by
    simpa using (F.app_pullback (𝟙 Γ₁).op σ label X).symm
  rw [← ΩIdeal.presheaf_map_mem_id (F.val.app _ ((𝟙 Γ₁).op, label) X), hnatural]
  constructor
  · intro ⟨x, hx, hxy⟩
    exact (F.val.app _ _).hom.monotone
      (ΩLower.principal_le_iff.mpr ((ΩIdeal.presheaf_map_mem_id X σ x).mpr hx)) (𝟙 Γ₂) _
      (hxy.mem_of_outputAtom (F.val.app _ _ (principalIdeal x)).property
        BasisAction.mem_value_of_outputAtom)
  · intro hy
    have ⟨x, hx, hxy⟩ := F.property _ _ (X.pullback σ) hy
    exact ⟨x, (ΩIdeal.presheaf_map_mem_id X σ x).mp hx,
      .entry (BasisAction.outputAtom_of_mem_value hxy)⟩

theorem abstraction_finitary (H : Domain Γ₁ → IdealAction Γ₁)
    (hmono : ∀ {I J : Domain Γ₁}, I ≤ J →
      ∀ (label : Tm_ Γ₁) (X : Domain Γ₁),
        (H I).val.app _ ((𝟙 Γ₁).op, label) X ≤ (H J).val.app _ ((𝟙 Γ₁).op, label) X)
    (hfin : ∀ (I : Domain Γ₁) (label : Tm_ Γ₁)
      (X : Domain Γ₁) {y : CoherentShape Γ₁},
      ((H I).val.app _ ((𝟙 Γ₁).op, label) X).mem (𝟙 Γ₁) y →
        ∃ f, I.mem (𝟙 Γ₁) f ∧
          ((H (principalIdeal f)).val.app _ ((𝟙 Γ₁).op, label) X).mem (𝟙 Γ₁) y)
    (I : Domain Γ₁) {q : CoherentShape Γ₁}
    (hq : (abstraction (H I)).mem (𝟙 Γ₁) q) :
    ∃ f, I.mem (𝟙 Γ₁) f ∧ (abstraction (H (principalIdeal f))).mem (𝟙 Γ₁) q := by
  have ⟨⟨graph, hcoh⟩, hgraph, hq⟩ := (mem_abstraction _ _ _).mp hq
  choose j hj hout using fun i => hfin I (graph.names i) _ (hgraph i)
  have ⟨k, hk, hjk⟩ := ΩLower.IsDirected.exists_upper_fin I.property (𝟙 Γ₁) j hj
  exact ⟨k, hk, (mem_abstraction _ _ _).mpr ⟨⟨graph, hcoh⟩, fun i =>
    hmono (principalIdeal_mono (hjk i)) _ _ (𝟙 Γ₁) _ (hout i), hq⟩⟩

end IdealAction

theorem pullback_abstraction (F : IdealAction Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (IdealAction.abstraction F).pullback σ = IdealAction.abstraction (F.pullback σ) :=
  Subtype.val_injective (BasisAction.pullback_abstraction F.onBasis σ)

theorem pullback_application (I X : Domain Γ₁) (label : Tm_ Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (application I label X).pullback σ₁ =
      application (I.pullback σ₁) ((Tm E ℓ).map σ₁.op label) (X.pullback σ₁) := by
  ext Γ₃ σ₂ y
  rw [ΩIdeal.presheaf_map_mem, mem_application, ← ΩIdeal.pullback_pullback, op_comp,
    Functor.map_comp_apply]
  rfl

noncomputable def applicationAction (F : Domain Γ₁) : IdealAction Γ₁ where
  val.app _ p := Preord.ofHom {
    toFun := application (F.pullback p.1.unop) p.2
    monotone' _ _ h := application_mono (@le_rfl _ _ _) h }
  val.naturality σ p := Preord.ext fun I =>
    (congrArg (fun H => application H ((Tm E ℓ).map σ p.2) (I.pullback σ.unop))
      (ΩIdeal.pullback_pullback F p.1.unop σ.unop).symm).trans
      (pullback_application (F.pullback p.1.unop) I p.2 σ.unop).symm
  property _ := fun (⟨σ⟩, label) => application_argument_finitary (F.pullback σ) label

end Metalean.CoherentShape
