module

public import Metalean.Semantics.Basis.Rank
public import Metalean.Semantics.Domain.Decoder.Locality
public import Metalean.Semantics.Domain.Pi

@[expose] public section

namespace Metalean

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

namespace Shape

def ctorTypeDom : Shape Γ₁ → Shape Γ₁
  | .forallE _ dom _ _ _ _ => dom
  | _ => .bot

def ctorTypeGraph : Shape Γ₁ → Graph Γ₁
  | .forallE _ _ k names ins outs => ⟨k, names, ins, outs⟩
  | _ => .nil

theorem ctorTypeDom_mono {a b : Shape Γ₁} (h : a ≤ b) : a.ctorTypeDom ≤ b.ctorTypeDom := by
  cases h with
  | collapse hb => cases hb <;> exact .bot _
  | forallE ha _ => exact ha
  | _ => exact .refl _

theorem ctorTypeGraph_mono {a b : Shape Γ₁} (h : a ≤ b) :
    a.ctorTypeGraph ≤ b.ctorTypeGraph := by
  cases h with
  | collapse hb => cases hb <;> exact fun i => i.elim0
  | forallE _ hf => exact hf
  | _ => exact Graph.Le.refl _

@[simp] theorem map_ctorTypeDom (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) (a : Shape Γ₁) :
    (a.map arg pi).ctorTypeDom = a.ctorTypeDom.map arg pi := by
  cases a <;> rfl

@[simp] theorem map_ctorTypeGraph (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) (a : Shape Γ₁) :
    (a.map arg pi).ctorTypeGraph = a.ctorTypeGraph.map arg pi := by
  have hnil : (Graph.nil : Graph Γ₁).map arg pi = Graph.nil := by
    simp only [Graph.map, Graph.nil, Graph.mk.injEq, heq_eq_eq, true_and]
    exact ⟨funext fun i => i.elim0, funext fun i => i.elim0, funext fun i => i.elim0⟩
  cases a <;> first | rfl | exact hnil.symm

theorem rank_ctorTypeDom_lt {a : Shape Γ₁} (h : ¬ a.ctorTypeDom = .bot) :
    a.ctorTypeDom.rank < a.rank := by
  cases a with
  | forallE label dom k names ins outs =>
    exact Nat.lt_succ_of_le (le_max_left _ _)
  | _ => exact absurd rfl h

theorem rank_ctorTypeGraph_le (a : Shape Γ₁) : a.ctorTypeGraph.rank ≤ a.rank := by
  cases a with
  | forallE label dom k names ins outs =>
    exact Nat.le_succ_of_le (le_max_right _ _)
  | _ => simp [Graph.rank, ctorTypeGraph, Graph.nil]

theorem IsCoherent.ctorTypeDom {a : Shape Γ₁} (h : IsCoherent Γ₁ a) :
    IsCoherent Γ₁ a.ctorTypeDom := by
  cases h with
  | forallE ha _ _ _ => exact ha
  | _ => exact .bot

theorem IsCoherent.ctorTypeGraph {a : Shape Γ₁} (h : IsCoherent Γ₁ a) :
    Graph.IsCoherent Γ₁ a.ctorTypeGraph := by
  cases h with
  | forallE _ hd hi ho => exact ⟨hd, hi, ho⟩
  | _ => exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

end Shape

noncomputable def CoherentShape.ctorTypeDom (a : CoherentShape Γ₁) : CoherentShape Γ₁ :=
  ⟨a.1.ctorTypeDom, a.2.ctorTypeDom⟩

noncomputable def CoherentShape.ctorTypeGraph (a : CoherentShape Γ₁) : CoherentGraph Γ₁ :=
  ⟨a.1.ctorTypeGraph, a.2.ctorTypeGraph⟩

theorem CoherentShape.ctorTypeDom_mono {a b : CoherentShape Γ₁} (h : a ≤ b) :
    a.ctorTypeDom ≤ b.ctorTypeDom := Shape.ctorTypeDom_mono h

theorem CoherentShape.ctorTypeGraph_mono {a b : CoherentShape Γ₁} (h : a ≤ b) :
    a.ctorTypeGraph.1 ≤ b.ctorTypeGraph.1 := Shape.ctorTypeGraph_mono h

@[simp] theorem CoherentShape.reindex_ctorTypeDom (σ : Γ₂ ⟶ Γ₁) (a : CoherentShape Γ₁) :
    reindex σ a.ctorTypeDom = (reindex σ a).ctorTypeDom :=
  Subtype.val_injective (Shape.map_ctorTypeDom _ _ a.1).symm

@[simp] theorem CoherentShape.reindex_ctorTypeGraph (σ : Γ₂ ⟶ Γ₁) (a : CoherentShape Γ₁) :
    (reindex σ a).ctorTypeGraph = a.ctorTypeGraph.reindex σ :=
  Subtype.val_injective (Shape.map_ctorTypeGraph _ _ a.1)

namespace CoherentShape

namespace RawValue

noncomputable def ctorTypeDom (X : RawValue Γ₁) : RawValue Γ₁ where
  mem σ y := ∃ a : CoherentShape _, X.mem σ a ∧ y ≤ a.ctorTypeDom
  natural σ₁ σ₂ y := fun ⟨a, ha, hy⟩ =>
    ⟨reindex σ₂ a, X.natural σ₁ σ₂ a ha, by
      rw [← CoherentShape.reindex_ctorTypeDom]
      exact Le.reindex σ₂ hy⟩
  bottom σ := ⟨⊥, X.bottom σ, bot_le⟩
  lower _ hyz := fun ⟨a, ha, hz⟩ => ⟨a, ha, hyz.trans hz⟩

theorem ctorTypeDom_mono {X Y : RawValue Γ₁} (h : X ≤ Y) : ctorTypeDom X ≤ ctorTypeDom Y :=
  fun σ _ ⟨a, ha, hy⟩ => ⟨a, h σ a ha, hy⟩

theorem ctorTypeDom_isDirected {X : RawValue Γ₁} (hX : X.IsDirected) :
    (ctorTypeDom X).IsDirected := by
  intro Γ₂ σ y z ⟨a, ha, hy⟩ ⟨b, hb, hz⟩
  have ⟨c, hc, hac, hbc⟩ := hX σ ha hb
  exact ⟨c.ctorTypeDom, ⟨c, hc, le_rfl⟩, hy.trans (CoherentShape.ctorTypeDom_mono hac),
    hz.trans (CoherentShape.ctorTypeDom_mono hbc)⟩

@[simp] theorem ctorTypeDom_pi (label : Ty.Pair Γ₁)
    (A : RawValue Γ₁) (B : BasisAction Γ₁) :
    ctorTypeDom (B.pi label A) = A := by
  ext Γ₂ σ y
  constructor
  · intro ⟨q, ⟨a, f, ha, _, hq⟩, hy⟩
    exact A.lower σ (hy.trans (CoherentShape.ctorTypeDom_mono hq)) ha
  · intro hy
    exact ⟨piGenerator ((Ty.pairPresheaf E ℓ).map σ.op label) y (CoherentGraph.nil Γ₂),
      ⟨y, CoherentGraph.nil Γ₂, hy, fun i => i.elim0, le_rfl⟩, le_rfl⟩

end RawValue

noncomputable def ctorTypeDomIdeal (X : Domain Γ₁) : Domain Γ₁ :=
  ⟨RawValue.ctorTypeDom X.val, RawValue.ctorTypeDom_isDirected X.property⟩

theorem ctorTypeDomIdeal_mono {X Y : Domain Γ₁} (h : X ≤ Y) :
    ctorTypeDomIdeal X ≤ ctorTypeDomIdeal Y :=
  RawValue.ctorTypeDom_mono h

@[simp] theorem pullback_ctorTypeDomIdeal (X : Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (ctorTypeDomIdeal X).pullback σ = ctorTypeDomIdeal (X.pullback σ) :=
  Subtype.val_injective (ΩLower.ext fun _ _ => Iff.rfl)

theorem ctorTypeDomIdeal_finitary : ΩIdeal.IsFinitary (ctorTypeDomIdeal (Γ₁ := Γ₁)) :=
  fun _ _ ⟨a, ha, hle⟩ => ⟨a, ha, a, (ΩLower.mem_principal_id _ _).mpr le_rfl, hle⟩

noncomputable def ctorTypeFibreIdeal (X : Domain Γ₁) (name : Tm_ Γ₁)
    (arg : Domain Γ₁) : Domain Γ₁ where
  val.mem σ y := ∃ a : CoherentShape _, X.mem σ a ∧
    (application (principalIdeal a.ctorTypeGraph.lamGenerator) ((Tm E ℓ).map σ.op name)
      (arg.pullback σ)).mem (𝟙 _) y
  val.natural σ₁ σ₂ y := fun ⟨a, ha, hy⟩ => by
    refine ⟨reindex σ₂ a, X.natural σ₁ σ₂ a ha, ?_⟩
    have h := (application _ _ _).natural (𝟙 _) σ₂ y hy
    rw [Category.comp_id, ← ΩIdeal.presheaf_map_mem_id, pullback_application,
      ΩIdeal.presheaf_map_principal, ΩIdeal.pullback_pullback] at h
    rw [CoherentShape.reindex_ctorTypeGraph, op_comp, Functor.map_comp_apply]
    exact h
  val.bottom σ := ⟨⊥, X.bottom σ, (application _ _ _).bottom _⟩
  val.lower _ hyz := fun ⟨a, ha, hz⟩ => ⟨a, ha, (application _ _ _).lower _ hyz hz⟩
  property := by
    intro Γ₃ σ y z ⟨a, ha, hy⟩ ⟨b, hb, hz⟩
    have ⟨c, hc, hac, hbc⟩ := X.property σ ha hb
    have hyc := application_mono (principalIdeal_mono (CoherentGraph.lamGenerator_le_iff.mpr
      (CoherentShape.ctorTypeGraph_mono hac))) (@le_rfl _ _ _) (𝟙 _) y hy
    have hzc := application_mono (principalIdeal_mono (CoherentGraph.lamGenerator_le_iff.mpr
      (CoherentShape.ctorTypeGraph_mono hbc))) (@le_rfl _ _ _) (𝟙 _) z hz
    have ⟨w, hw, hyw, hzw⟩ := (application _ _ _).property (𝟙 _) hyc hzc
    exact ⟨w, ⟨c, hc, hw⟩, hyw, hzw⟩

@[simp] theorem ctorTypeFibreIdeal_pi (label : Ty.Pair Γ₁)
    (A : Domain Γ₁) (B : IdealAction Γ₁) (name : Tm_ Γ₁) (X : Domain Γ₁) :
    ctorTypeFibreIdeal (pi label A B) name X = B.val.app _ ((𝟙 Γ₁).op, name) X := by
  refine ΩIdeal.ext fun σ y => ?_
  have hnatural : (B.val.app _ ((𝟙 Γ₁).op, name) X).pullback σ =
      B.val.app _ (σ.op, (Tm E ℓ).map σ.op name) (X.pullback σ) := by
    simpa using (B.app_pullback (𝟙 Γ₁).op σ name X).symm
  rw [← ΩIdeal.presheaf_map_mem_id (B.val.app _ ((𝟙 Γ₁).op, name) X) σ, hnatural]
  constructor
  · intro ⟨q, ⟨a, f, _, hf, hq⟩, hy⟩
    have hy' := application_mono (principalIdeal_mono
      (CoherentGraph.lamGenerator_le_iff.mpr (CoherentShape.ctorTypeGraph_mono hq))) (@le_rfl _ _ _) (𝟙 _) y hy
    have hf' : (B.pullback σ).onBasis.GraphValid (𝟙 _) f := by
      intro i
      change (B.val.app _ (σ.op ≫ (𝟙 _).op, f.val.names i)
        (principalIdeal (f.input i))).mem (𝟙 _) (f.output i)
      rw [op_id, Category.comp_id]
      exact hf i
    have hz := graphAction_le_of_valid (B.pullback σ) f hf' (𝟙 _)
      ((Tm E ℓ).map σ.op name) (X.pullback σ) (𝟙 _) y
      (by rw [graphAction_value, CoherentGraph.reindex_id]; exact hy')
    change (B.val.app _ (σ.op ≫ (𝟙 _).op, (Tm E ℓ).map σ.op name)
      (X.pullback σ)).mem (𝟙 _) y at hz
    rwa [op_id, Category.comp_id] at hz
  · intro hy
    have ⟨x, hx, hxy⟩ := B.property _ (σ.op, (Tm E ℓ).map σ.op name) (X.pullback σ) hy
    let f := CoherentGraph.single ((Tm E ℓ).map σ.op name) x y
    refine ⟨piGenerator ((Ty.pairPresheaf E ℓ).map σ.op label) ⊥ f,
      ⟨⊥, f, A.bottom σ, fun _ => hxy, le_rfl⟩, ?_⟩
    rw [mem_application]
    refine ⟨x, hx, .entry ⟨f, ⟨0, Nat.one_pos⟩, ?_, ?_, le_rfl, rfl⟩⟩
    · change ((principalIdeal f.lamGenerator).pullback (𝟙 _)).mem (𝟙 _) f.lamGenerator
      simp
    · change (Tm E ℓ).map σ.op name =
        (Tm E ℓ).map (𝟙 _).op ((Tm E ℓ).map σ.op name)
      simp

theorem ctorTypeFibreIdeal_mono {X Y : Domain Γ₁} (h : X ≤ Y) (name : Tm_ Γ₁)
    {arg arg' : Domain Γ₁} (harg : arg ≤ arg') :
    ctorTypeFibreIdeal X name arg ≤ ctorTypeFibreIdeal Y name arg' := fun σ _ ⟨a, ha, hmem⟩ =>
  ⟨a, h σ a ha, application_mono (@le_rfl _ _ _) (ΩIdeal.pullback_mono harg σ) (𝟙 _) _ hmem⟩

@[simp] theorem pullback_ctorTypeFibreIdeal (X : Domain Γ₁) (name : Tm_ Γ₁)
    (arg : Domain Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (ctorTypeFibreIdeal X name arg).pullback σ₁ =
      ctorTypeFibreIdeal (X.pullback σ₁) ((Tm E ℓ).map σ₁.op name) (arg.pullback σ₁) := by
  refine ΩIdeal.ext fun σ₂ y => exists_congr fun a => and_congr_right fun _ => ?_
  rw [← Functor.map_comp_apply, ← op_comp, ΩIdeal.pullback_pullback, Quiver.Hom.unop_op]

theorem ctorTypeFibreIdeal_finitary_left (name : Tm_ Γ₁) (arg : Domain Γ₁) :
    ΩIdeal.IsFinitary fun X => ctorTypeFibreIdeal X name arg :=
  fun _ _ ⟨a, ha, hmem⟩ => ⟨a, ha, a, (ΩLower.mem_principal_id _ _).mpr le_rfl, hmem⟩

theorem ctorTypeFibreIdeal_finitary_right (X : Domain Γ₁) (name : Tm_ Γ₁) :
    ΩIdeal.IsFinitary (ctorTypeFibreIdeal X name) := by
  intro arg y ⟨a, ha, hmem⟩
  rw [ΩIdeal.pullback_id] at hmem
  have ⟨b, hb, hmem⟩ := application_argument_finitary _ _ _ hmem
  refine ⟨b, hb, a, ha, ?_⟩
  rwa [ΩIdeal.pullback_id]

namespace Domain.CofinalIn

variable {T : Domain Γ₁} {n : Nat}

theorem domain (h : T.CofinalIn (·.1.rank < n)) : (ctorTypeDomIdeal T).CofinalIn (·.1.rank < n) :=
  fun _ σ _ ⟨a, ha, hya⟩ =>
    have ⟨b, hr, hb, hab⟩ := h σ a ha
    have hdom : b.1.ctorTypeDom.rank ≤ b.1.rank := by
      by_cases hbot : b.1.ctorTypeDom = .bot
      · simp [hbot, Shape.rank]
      · exact (Shape.rank_ctorTypeDom_lt hbot).le
    ⟨b.ctorTypeDom, hdom.trans_lt hr, ⟨b, hb, le_rfl⟩, hya.trans (CoherentShape.ctorTypeDom_mono hab)⟩

theorem fibre (h : T.CofinalIn (·.1.rank < n)) (name : Tm_ Γ₁) (X : Domain Γ₁) :
    (ctorTypeFibreIdeal T name X).CofinalIn (·.1.rank < n) :=
  fun _ σ y ⟨a, ha, hy⟩ =>
    have ⟨b, hr, hb, hab⟩ := h σ a ha
    have hyb := application_mono (principalIdeal_mono
      (CoherentGraph.lamGenerator_le_iff.mpr (CoherentShape.ctorTypeGraph_mono hab))) (@le_rfl _ _ _) (𝟙 _) y hy
    have ⟨z, hz, hzmem, hyz⟩ := application_rank_upper _ _ _ (𝟙 _) hyb
    ⟨z, hz.trans_lt ((Shape.rank_ctorTypeGraph_le b.1).trans_lt hr), ⟨b, hb, hzmem⟩, hyz⟩

end Domain.CofinalIn

end CoherentShape

end Metalean
