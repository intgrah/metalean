/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Domain.Decoder.Stages
public import Metalean.Semantics.Domain.Pi

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ : CtxCat E ℓ}

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

theorem Evaluates.isCode {g : CoherentGraph Γ₁} (hg : ∀ i, Shape.IsCode false (g.val.outs i))
    {name : Tm_ Γ₁} {x w : CoherentShape Γ₁} :
    Evaluates (principalIdeal g.lamGenerator) name x w →
    Shape.IsCode false w.1
  | .entry h => by
    obtain ⟨graph, entry, hgraph, _, _, rfl⟩ := h
    rcases CoherentGraph.lamGenerator_le_iff.mp (by simpa using hgraph) entry with hbot | ⟨j, _, _, hout⟩
    · exact .bottom hbot
    · exact Shape.IsCode.of_le hout (hg j)
  | .bottom => .bot
  | .lower h hz => Shape.IsCode.of_le h (isCode hg hz)
  | .join _ hy hz => Shape.IsCode.cSup (isCode hg hy) (isCode hg hz)

theorem isCode_of_mem_application_lamGenerator {g : CoherentGraph Γ₁}
    (hg : ∀ i, Shape.IsCode false (g.1.outs i)) (name : Tm_ Γ₁)
    (Y : Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) {c : CoherentShape Γ₂}
    (hc : (application (principalIdeal g.lamGenerator) name Y).mem σ c) : Shape.IsCode false c.1 := by
  have ⟨_, _, hy⟩ := (mem_application _ _ _ _ _).mp hc
  simp at hy
  exact hy.isCode (g := g.reindex σ) fun i => (hg i).map _ _

namespace CodeAssignment

theorem mem_extend_piStep_pi (F : CodeAssignment E ℓ) (label : Ty.Pair Γ₁) (A : Domain Γ₁)
    (B : IdealAction Γ₁) (n : Tm_ Γ₁) (G : Domain Γ₁) (y : CoherentShape Γ₁) :
    (F.piStep.extend (pi label A B) n G).mem (𝟙 Γ₁) y ↔
      ((F.piAction label A B).val.app _ ((𝟙 Γ₁).op, n) G).mem (𝟙 Γ₁) y := by
  rw [mem_extend]
  constructor
  · intro ⟨c, hc, hy⟩
    have ⟨a, f, ha, hf, hc⟩ := (BasisAction.mem_pi _ _ _ _ _).mp hc
    simp at hc hy
    have hy' := F.piStep.eval_mono_code hc _ G (𝟙 Γ₁) y hy
    exact F.piAction_mono label (ΩLower.principal_le_iff.mpr ha)
      (graphAction_le_of_valid B f hf) _ ((𝟙 Γ₁).op, n) G (𝟙 Γ₁) y hy'
  · intro hy
    have ⟨a, ha, hy⟩ := F.piAction_domain_finitary label n A B G hy
    rw [← applicationAction_abstraction B] at hy
    have ⟨h, hh, hy⟩ := F.piAction_body_finitary label n (principalIdeal a)
      (IdealAction.abstraction B) G hy
    have ⟨f, hf, hhf⟩ := (IdealAction.mem_abstraction _ _ _).mp hh
    have hbody : ∀ {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (m : Tm_ Γ₂)
        (X : Domain Γ₂),
        (applicationAction (principalIdeal h)).val.app _ (σ.op, m) X ≤
          (graphAction f).val.app _ (σ.op, m) X :=
      fun σ m X => application_mono (ΩIdeal.pullback_mono (ΩLower.principal_mono hhf) σ) (@le_rfl _ _ _)
    have hyf : ((F.piAction label (principalIdeal a) (graphAction f)).val.app _
        ((𝟙 Γ₁).op, n) G).mem (𝟙 Γ₁) y :=
      F.piAction_mono label (fun _ _ h ↦ h) hbody _ ((𝟙 Γ₁).op, n) G (𝟙 Γ₁) y hy
    refine ⟨piGenerator label a f, (BasisAction.mem_pi _ _ _ _ _).mpr ⟨a, f, ha, hf, by simp⟩, ?_⟩
    simp
    exact hyf

theorem piAction_value_pullback (F : CodeAssignment E ℓ) (label : Ty.Pair Γ₁)
    (A : Domain Γ₁) (B : IdealAction Γ₁) (n : Tm_ Γ₁)
    (G : Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    ((F.piAction label A B).val.app _ ((𝟙 Γ₁).op, n) G).pullback σ =
      (F.piAction ((Ty.pairPresheaf E ℓ).map σ.op label) (A.pullback σ) (B.pullback σ)).val.app _
        ((𝟙 Γ₂).op, (Tm E ℓ).map σ.op n) (G.pullback σ) := by
  rw [← pullback_piAction]
  change ((F.piAction label A B).val.app _ ((𝟙 Γ₁).op, n) G).pullback σ =
    (F.piAction label A B).val.app _ ((𝟙 Γ₂ ≫ σ).op, (Tm E ℓ).map σ.op n) (G.pullback σ)
  rw [← (F.piAction label A B).app_pullback]
  simp

theorem extend_piStep_pi (F : CodeAssignment E ℓ) (label : Ty.Pair Γ₁) (A : Domain Γ₁)
    (B : IdealAction Γ₁) (n : Tm_ Γ₁) (G : Domain Γ₁) :
    F.piStep.extend (pi label A B) n G =
      (F.piAction label A B).val.app _ ((𝟙 Γ₁).op, n) G := by
  ext Γ₂ σ y
  rw [← ΩIdeal.presheaf_map_mem_id, F.piStep.pullback_extend, pullback_pi,
    ← ΩIdeal.presheaf_map_mem_id _ σ y, piAction_value_pullback]
  exact F.mem_extend_piStep_pi ((Ty.pairPresheaf E ℓ).map σ.op label) _ _ _ _ y

theorem piLimit_fixedPoint : (piLimit E ℓ).piStep = piLimit E ℓ := by
  refine NatTrans.ext (funext fun Γ₁ => Preord.ext fun ⟨a, ha⟩ => ?_)
  exact piStepValue_eq_of_rank
    (fun b hb => by rw [piLimit_app, piStage_value_stable _ b le_rfl (Nat.lt_succ_self _) hb])
    a ha le_rfl

theorem piLimit_extend_pi (label : Ty.Pair Γ₁) (A : Domain Γ₁) (B : IdealAction Γ₁)
    (n : Tm_ Γ₁) (G : Domain Γ₁) :
    (piLimit E ℓ).extend (pi label A B) n G =
      ((piLimit E ℓ).piAction label A B).val.app _ ((𝟙 Γ₁).op, n) G := by
  conv_lhs => rw [← piLimit_fixedPoint]
  exact extend_piStep_pi (piLimit E ℓ) label A B n G

theorem piLimit_value_sort (r : Level ℓ) :
    (piLimit E ℓ).app _ (sortAtom r : CoherentShape Γ₁) = universeAction r.rel := by
  rw [← piLimit_fixedPoint]
  rfl

theorem piLimit_extend_sort (r : Level ℓ) (n : Tm_ Γ₁) (X : Domain Γ₁) :
    (piLimit E ℓ).extend (principalIdeal (sortAtom r)) n X = universeIdeal r.rel X := by
  rw [extend_principal, eval, piLimit_value_sort]
  rfl

theorem piStage_eval_prop (k : Nat) {c : CoherentShape Γ₁} (hc : Shape.IsCode false c.1)
    (n : Tm_ Γ₁) (X : Domain Γ₁) :
    ((piStage E ℓ) k).eval c n X = ⊥ := by
  induction k generalizing Γ₁ with
  | zero => rfl
  | succ k ih =>
    have ⟨a, ha⟩ := c
    cases a with
    | sort => cases Shape.IsCode.eq_true_of_sort hc
    | ind code ctorTypes =>
      have hrel : code.rel = false := by
        cases hc with
        | bottom h => nomatch h
        | ind _ h => exact h
      change (((piStage E ℓ) k).piStepValue (.ind code ctorTypes) ha).val.app _
        ((𝟙 Γ₁).op, n) X = (⊥ : Domain Γ₁)
      simp [piStepValue, hrel, IdealAction.bottom]
    | quot code =>
      have hrel : code.level.rel = false := by
        cases hc with
        | bottom h => nomatch h
        | quot _ h => exact h
      change (quotCodeAction code).val.app _ ((𝟙 Γ₁).op, n) X = (⊥ : Domain Γ₁)
      unfold quotCodeAction
      rw [hrel]
      rfl
    | forallE label a m names ins outs =>
      have hf : ∀ i, Shape.IsCode false (outs i) := by
        cases hc with
        | bottom h => nomatch h
        | forallE_prop hf => exact hf
      apply IdealAction.abstraction_eq_bottom
      intro Γ₃ σ₁ name Y
      apply le_antisymm
      · intro Γ₄ σ₂ y hy
        rcases hy with hy | ⟨hcond, hm, hy⟩
        · exact (ΩIdeal.mem_bot σ₂ y).mpr hy
        rw [CodeAssignment.resultBody] at hy
        have ⟨c, hc, hy⟩ := (mem_extend _ _ _ _ _ _).mp hy
        rw [IdealAction.pullback_app] at hc
        simp only [op_id, unop_id, Category.comp_id] at hc
        erw [graphAction_value] at hc
        rw [ih (isCode_of_mem_application_lamGenerator (fun i => (hf i).map _ _) _ _ (𝟙 Γ₄) hc),
          ΩIdeal.mem_bot] at hy
        exact (ΩIdeal.mem_bot σ₂ y).mpr hy
      · exact @bot_le (Domain _) _ _ _
    | _ => rfl

theorem piLimit_eval_prop {c : CoherentShape Γ₁} (hc : Shape.IsCode false c.1)
    (n : Tm_ Γ₁) (X : Domain Γ₁) :
    (piLimit E ℓ).eval c n X = ⊥ := by
  unfold eval
  rw [piLimit_app]
  exact piStage_eval_prop _ hc n X

theorem mem_piLimit_rawExtend_sort_iff (r : Level ℓ) (X : RawValue Γ₁)
    (n : Tm_ Γ₁) (σ : Γ₂ ⟶ Γ₁) (y : CoherentShape Γ₂) :
    ((piLimit E ℓ).rawExtend (ΩLower.principal (pointedOrder E ℓ) (sortAtom r)) n X).mem σ y ↔
      X.mem σ y ∧ Shape.IsCode r.rel y.1 := by
  have heval (x : CoherentShape Γ₂) : (piLimit E ℓ).eval (sortAtom r)
      ((Tm E ℓ).map σ.op n) (principalIdeal x) = universeIdeal r.rel (principalIdeal x) := by
    rw [eval, piLimit_value_sort]
    rfl
  rw [mem_rawExtend]
  constructor
  · intro ⟨c, hc, x, hx, hy⟩
    have hy' := (piLimit E ℓ).eval_mono_code (show c ≤ sortAtom r from hc) _ (principalIdeal x) (𝟙 Γ₂) y hy
    rw [heval, ΩIdeal.val_mem, mem_universeIdeal_iff, principalIdeal_mem, reindex_id] at hy'
    exact ⟨X.lower σ hy'.1 hx, hy'.2⟩
  · intro ⟨hy, hcode⟩
    refine ⟨sortAtom r, le_rfl, y, hy, ?_⟩
    rw [heval, mem_universeIdeal_iff, principalIdeal_mem, reindex_id]
    exact ⟨le_rfl, hcode⟩

theorem piLimit_rawExtend_prop {X : RawValue Γ₁} (m : Tm_ Γ₁)
    (hX : (piLimit E ℓ).rawExtend (ΩLower.principal (pointedOrder E ℓ) (sortAtom Level.zero))
      m X = X)
    (n : Tm_ Γ₁) (Y : RawValue Γ₁) : (piLimit E ℓ).rawExtend X n Y = ⊥ := by
  apply le_antisymm
  · intro Γ₂ σ y hy
    have ⟨c, hc, x, _, hy⟩ := (mem_rawExtend _ _ _ _ _ _).mp hy
    rw [← hX, mem_piLimit_rawExtend_sort_iff] at hc
    have ⟨_, hcode⟩ := hc
    simp at hcode
    rw [piLimit_eval_prop hcode, ΩIdeal.mem_bot] at hy
    exact (ΩLower.mem_bot _ _).mpr hy
  · intro Γ₂ σ y hy
    exact ((piLimit E ℓ).rawExtend X n Y).lower σ ((ΩLower.mem_bot _ _).mp hy)
      (((piLimit E ℓ).rawExtend X n Y).bottom σ)

theorem piLimit_extend_quot_of_rel (code : QuotCode Γ₁) (hrel : code.level.rel = true)
    (n : Tm_ Γ₁) (X : Domain Γ₁) :
    (piLimit E ℓ).extend (principalIdeal (quotAtom code)) n X = quotIdeal code.η X := by
  rw [extend_principal, ← piLimit_fixedPoint]
  change (quotCodeAction code).val.app _ ((𝟙 Γ₁).op, n) X = _
  unfold quotCodeAction
  rw [hrel]
  rfl

theorem piLimit_rawExtend_quot (code : QuotCode Γ₁) (hrel : code.level.rel = true)
    (n : Tm_ Γ₁) (X : RawValue Γ₁) :
    (piLimit E ℓ).rawExtend (principalIdeal (quotAtom code)).val n X =
      RawValue.quotProjection code.η X :=
  (piLimit E ℓ).rawExtend_eq_map _ fun σ _ hc =>
    ⟨_, (principalIdeal_mem _ _ _).mpr le_rfl, (principalIdeal_mem _ _ _).mp hc, fun x => by
      rw [← extend_principal, reindex_quotAtom,
        piLimit_extend_quot_of_rel (code.map ((Tm E ℓ).map σ.op)) hrel _, quotIdeal_principal]
      rfl⟩

end CodeAssignment

end Metalean.CoherentShape
