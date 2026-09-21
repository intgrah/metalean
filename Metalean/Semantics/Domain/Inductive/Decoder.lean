/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Domain.Decoder.Stages
import Metalean.Semantics.Domain.Decoder.FixedPoint

@[expose] public section

namespace Metalean.CoherentShape.CodeAssignment

open CategoryTheory Presheaf

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ : CtxCat E ℓ}

theorem piLimit_extend_ind_of_rel (code : IndCode Γ) (hrel : code.rel = true)
    (ctorTypes : Fin code.toIndHead.nctors → CoherentShape Γ)
    (n : Tm_ Γ) (X : Domain Γ) :
    (piLimit E ℓ).extend (principalIdeal (indAtom code ctorTypes)) n X =
      (piLimit E ℓ).indRebuild code (fun c => principalIdeal (ctorTypes c)) (𝟙 Γ) n X := by
  rw [extend_principal]
  conv_lhs => rw [← piLimit_fixedPoint]
  change (if code.rel then _ else IdealAction.bottom).val.app _ ((𝟙 Γ).op, n) X = _
  rw [ite_eq_left hrel]
  rfl

theorem piLimit_extend_ind_of_structural (code : IndCode Γ) (hrel : code.rel = true)
    {c : Fin code.toIndHead.nctors} {n : Tm_ Γ} (hg : code.StructGuard c n)
    (ctorTypes : Fin code.toIndHead.nctors → CoherentShape Γ) (X : Domain Γ) :
    (piLimit E ℓ).extend (principalIdeal (indAtom code ctorTypes)) n X =
      (piLimit E ℓ).indBody (principalIdeal (ctorTypes c)) X hg := by
  have hg' := hg.cast code.map_hom_id.symm rfl rfl
  rw [piLimit_extend_ind_of_rel code hrel,
    indRebuild_eq_indBody (piLimit E ℓ) code _ _ _ _ hg']
  exact (piLimit E ℓ).indBody_congr code.map_hom_id rfl rfl
    (ΩIdeal.pullback_id _) rfl hg' hg

theorem piLimit_extend_ind_of_nonstructural (code : IndCode Γ) (hrel : code.rel = true)
    (hns : ∀ c : Fin code.toIndHead.nctors, ¬ (E.get code.η).block.IsStructure code.s c)
    (ctorTypes : Fin code.toIndHead.nctors → CoherentShape Γ)
    (n : Tm_ Γ) (X : Domain Γ) :
    (piLimit E ℓ).extend (principalIdeal (indAtom code ctorTypes)) n X =
      indIdeal code.toIndHead X := by
  rw [piLimit_extend_ind_of_rel code hrel,
    indRebuild_eq_indIdeal (piLimit E ℓ) code _ _ _ _ hns]

theorem piLimit_rawExtend_indValue_of_structural (code : IndCode Γ) (hrel : code.rel = true)
    {c : Fin code.toIndHead.nctors} {n : Tm_ Γ} (hg : code.StructGuard c n)
    (Ts : Fin code.toIndHead.nctors → Domain Γ) (X : Domain Γ) :
    (piLimit E ℓ).rawExtend (RawValue.ind code fun d => (Ts d).val) n X.val =
      ((piLimit E ℓ).indBody (Ts c) X hg).val := by
  ext Γ₂ σ y
  change _ ↔ ((piLimit E ℓ).indBody (Ts c) X hg).mem σ y
  rw [← ΩIdeal.presheaf_map_mem_id _ σ,
    pullback_indBody (piLimit E ℓ) (Ts c) X hg σ (hg.pullback σ), mem_rawExtend]
  constructor
  · intro ⟨q, ⟨ts, hts, hq⟩, x, hx, hy⟩
    have hy' := (piLimit E ℓ).eval_mono_code hq _ (principalIdeal x) (𝟙 Γ₂) y hy
    rw [← extend_principal, piLimit_extend_ind_of_structural _
      ((IndCode.rel_map _ _).trans hrel) (hg.pullback σ)] at hy'
    exact (piLimit E ℓ).indBody_mono
      (ΩLower.principal_le_iff.mpr ((ΩIdeal.presheaf_map_mem_id _ σ _).mpr (hts c)))
      (ΩLower.principal_le_iff.mpr ((ΩIdeal.presheaf_map_mem_id _ σ _).mpr hx))
      (hg.pullback σ) (𝟙 Γ₂) y hy'
  · intro hy
    have ⟨t, ht, hy⟩ := (piLimit E ℓ).indBody_finitary_type (X.pullback σ)
      (hg.pullback σ) ((Ts c).pullback σ) hy
    have ⟨x, hx, hy⟩ := (piLimit E ℓ).indBody_finitary (principalIdeal t)
      (hg.pullback σ) (X.pullback σ) hy
    refine ⟨indAtom (code.map ((Tm E ℓ).map σ.op)) fun _ => t,
      ⟨fun _ => t, fun d => ?_, le_rfl⟩, x, (ΩIdeal.presheaf_map_mem_id _ σ _).mp hx, ?_⟩
    · obtain rfl := hg.witness.struct.ctor_unique d
      exact (ΩIdeal.presheaf_map_mem_id _ σ _).mp ht
    · rwa [← extend_principal, piLimit_extend_ind_of_structural _
        ((IndCode.rel_map _ _).trans hrel) (hg.pullback σ)]

theorem telescope_of_structural_fixed (code : IndCode Γ) (hrel : code.rel = true)
    {c : Fin code.toIndHead.nctors} {n : Tm_ Γ} (hg : code.StructGuard c n)
    (Ts : Fin code.toIndHead.nctors → Domain Γ) (X : Domain Γ)
    (hfix : (piLimit E ℓ).rawExtend (RawValue.ind code fun d => (Ts d).val) n X.val = X.val) :
    ((piLimit E ℓ).telescope (Ts c) (indNames hg)
      fun i => projIdeal (code.ctorHead c) i X).1 =
      fun i => projIdeal (code.ctorHead c) i X := by
  have hbody : (piLimit E ℓ).indBody (Ts c) X hg = X := Subtype.val_injective
    ((piLimit_rawExtend_indValue_of_structural code hrel hg Ts X).symm.trans hfix)
  funext i
  rw [← projIdeal_indBody, hbody]

theorem ctor_proj_of_structural_fixed (code : IndCode Γ) (hrel : code.rel = true)
    {c : Fin code.toIndHead.nctors} {n : Tm_ Γ} (hg : code.StructGuard c n)
    (Ts : Fin code.toIndHead.nctors → Domain Γ) (X : Domain Γ)
    (hfix : (piLimit E ℓ).rawExtend (RawValue.ind code fun d => (Ts d).val) n X.val = X.val)
    (names : Fin (code.ctorHead c).arity → Tm_ Γ) :
    RawValue.ctor (code.ctorHead c) names (fun i => RawValue.proj (code.ctorHead c) i X.val) = X.val := by
  have hbody : ((piLimit E ℓ).indBody (Ts c) X hg).val = X.val :=
    (piLimit_rawExtend_indValue_of_structural code hrel hg Ts X).symm.trans hfix
  rw [← hbody]
  change RawValue.ctor (code.ctorHead c) names
    (fun i => RawValue.proj (code.ctorHead c) i
      (RawValue.ctor (code.ctorHead c) (indNames hg) _)) =
    RawValue.ctor (code.ctorHead c) (indNames hg) _
  simp_rw [RawValue.proj_ctor]
  exact RawValue.ctor_congr_names _ hg.witness.struct names (indNames hg) _

theorem piLimit_rawExtend_indValue_of_nonstructural (code : IndCode Γ) (hrel : code.rel = true)
    (hns : ∀ c : Fin code.toIndHead.nctors, ¬ (E.get code.η).block.IsStructure code.s c)
    (Ts : Fin code.toIndHead.nctors → RawValue Γ) (n : Tm_ Γ) (X : RawValue Γ) :
    (piLimit E ℓ).rawExtend (RawValue.ind code Ts) n X =
      RawValue.indProjection code.toIndHead X :=
  (piLimit E ℓ).rawExtend_eq_map _ fun σ _ ⟨ts, hts, hc⟩ =>
    ⟨_, ⟨ts, hts, le_rfl⟩, hc, fun x => by
      rw [← extend_principal, piLimit_extend_ind_of_nonstructural (code.map ((Tm E ℓ).map σ.op))
        ((IndCode.rel_map _ _).trans hrel) hns ts, indIdeal_principal]
      rfl⟩

end Metalean.CoherentShape.CodeAssignment
