/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Basis.Inductive
public import Metalean.Semantics.Domain.Constructors
public import Metalean.Semantics.Domain.Action

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory Presheaf

variable {Γ₁ Γ₂ : CtxCat E ℓ}

def indMap (target : IndHead ζ) (a : CoherentShape Γ₁) : CoherentShape Γ₁ :=
  ⟨a.1.indProjection target, a.2.indProjection target⟩

theorem indMap_mono (target : IndHead ζ) {a b : CoherentShape Γ₁} (h : a ≤ b) :
    indMap target a ≤ indMap target b :=
  Shape.indProjection_mono target h

noncomputable def indHom (E : Env ζ) (ℓ : Nat) (target : IndHead ζ) :
    order E ℓ ⟶ order E ℓ where
  app _ := Preord.ofHom {
    toFun := indMap target
    monotone' := fun _ _ h => indMap_mono target h }
  naturality {_ _} _ := Preord.ext fun a => Subtype.ext (Shape.indProjection_map target _ _ a.1)

namespace RawValue

noncomputable def indProjection (target : IndHead ζ) (X : RawValue Γ₁) : RawValue Γ₁ :=
  X.map (.ofNatTrans (indHom E ℓ target))

@[simp] theorem mem_indProjection (target : IndHead ζ)
    (X : RawValue Γ₂) (σ : Γ₁ ⟶ Γ₂) (y : CoherentShape Γ₁) :
    (X.indProjection target).mem σ y ↔ ∃ x, X.mem σ x ∧ y ≤ indMap target x :=
  ΩLower.mem_map (.ofNatTrans (indHom E ℓ target)) X σ y

theorem indProjection_le (target : IndHead ζ) (X : RawValue Γ₁) :
    X.indProjection target ≤ X := by
  intro Γ₂ σ y ⟨⟨x, _⟩, hx, hy⟩
  exact X.lower σ (hy.trans (Shape.indProjection_le target x)) hx

@[simp] theorem pullback_indProjection (target : IndHead ζ) (X : RawValue Γ₁)
    (σ : Γ₂ ⟶ Γ₁) :
    (X.indProjection target).pullback σ = RawValue.indProjection target (X.pullback σ) :=
  ΩLower.pullback_map (.ofNatTrans (indHom E ℓ target)) X σ

@[simp] theorem indProjection_idempotent (target : IndHead ζ) (X : RawValue Γ₁) :
    (X.indProjection target).indProjection target = X.indProjection target := by
  unfold indProjection
  rw [ΩLower.map_map]
  congr 1
  ext Γ₂ σ a
  exact Subtype.ext (Shape.indProjection_idempotent target a.1)

end RawValue

noncomputable def indIdeal (target : IndHead ζ) (X : Domain Γ₁) : Domain Γ₁ :=
  ⟨RawValue.indProjection target X.val, ΩLower.IsDirected.map _ X.property⟩

theorem indIdeal_mono (target : IndHead ζ) {X Y : Domain Γ₁} (h : X ≤ Y) :
    indIdeal target X ≤ indIdeal target Y :=
  fun σ _ ⟨x, hx, hy⟩ => ⟨x, h σ x hx, hy⟩

theorem indIdeal_finitary (target : IndHead ζ) :
    Presheaf.ΩIdeal.IsFinitary (indIdeal target (Γ₁ := Γ₁)) :=
  fun _ _ ⟨x, hx, hy⟩ => ⟨x, hx, x, (ΩLower.mem_principal_id _ _).mpr le_rfl, hy⟩

theorem indIdeal_idempotent (target : IndHead ζ) (X : Domain Γ₁) :
    indIdeal target (indIdeal target X) = indIdeal target X :=
  Subtype.val_injective (RawValue.indProjection_idempotent target X.val)

@[simp] theorem indIdeal_bottom (target : IndHead ζ) :
    indIdeal target (⊥ : Domain Γ₁) = ⊥ :=
  le_antisymm (fun _ => RawValue.indProjection_le target _) (@bot_le (Domain Γ₁) _ _ _)

@[simp] theorem indIdeal_principal (target : IndHead ζ) (a : CoherentShape Γ₁) :
    indIdeal target (principalIdeal a) = principalIdeal (indMap target a) :=
  Subtype.val_injective (ΩLower.map_principal (.ofNatTrans (indHom E ℓ target)) a)

theorem indMap_ctorMap (head : CtorHead ζ) (names : Fin head.arity → Tm_ Γ₁)
    (fields : Fin head.arity → CoherentShape Γ₁) :
    indMap head.toIndHead (ctorMap head names fields) =
      ctorMap head names (head.projectFields fields fun f =>
        indMap ⟨head.η, head.sig.recursiveTarget f⟩ (fields (Fin.natAdd head.sig.nfields f))) := by
  refine Subtype.ext ?_
  by_cases hs : head.IsStructural E
  · simp only [indMap, val_ctorMap_struct hs, Shape.indProjection, ↓reduceIte]
    exact congrArg _ (funext (head.projectFields_rel₂
      (R := fun (x : Shape Γ₁) (y : CoherentShape Γ₁) => x = y.1) (fun _ => rfl) fun _ _ => rfl))
  · simp only [indMap, val_ctorMap hs, Shape.indProjection, ↓reduceIte]
    exact congrArg _ (funext (head.projectFields_rel₂
      (R := fun (x : Shape Γ₁) (y : CoherentShape Γ₁) => x = y.1) (fun _ => rfl) fun _ _ => rfl))

namespace RawValue

theorem indProjection_ctor (head : CtorHead ζ) (names : Fin head.arity → Tm_ Γ₁)
    (Xs : Fin head.arity → RawValue Γ₁) :
    indProjection head.toIndHead (ctor head names Xs) =
      ctor head names (head.projectFields Xs fun f =>
        indProjection ⟨head.η, head.sig.recursiveTarget f⟩
          (Xs (Fin.natAdd head.sig.nfields f))) := by
  ext Γ₂ σ y
  constructor
  · intro ⟨x, ⟨xs, hxs, hx⟩, hy⟩
    exact ⟨_, head.projectFields_rel₂ (R := fun (X : RawValue Γ₁) x => X.mem σ x) hxs
        fun _ _ => (mem_indProjection _ _ _ _).mpr ⟨_, hxs _, le_rfl⟩,
      hy.trans ((indMap_mono _ hx).trans_eq (indMap_ctorMap head _ xs))⟩
  · intro ⟨zs, hzs, hy⟩
    have hrs (f : Fin head.sig.nrecFields) : ∃ r, (Xs (Fin.natAdd head.sig.nfields f)).mem σ r ∧
        zs (Fin.natAdd head.sig.nfields f) ≤ if head.sig.recursiveArity f = 0 then
          indMap ⟨head.η, head.sig.recursiveTarget f⟩ r else r := by
      have h := hzs (Fin.natAdd head.sig.nfields f)
      rw [CtorHead.projectFields_natAdd] at h
      split_ifs at h ⊢
      · exact (mem_indProjection _ _ _ _).mp h
      · exact ⟨_, h, le_rfl⟩
    choose rs hrs hle using hrs
    let xs := Fin.append (fun f => zs (f.castAdd head.sig.nrecFields)) rs
    refine ⟨ctorMap head _ xs, ⟨xs, fun i => ?_, le_rfl⟩, ?_⟩
    · refine Fin.addCases (fun f => ?_) (fun f => ?_) i
      · simpa [xs] using hzs (f.castAdd _)
      · simpa [xs] using hrs f
    · refine hy.trans ((ctorMap_mono _ _ fun i => ?_).trans_eq (indMap_ctorMap head _ xs).symm)
      refine Fin.addCases (fun f => ?_) (fun f => ?_) i
      · simp [xs]
      · simpa [xs] using hle f

end RawValue

end Metalean.CoherentShape
