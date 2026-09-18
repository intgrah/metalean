/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Order.Presheaf.Finitary
public import Metalean.Semantics.Basis.Join
import Mathlib.Order.Filter.Basic

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory MonoidalCategory Presheaf TypeTheory TypeTheory.NaturalModel

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

def sortAtom (r : Level ℓ) : CoherentShape Γ₁ := ⟨.sort r, .sort⟩

theorem sortAtom_le_iff {u v : Level ℓ} :
    (sortAtom u : CoherentShape Γ₁) ≤ sortAtom v ↔ u = v := by
  refine ⟨fun h => ?_, fun h => h ▸ .sort u⟩
  cases h with
  | collapse h => nomatch h
  | sort => rfl

def indAtom (code : IndCode Γ₁) (ctorTypes : Fin code.toIndHead.nctors → CoherentShape Γ₁) :
    CoherentShape Γ₁ :=
  ⟨.ind code fun c => (ctorTypes c).1, .ind fun c => (ctorTypes c).2⟩

@[simp] theorem reindex_indAtom (σ : Γ₂ ⟶ Γ₁) (code : IndCode Γ₁)
    (ctorTypes : Fin code.toIndHead.nctors → CoherentShape Γ₁) :
    reindex σ (indAtom code ctorTypes) =
      indAtom (code.map ((Tm E ℓ).map σ.op)) fun c => reindex σ (ctorTypes c) := rfl

theorem indAtom_congr {code code' : IndCode Γ₁} (h : code = code')
    {ts : Fin code.toIndHead.nctors → CoherentShape Γ₁}
    {ts' : Fin code'.toIndHead.nctors → CoherentShape Γ₁}
    (hts : ∀ c c', c.val = c'.val → ts c = ts' c') : indAtom code ts = indAtom code' ts' := by
  subst h
  exact congrArg (indAtom code) (funext fun c => hts c c rfl)

theorem code_eq_of_indAtom_le {code code' : IndCode Γ₁}
    {ctorTypes : Fin code.toIndHead.nctors → CoherentShape Γ₁}
    {ctorTypes' : Fin code'.toIndHead.nctors → CoherentShape Γ₁}
    (h : indAtom code ctorTypes ≤ indAtom code' ctorTypes') : code = code' := by
  cases h with
  | collapse h => nomatch h
  | ind => rfl

variable (head : CtorHead ζ)

def ctorMap (names : Fin head.arity → Tm_ Γ₁)
    (fields : Fin head.arity → CoherentShape Γ₁) : CoherentShape Γ₁ :=
  if h : head.IsStructural E then
    ⟨.struct head h fun i => (fields i).1, .struct fun i => (fields i).2⟩
  else ⟨.ctor head names fun i => (fields i).1, .ctor h fun i => (fields i).2⟩

variable {head}

theorem val_ctorMap (hns : ¬ head.IsStructural E)
    (names : Fin head.arity → Tm_ Γ₁)
    (fields : Fin head.arity → CoherentShape Γ₁) :
    (ctorMap head names fields).1 = .ctor head names fun i => (fields i).1 := by
  rw [ctorMap, dite_eq_right hns]

theorem val_ctorMap_struct (hs : head.IsStructural E)
    (names : Fin head.arity → Tm_ Γ₁)
    (fields : Fin head.arity → CoherentShape Γ₁) :
    (ctorMap head names fields).1 = .struct head hs fun i => (fields i).1 := by
  rw [ctorMap, dite_eq_left hs]

theorem ctorMap_le_bot_iff {names : Fin head.arity → Tm_ Γ₁}
    {fields : Fin head.arity → CoherentShape Γ₁} :
    ctorMap head names fields ≤ ⊥ ↔ head.IsStructural E ∧ ∀ i, fields i ≤ ⊥ := by
  by_cases hs : head.IsStructural E
  · rw [le_bot_iff, val_ctorMap_struct hs]
    simp [hs, le_bot_iff]
  · rw [le_bot_iff, val_ctorMap hs]
    simp [hs]

theorem ctorMap_names_eq (hns : ¬ head.IsStructural E)
    {names names' : Fin head.arity → Tm_ Γ₁}
    {fields fields' : Fin head.arity → CoherentShape Γ₁}
    (h : ctorMap head names fields ≤ ctorMap head names' fields') : names = names' := by
  rw [le_def, val_ctorMap hns, val_ctorMap hns] at h
  cases h with
  | collapse h => nomatch h
  | ctor => rfl

theorem ctorMap_le_field {names names' : Fin head.arity → Tm_ Γ₁}
    {fields fields' : Fin head.arity → CoherentShape Γ₁}
    (h : ctorMap head names fields ≤ ctorMap head names' fields') (i : Fin head.arity) :
    fields i ≤ fields' i := by
  by_cases hs : head.IsStructural E
  · rw [le_def, val_ctorMap_struct hs, val_ctorMap_struct hs] at h
    cases h with
    | collapse hbot => exact (le_bot_iff.mpr (Basis.IsBottom.struct_iff.mp hbot i)).trans bot_le
    | struct hle => exact hle i
  · rw [le_def, val_ctorMap hs, val_ctorMap hs] at h
    cases h with
    | collapse h => nomatch h
    | ctor hle => exact hle i

theorem ctorMap_head_eq {head' : CtorHead ζ}
    {names : Fin head.arity → Tm_ Γ₁} {fields : Fin head.arity → CoherentShape Γ₁}
    {names' : Fin head'.arity → Tm_ Γ₁} {fields' : Fin head'.arity → CoherentShape Γ₁}
    (h : ctorMap head names fields ≤ ctorMap head' names' fields') :
    ctorMap head names fields ≤ ⊥ ∨ head = head' := by
  by_cases hs : head.IsStructural E
  · rw [le_def, val_ctorMap_struct hs] at h
    by_cases hs' : head'.IsStructural E
    · rw [val_ctorMap_struct hs'] at h
      cases h with
      | collapse hbot => exact .inl (by rw [le_bot_iff, val_ctorMap_struct hs]; exact hbot)
      | struct => exact .inr rfl
    · rw [val_ctorMap hs'] at h
      exact .inl (by
        rw [le_bot_iff, val_ctorMap_struct hs]
        cases h with | collapse h => exact h)
  · rw [le_def, val_ctorMap hs] at h
    by_cases hs' : head'.IsStructural E
    · rw [val_ctorMap_struct hs'] at h
      nomatch h
    · rw [val_ctorMap hs'] at h
      cases h with
      | collapse h => nomatch h
      | ctor => exact .inr rfl

theorem ctorMap_le_inv {names : Fin head.arity → Tm_ Γ₁}
    {fields : Fin head.arity → CoherentShape Γ₁} {z : CoherentShape Γ₁}
    (h : ctorMap head names fields ≤ z) :
    ctorMap head names fields ≤ ⊥ ∨
      ∃ fields' : Fin head.arity → CoherentShape Γ₁,
        z = ctorMap head names fields' ∧ ∀ i, fields i ≤ fields' i := by
  have ⟨z, hz⟩ := z
  by_cases hs : head.IsStructural E
  · rw [le_def, val_ctorMap_struct hs] at h
    cases h with
    | collapse hbot => exact .inl (by rw [le_bot_iff, val_ctorMap_struct hs]; exact hbot)
    | struct hfields =>
      have .struct hcoherent := hz
      exact .inr ⟨fun i => ⟨_, hcoherent i⟩,
        Subtype.ext (val_ctorMap_struct hs names fun i => ⟨_, hcoherent i⟩).symm, hfields⟩
  · rw [le_def, val_ctorMap hs] at h
    cases h with
    | collapse h => nomatch h
    | ctor hfields =>
      have .ctor _ hcoherent := hz
      exact .inr ⟨fun i => ⟨_, hcoherent i⟩,
        Subtype.ext (val_ctorMap hs names fun i => ⟨_, hcoherent i⟩).symm, hfields⟩

variable (head)

theorem ctorMap_mono (names : Fin head.arity → Tm_ Γ₁)
    {fields fields' : Fin head.arity → CoherentShape Γ₁} (h : ∀ i, fields i ≤ fields' i) :
    ctorMap head names fields ≤ ctorMap head names fields' := by
  by_cases hs : head.IsStructural E
  · rw [le_def, val_ctorMap_struct hs, val_ctorMap_struct hs]
    exact Basis.Le.struct h
  · rw [le_def, val_ctorMap hs, val_ctorMap hs]
    exact Basis.Le.ctor h

@[simp] theorem reindex_ctorMap (names : Fin head.arity → Tm_ Γ₁)
    (fields : Fin head.arity → CoherentShape Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    reindex σ (ctorMap head names fields) =
      ctorMap head (fun i => (Tm E ℓ).map σ.op (names i)) fun i => reindex σ (fields i) := by
  dsimp only [ctorMap]
  split_ifs <;> rfl

namespace RawValue

def ind (code : IndCode Γ₁) (Ts : Fin code.toIndHead.nctors → RawValue Γ₁) : RawValue Γ₁ where
  mem σ y := ∃ ts : Fin code.toIndHead.nctors → CoherentShape _, (∀ c, (Ts c).mem σ (ts c)) ∧
    y ≤ indAtom (code.map ((Tm E ℓ).map σ.op)) ts
  natural σ₁ σ₂ y := fun ⟨ts, hts, hy⟩ =>
    ⟨fun c => reindex σ₂ (ts c), fun c => (Ts c).natural σ₁ σ₂ _ (hts c),
      (Le.reindex σ₂ hy).trans_eq ((reindex_indAtom σ₂ _ ts).trans
        (indAtom_congr (IndCode.map_comp_hom σ₁ σ₂ code).symm fun _ _ hcc => by
          rw [Fin.ext hcc]))⟩
  bottom σ := ⟨fun _ => ⊥, fun c => (Ts c).bottom σ, bot_le⟩
  lower σ hyz := fun ⟨ts, hts, hz⟩ => ⟨ts, hts, hyz.trans hz⟩

@[simp] theorem mem_ind (code : IndCode Γ₁) (Ts : Fin code.toIndHead.nctors → RawValue Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (y : CoherentShape Γ₂) :
    (ind code Ts).mem σ y ↔ ∃ ts : Fin code.toIndHead.nctors → CoherentShape Γ₂,
      (∀ c, (Ts c).mem σ (ts c)) ∧ y ≤ indAtom (code.map ((Tm E ℓ).map σ.op)) ts :=
  Iff.rfl

theorem ind_mono (code : IndCode Γ₁) {Ts Us : Fin code.toIndHead.nctors → RawValue Γ₁}
    (h : ∀ c, Ts c ≤ Us c) : ind code Ts ≤ ind code Us :=
  fun σ _ ⟨ts, hts, hy⟩ => ⟨ts, fun c => h c σ _ (hts c), hy⟩

@[simp] theorem pullback_ind (code : IndCode Γ₁) (Ts : Fin code.toIndHead.nctors → RawValue Γ₁)
    (σ₁ : Γ₂ ⟶ Γ₁) :
    (ind code Ts).pullback σ₁ =
      ind (code.map ((Tm E ℓ).map σ₁.op)) fun c => (Ts c).pullback σ₁ := by
  ext Γ₃ σ₂ y
  simp only [ΩLower.pullback, mem_ind]
  refine exists_congr fun ts => and_congr Iff.rfl (Iff.of_eq (congrArg (y ≤ ·) ?_))
  exact indAtom_congr (IndCode.map_comp_hom σ₁ σ₂ code)
    fun _ _ hcc => by rw [Fin.ext hcc]

theorem code_eq_of_ind_eq {code code' : IndCode Γ₁}
    {Ts : Fin code.toIndHead.nctors → RawValue Γ₁}
    {Us : Fin code'.toIndHead.nctors → RawValue Γ₁} (h : ind code Ts = ind code' Us) :
    code = code' := by
  have hmem : (ind code Ts).mem (𝟙 Γ₁) (indAtom (code.map ((Tm E ℓ).map (𝟙 Γ₁).op)) fun _ => ⊥) :=
    ⟨fun _ => ⊥, fun c => (Ts c).bottom _, le_rfl⟩
  have ⟨ts, _, hle⟩ := h ▸ hmem
  have h := code_eq_of_indAtom_le hle
  rwa [IndCode.map_hom_id, IndCode.map_hom_id] at h

theorem ind_congr {code code' : IndCode Γ₁} (h : code = code')
    {Ts : Fin code.toIndHead.nctors → RawValue Γ₁} {Us : Fin code'.toIndHead.nctors → RawValue Γ₁}
    (hTs : ∀ c c', c.val = c'.val → Ts c = Us c') : ind code Ts = ind code' Us := by
  subst h
  exact congrArg (ind code) (funext fun c => hTs c c rfl)

theorem ind_isDirected (code : IndCode Γ₁) {Ts : Fin code.toIndHead.nctors → RawValue Γ₁}
    (hTs : ∀ c, (Ts c).IsDirected) : (ind code Ts).IsDirected := by
  intro Γ₂ σ a b ⟨ts, hts, ha⟩ ⟨us, hus, hb⟩
  choose vs hv htv huv using fun c => hTs c σ (hts c) (hus c)
  exact ⟨indAtom (code.map ((Tm E ℓ).map σ.op)) vs, ⟨vs, hv, le_rfl⟩,
    ha.trans (.ind htv), hb.trans (.ind huv)⟩

def ctor (names : Fin head.arity → Tm_ Γ₁)
    (Xs : Fin head.arity → RawValue Γ₁) : RawValue Γ₁ where
  mem σ y := ∃ xs : Fin head.arity → CoherentShape _, (∀ i, (Xs i).mem σ (xs i)) ∧
    y ≤ ctorMap head (fun i => (Tm E ℓ).map σ.op (names i)) xs
  natural σ₁ σ₂ y := fun ⟨xs, hxs, hy⟩ =>
    ⟨fun i => reindex σ₂ (xs i), fun i => (Xs i).natural σ₁ σ₂ _ (hxs i), by
      simpa using Le.reindex σ₂ hy⟩
  bottom σ := ⟨fun _ => ⊥, fun i => (Xs i).bottom σ, bot_le⟩
  lower σ hyz := fun ⟨xs, hxs, hz⟩ => ⟨xs, hxs, hyz.trans hz⟩

@[simp] theorem mem_ctor (names : Fin head.arity → Tm_ Γ₁)
    (Xs : Fin head.arity → RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁) (y : CoherentShape Γ₂) :
    (ctor head names Xs).mem σ y ↔ ∃ xs : Fin head.arity → CoherentShape Γ₂,
      (∀ i, (Xs i).mem σ (xs i)) ∧
        y ≤ ctorMap head (fun i => (Tm E ℓ).map σ.op (names i)) xs :=
  Iff.rfl

theorem ctor_congr_names (hs : head.IsStructural E)
    (names names' : Fin head.arity → Tm_ Γ₁)
    (Xs : Fin head.arity → RawValue Γ₁) : ctor head names Xs = ctor head names' Xs :=
  ΩLower.ext fun _ y => exists_congr fun xs => and_congr_right fun _ =>
    Iff.of_eq (congrArg (y ≤ ·) (Subtype.ext ((val_ctorMap_struct hs _ xs).trans
      (val_ctorMap_struct hs _ xs).symm)))

theorem ctor_mono (names : Fin head.arity → Tm_ Γ₁)
    {Xs Ys : Fin head.arity → RawValue Γ₁} (h : ∀ i, Xs i ≤ Ys i) :
    ctor head names Xs ≤ ctor head names Ys :=
  fun σ _ ⟨xs, hxs, hy⟩ => ⟨xs, fun i => h i σ _ (hxs i), hy⟩

@[simp] theorem pullback_ctor (names : Fin head.arity → Tm_ Γ₁)
    (Xs : Fin head.arity → RawValue Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (ctor head names Xs).pullback σ₁ =
      ctor head (fun i => (Tm E ℓ).map σ₁.op (names i)) fun i => (Xs i).pullback σ₁ := by
  ext Γ₃ σ₂ y
  simp [ΩLower.pullback]

theorem ctor_isDirected (names : Fin head.arity → Tm_ Γ₁)
    {Xs : Fin head.arity → RawValue Γ₁} (hXs : ∀ i, (Xs i).IsDirected) :
    (ctor head names Xs).IsDirected := by
  intro Γ₂ σ a b ⟨xs, hxs, ha⟩ ⟨ys, hys, hb⟩
  choose zs hz hxz hyz using fun i => hXs i σ (hxs i) (hys i)
  exact ⟨ctorMap head _ zs, ⟨zs, hz, le_rfl⟩, ha.trans (ctorMap_mono _ _ hxz),
    hb.trans (ctorMap_mono _ _ hyz)⟩

noncomputable def proj (i : Fin head.arity) (X : RawValue Γ₁) : RawValue Γ₁ where
  mem σ y := y ≤ ⊥ ∨ ∃ (names : Fin head.arity → Tm_ _)
    (fields : Fin head.arity → CoherentShape _),
    X.mem σ (ctorMap head names fields) ∧ y ≤ fields i
  natural σ₁ σ₂ y
    | .inl hy => .inl (le_bot_iff.mpr (le_bot_iff.mp (Le.reindex σ₂ hy)))
    | .inr ⟨names, fields, hX, hy⟩ =>
      .inr ⟨fun j => (Tm E ℓ).map σ₂.op (names j), fun j => reindex σ₂ (fields j),
        by simpa using X.natural σ₁ σ₂ _ hX, Le.reindex σ₂ hy⟩
  bottom _ := .inl le_rfl
  lower _ hyz
    | .inl hz => .inl (hyz.trans hz)
    | .inr ⟨names, fields, hX, hz⟩ => .inr ⟨names, fields, hX, hyz.trans hz⟩

@[simp] theorem mem_proj (i : Fin head.arity) (X : RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (y : CoherentShape Γ₂) :
    (proj head i X).mem σ y ↔ y ≤ ⊥ ∨ ∃ (names : Fin head.arity → Tm_ Γ₂)
      (fields : Fin head.arity → CoherentShape Γ₂),
      X.mem σ (ctorMap head names fields) ∧ y ≤ fields i :=
  Iff.rfl

theorem proj_mono (i : Fin head.arity) {X Y : RawValue Γ₁} (h : X ≤ Y) :
    proj head i X ≤ proj head i Y := by
  rintro Γ₂ σ y (hy | ⟨names, fields, hX, hy⟩)
  · exact Or.inl hy
  · exact Or.inr ⟨names, fields, h σ _ hX, hy⟩

@[simp] theorem pullback_proj (i : Fin head.arity) (X : RawValue Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (proj head i X).pullback σ = proj head i (X.pullback σ) :=
  ΩLower.ext fun _ _ => Iff.rfl

theorem proj_isDirected (i : Fin head.arity) {X : RawValue Γ₁} (hX : X.IsDirected) :
    (proj head i X).IsDirected := by
  rintro Γ₂ σ a b (ha | ⟨names, fields, hXa, ha⟩) hb
  · exact ⟨b, hb, ha.trans bot_le, le_rfl⟩
  rcases hb with hb | ⟨names₁, fields₁, hXb, hb⟩
  · exact ⟨a, Or.inr ⟨names, fields, hXa, ha⟩, le_rfl, hb.trans bot_le⟩
  have ⟨z, hXz, hza, hzb⟩ := hX σ hXa hXb
  rcases ctorMap_le_inv hza with hbot | ⟨fields', hzeq, hle⟩
  · exact ⟨b, Or.inr ⟨names₁, fields₁, hXb, hb⟩,
      ha.trans (((ctorMap_le_bot_iff.mp hbot).2 i).trans bot_le), le_rfl⟩
  subst hzeq
  exact ⟨fields' i, Or.inr ⟨names, fields', hXz, le_rfl⟩, ha.trans (hle i),
    hb.trans (ctorMap_le_field hzb i)⟩

theorem proj_eventually (i : Fin head.arity) {I : RawValue Γ₁} {y : CoherentShape Γ₁}
    (hy : (proj head i I).mem (𝟙 Γ₁) y) :
    ∀ᶠ J in I.approximations, (proj head i J).mem (𝟙 Γ₁) y := by
  rcases hy with hy | ⟨names, fields, hI, hy⟩
  · exact Filter.Eventually.of_forall fun _ => Or.inl hy
  · exact (ΩLower.eventually_mem hI).mono fun _ hJ => Or.inr ⟨names, fields, hJ, hy⟩

theorem proj_ctor (names : Fin head.arity → Tm_ Γ₁)
    (Xs : Fin head.arity → RawValue Γ₁) (i : Fin head.arity) :
    proj head i (ctor head names Xs) = Xs i := by
  refine ΩLower.ext fun σ y => ⟨?_, ?_⟩
  · rintro (hy | ⟨names₁, fields₁, ⟨xs, hxs, hle⟩, hy⟩)
    · exact (Xs i).lower σ hy ((Xs i).bottom σ)
    · exact (Xs i).lower σ (hy.trans (ctorMap_le_field hle i)) (hxs i)
  · intro hy
    refine Or.inr ⟨fun j => (Tm E ℓ).map σ.op (names j),
      Function.update (fun _ => ⊥) i y, ⟨Function.update (fun _ => ⊥) i y, fun j => ?_, le_rfl⟩,
      by rw [Function.update_self]⟩
    rcases eq_or_ne j i with rfl | hj
    · rwa [Function.update_self]
    · rw [Function.update_of_ne hj]
      exact (Xs j).bottom σ

@[simp] theorem proj_bot (i : Fin head.arity) : proj head i (⊥ : RawValue Γ₁) = ⊥ := by
  apply le_antisymm
  · rintro Γ₂ σ y (hy | ⟨names, fields, hX, hy⟩)
    · exact hy
    · exact hy.trans ((ctorMap_le_bot_iff.mp ((ΩLower.mem_bot _ _).mp hX)).2 i)
  · intro Γ₂ σ y hy
    exact Or.inl hy

@[simp] theorem ctor_bot (hs : head.IsStructural E)
    (names : Fin head.arity → Tm_ Γ₁) :
    ctor head names (fun _ => (⊥ : RawValue Γ₁)) = ⊥ := by
  apply le_antisymm
  · intro Γ₂ σ y ⟨fields, hf, hy⟩
    exact hy.trans (ctorMap_le_bot_iff.mpr ⟨hs, fun i => (ΩLower.mem_bot _ _).mp (hf i)⟩)
  · intro Γ₂ σ y hy
    exact (ctor head names fun _ => (⊥ : RawValue Γ₁)).lower σ hy
      ((ctor head names fun _ => (⊥ : RawValue Γ₁)).bottom σ)

end RawValue

noncomputable def ctorIdeal (names : Fin head.arity → Tm_ Γ₁)
    (Xs : Fin head.arity → Domain Γ₁) : Domain Γ₁ :=
  ⟨RawValue.ctor head names fun i => (Xs i).val,
    RawValue.ctor_isDirected head names fun i => (Xs i).property⟩

theorem ctorIdeal_finitary (names : Fin head.arity → Tm_ Γ₁)
    (fields : Fin head.arity → Domain Γ₁ → Domain Γ₁)
    (hf : ∀ i, ΩIdeal.IsFinitary (fields i)) (hm : ∀ i, Monotone (fields i)) :
    ΩIdeal.IsFinitary fun X => ctorIdeal head names fun i => fields i X := by
  intro X y ⟨xs, hxs, hy⟩
  choose zs hzs hxsz using fun i => hf i X (hxs i)
  have ⟨x, hx, hle⟩ := ΩLower.IsDirected.exists_upper_fin X.property (𝟙 Γ₁) zs hzs
  exact ⟨x, hx, xs,
    fun i => hm i (principalIdeal_mono (hle i)) (𝟙 Γ₁) (xs i) (hxsz i), hy⟩

@[simp] theorem pullback_ctorIdeal (names : Fin head.arity → Tm_ Γ₁)
    (Xs : Fin head.arity → Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (ctorIdeal head names Xs).pullback σ =
      ctorIdeal head (fun i => (Tm E ℓ).map σ.op (names i))
        fun i => (Xs i).pullback σ :=
  Subtype.val_injective (RawValue.pullback_ctor head names (fun i => (Xs i).val) σ)

noncomputable def projIdeal (i : Fin head.arity) (X : Domain Γ₁) : Domain Γ₁ :=
  ⟨RawValue.proj head i X.val, RawValue.proj_isDirected head i X.property⟩

theorem projIdeal_mono (i : Fin head.arity) {X Y : Domain Γ₁} (h : X ≤ Y) :
    projIdeal head i X ≤ projIdeal head i Y :=
  RawValue.proj_mono head i h

@[simp] theorem pullback_projIdeal (i : Fin head.arity) (X : Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (projIdeal head i X).pullback σ = projIdeal head i (X.pullback σ) :=
  Subtype.val_injective (RawValue.pullback_proj head i X.val σ)

theorem projIdeal_finitary (i : Fin head.arity) :
    ΩIdeal.IsFinitary (projIdeal head i (Γ₁ := Γ₁)) := by
  rintro X y (hy | ⟨names, fields, hX, hy⟩)
  · exact ⟨⊥, X.bottom (𝟙 Γ₁), Or.inl hy⟩
  · exact ⟨ctorMap head names fields, hX,
      Or.inr ⟨names, fields, (ΩLower.mem_principal_id _ _).mpr le_rfl, hy⟩⟩

@[simp] theorem projIdeal_bottom (i : Fin head.arity) :
    projIdeal head i (⊥ : Domain Γ₁) = ⊥ :=
  Subtype.val_injective (RawValue.proj_bot head i)

@[simp] theorem ctorIdeal_bottom (hs : head.IsStructural E)
    (names : Fin head.arity → Tm_ Γ₁) :
    ctorIdeal head names (fun _ => (⊥ : Domain Γ₁)) = ⊥ :=
  Subtype.val_injective (RawValue.ctor_bot head hs names)

end Metalean.CoherentShape
