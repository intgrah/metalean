/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Quot.Nat
public import Metalean.SetTheory.ZFC.Aczel
public import Metalean.SetTheory.ZFC.Universe.Sort

public section

namespace ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

theorem Aczel.lam_mem_vonNeumann {κ : Cardinal} (hκ : κ.IsInaccessible)
    {a : ZFSet} {f : ZFSet → ZFSet} (ha : a ∈ V_ κ.ord)
    (hf : ∀ x ∈ a, f x ∈ V_ κ.ord) : Aczel.lam a f ∈ V_ κ.ord := by
  refine sUnion_mem_vonNeumann (image_mem_vonNeumann hκ ha ?_)
  intro x hx
  exact image_mem_vonNeumann hκ (hf x hx) fun y hy =>
    pair_mem_vonNeumann (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le)
      (isTransitive_vonNeumann _ _ ha hx) (isTransitive_vonNeumann _ _ (hf x hx) hy)

theorem Aczel.piMap_mem_vonNeumann {κ : Cardinal} (hκ : κ.IsInaccessible)
    {a b : ZFSet} (ha : a ∈ V_ κ.ord) (hb : ∀ x ∈ a, ZFSet.app b x ∈ V_ κ.ord) :
    Aczel.piMap a b ∈ V_ κ.ord := by
  apply image_mem_vonNeumann hκ (pi_mem_vonNeumann hκ ha hb)
  intro f hf
  exact Aczel.lam_mem_vonNeumann hκ ha fun x hx =>
    isTransitive_vonNeumann _ _ (hb x hx) (app_mem_of_mem_pi hf hx)

theorem Aczel.mem_vonNeumann_of_mem_piMap {κ : Cardinal} (hκ : κ.IsInaccessible)
    {a b f : ZFSet} (ha : a ∈ V_ κ.ord) (hf : f ∈ Aczel.piMap a b)
    (hb : ∀ x ∈ a, Aczel.app f x ∈ V_ κ.ord) : f ∈ V_ κ.ord := by
  obtain ⟨g, hg, rfl⟩ := Aczel.mem_piMap.mp hf
  apply Aczel.lam_mem_vonNeumann hκ ha
  intro x hx
  simpa [Aczel.app_lam hx] using hb x hx

theorem lam_mem_type {n : Nat} {a : ZFSet} {f : ZFSet → ZFSet} (ha : a ∈ U_ n)
    (hf : ∀ x ∈ a, f x ∈ U_ n) : Aczel.lam a f ∈ U_ n :=
  Aczel.lam_mem_vonNeumann (Cardinal.inaccessible_isInaccessible n) ha hf

theorem piMap_mem_type {n : Nat} {a b : ZFSet} (ha : a ∈ U_ n)
    (hb : ∀ x ∈ a, app b x ∈ U_ n) : Aczel.piMap a b ∈ U_ n :=
  Aczel.piMap_mem_vonNeumann (Cardinal.inaccessible_isInaccessible n) ha hb

theorem type_mem_of_mem_piMap {n : Nat} {a b f : ZFSet} (ha : a ∈ U_ n)
    (hf : f ∈ Aczel.piMap a b) (hb : ∀ x ∈ a, Aczel.app f x ∈ U_ n) : f ∈ U_ n :=
  Aczel.mem_vonNeumann_of_mem_piMap (Cardinal.inaccessible_isInaccessible n) ha hf hb

theorem pi_mem_sort_imax {lA lB : Nat} {a b : ZFSet} (ha : a ∈ S_ lA)
    (hb : ∀ x ∈ a, app b x ∈ S_ lB) :
    Aczel.piMap a b ∈ S_ (Nat.imax lA lB) := by
  cases lB with
  | zero => exact Aczel.piMap_mem_truth hb
  | succ m =>
    have hk : Nat.imax lA (m + 1) = Nat.max lA (m + 1) := Nat.imax_succ_right
    have hpos : 1 ≤ Nat.max lA (m + 1) := Nat.le_trans (Nat.le_add_left 1 m) (Nat.le_max_right _ _)
    have hsucc : Nat.max lA (m + 1) = Nat.max lA (m + 1) - 1 + 1 :=
      (Nat.succ_pred_eq_of_pos hpos).symm
    rw [hk, hsucc]
    refine piMap_mem_type (mem_type_of_mem_sort ?_ ha)
      fun x hx => mem_type_of_mem_sort ?_ (hb x hx)
    · exact hsucc ▸ Nat.le_max_left lA (m + 1)
    · exact hsucc ▸ Nat.le_max_right lA (m + 1)

end ZFSet
