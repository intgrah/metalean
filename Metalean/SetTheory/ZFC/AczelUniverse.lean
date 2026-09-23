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

theorem lam_mem_type {n : Nat} {a : ZFSet} {fn : ZFSet → ZFSet} (ha : a ∈ U_ n)
    (hf : ∀ x ∈ a, fn x ∈ U_ n) : Aczel.lam a fn ∈ U_ n := by
  refine sUnion_mem_type (image_mem_type ha ?_)
  intro x hx
  exact image_mem_type (hf x hx) fun y hy =>
    pair_mem_type (mem_type_of_mem ha hx) (mem_type_of_mem (hf x hx) hy)

theorem piMap_mem_type {n : Nat} {a b : ZFSet} (ha : a ∈ U_ n)
    (hb : ∀ x ∈ a, app b x ∈ U_ n) : Aczel.piMap a b ∈ U_ n := by
  apply image_mem_type (pi_mem_type ha hb)
  intro f hf
  apply lam_mem_type ha
  intro x hx
  exact mem_type_of_mem (hb x hx) (app_mem_of_mem_pi hf hx)

theorem type_mem_of_mem_piMap {n : Nat} {a b fn : ZFSet} (ha : a ∈ U_ n)
    (hF : fn ∈ Aczel.piMap a b) (hb : ∀ x ∈ a, Aczel.app fn x ∈ U_ n) : fn ∈ U_ n := by
  obtain ⟨f, hf, rfl⟩ := Aczel.mem_piMap.mp hF
  apply lam_mem_type ha
  intro x hx
  simpa [Aczel.app_lam hx] using hb x hx

theorem pi_mem_sort_imax {lA lB : Nat} {a b : ZFSet} (ha : a ∈ S_ lA)
    (hb : ∀ x ∈ a, app b x ∈ S_ lB) :
    Aczel.piMap a b ∈ S_ (Nat.imax lA lB) := by
  match lB with
  | 0 => exact Aczel.piMap_mem_truth hb
  | m + 1 =>
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
