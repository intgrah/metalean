/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.ZFC.VonNeumann
public import Mathlib.SetTheory.Cardinal.Regular
public import Metalean.SetTheory.ZFC.Function
import Metalean.Grind

public section

universe u v

namespace ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {o : Ordinal.{u}} {κ : Cardinal.{u}} {x y a b : ZFSet.{u}}

theorem empty_mem_vonNeumann (ho : 0 < o) : (∅ : ZFSet) ∈ V_ o := by
  simpa [mem_vonNeumann] using ho

theorem omega_mem_vonNeumann (ho : Ordinal.omega0 < o) : omega ∈ V_ o := by
  apply mem_vonNeumann.mpr
  apply lt_of_le_of_lt (Ordinal.iSup_le fun i => ?_) ho
  have hrank (k : Nat) : Order.succ (PSet.ofNat k).rank < Ordinal.omega0 := by
    induction k with
    | zero =>
      simp!
    | succ k ih =>
      rw [PSet.ofNat, PSet.rank_insert]
      exact Ordinal.isSuccLimit_omega0.succ_lt (max_lt ih ((Order.lt_succ _).trans ih))
  exact (hrank i.down).le

theorem singleton_mem_vonNeumann (ho : Order.IsSuccLimit o) (hx : x ∈ V_ o) :
    {x} ∈ V_ o := by
  simpa [mem_vonNeumann] using ho.succ_lt (mem_vonNeumann.mp hx)

theorem powerset_mem_vonNeumann (ho : Order.IsSuccLimit o) (hx : x ∈ V_ o) :
    powerset x ∈ V_ o := by
  simpa [mem_vonNeumann] using ho.succ_lt (mem_vonNeumann.mp hx)

theorem pairing_mem_vonNeumann (ho : Order.IsSuccLimit o)
    (hx : x ∈ V_ o) (hy : y ∈ V_ o) : {x, y} ∈ V_ o := by
  rw [mem_vonNeumann, rank_pair]
  exact max_lt (ho.succ_lt (mem_vonNeumann.mp hx)) (ho.succ_lt (mem_vonNeumann.mp hy))

theorem pair_mem_vonNeumann (ho : Order.IsSuccLimit o)
    (hx : x ∈ V_ o) (hy : y ∈ V_ o) : pair x y ∈ V_ o :=
  pairing_mem_vonNeumann ho (singleton_mem_vonNeumann ho hx) (pairing_mem_vonNeumann ho hx hy)

theorem union_mem_vonNeumann (hx : x ∈ V_ o) (hy : y ∈ V_ o) : x ∪ y ∈ V_ o := by
  rw [mem_vonNeumann, rank_union]
  exact max_lt (mem_vonNeumann.mp hx) (mem_vonNeumann.mp hy)

theorem sUnion_mem_vonNeumann (hx : x ∈ V_ o) : ⋃₀ x ∈ V_ o :=
  mem_vonNeumann.mpr ((rank_sUnion_le x).trans_lt (mem_vonNeumann.mp hx))

theorem range_mem_vonNeumann {ι : Type v} [Small.{u} ι] {f : ι → ZFSet.{u}}
    (ho : Order.IsSuccLimit o)
    (hι : Cardinal.lift.{u} (Cardinal.mk ι) < (Ordinal.lift.{v} o).cof)
    (hf : ∀ i, f i ∈ V_ o) : range f ∈ V_ o := by
  rw [mem_vonNeumann, rank_range]
  exact Ordinal.lift_iSup_lt_of_lt_cof hι fun i => ho.succ_lt (mem_vonNeumann.mp (hf i))

theorem card_lt_of_mem_vonNeumann (hκ : κ.IsInaccessible) (hx : x ∈ V_ κ.ord) :
    card x < κ := by
  apply (card_mono (subset_vonNeumann_self x)).trans_lt
  rw [card_vonNeumann, ← hκ.preBeth_ord]
  exact Cardinal.preBeth_strictMono (mem_vonNeumann.mp hx)

theorem image_mem_vonNeumann_of_lt_cof {f : ZFSet → ZFSet} (ho : Order.IsSuccLimit o)
    (hx : card x < o.cof) (hf : ∀ y ∈ x, f y ∈ V_ o) : image f x ∈ V_ o := by
  let g : Shrink x → ZFSet := fun i => f ((equivShrink x).symm i).1
  have himage : image f x = range g := by
    ext y
    rw [mem_image, mem_range]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨equivShrink x ⟨z, hz⟩, by simp [g]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨((equivShrink x).symm i).1, ((equivShrink x).symm i).2, rfl⟩
  rw [mem_vonNeumann, himage, rank_range]
  apply Ordinal.iSup_lt_of_lt_cof
  · exact hx
  · intro i
    exact ho.succ_lt (mem_vonNeumann.mp (hf _ ((equivShrink x).symm i).2))

theorem image_mem_vonNeumann {f : ZFSet → ZFSet} (hκ : κ.IsInaccessible)
    (hx : x ∈ V_ κ.ord) (hf : ∀ y ∈ x, f y ∈ V_ κ.ord) : image f x ∈ V_ κ.ord :=
  image_mem_vonNeumann_of_lt_cof (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le)
    (by simpa [hκ.isRegular.cof_ord] using card_lt_of_mem_vonNeumann hκ hx) hf

theorem prod_mem_vonNeumann (ho : Order.IsSuccLimit o)
    (hx : x ∈ V_ o) (hy : y ∈ V_ o) : prod x y ∈ V_ o := by
  rw [prod]
  exact mem_vonNeumann_of_subset sep_subset
    (powerset_mem_vonNeumann ho (powerset_mem_vonNeumann ho (union_mem_vonNeumann hx hy)))

theorem fst_mem_vonNeumann (ho : 0 < o) {p : ZFSet} (hp : p ∈ V_ o) : fst p ∈ V_ o := by
  by_cases h : ∃ x y, p = pair x y
  · obtain ⟨x, y, rfl⟩ := h
    have hs : {x} ∈ V_ o := isTransitive_vonNeumann _ _ hp (by simp [pair])
    exact isTransitive_vonNeumann _ _ hs (by simp)
  · rw [fst, dite_eq_right h]
    exact empty_mem_vonNeumann ho

theorem snd_mem_vonNeumann (ho : 0 < o) {p : ZFSet} (hp : p ∈ V_ o) : snd p ∈ V_ o := by
  by_cases h : ∃ x y, p = pair x y
  · obtain ⟨x, y, rfl⟩ := h
    have hs : {x, y} ∈ V_ o := isTransitive_vonNeumann _ _ hp (by simp [pair])
    exact isTransitive_vonNeumann _ _ hs (by simp)
  · rw [snd, dite_eq_right h]
    exact empty_mem_vonNeumann ho

theorem pi_mem_vonNeumann (hκ : κ.IsInaccessible)
    (ha : a ∈ V_ κ.ord) (hb : ∀ x ∈ a, app b x ∈ V_ κ.ord) : pi a b ∈ V_ κ.ord :=
  mem_vonNeumann_of_subset sep_subset
    (powerset_mem_vonNeumann (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le)
      (prod_mem_vonNeumann (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le) ha
        (sUnion_mem_vonNeumann (image_mem_vonNeumann hκ ha hb))))

theorem sigma_mem_vonNeumann (hκ : κ.IsInaccessible)
    (ha : a ∈ V_ κ.ord) (hb : ∀ x ∈ a, app b x ∈ V_ κ.ord) : σ a b ∈ V_ κ.ord :=
  mem_vonNeumann_of_subset sep_subset
    (prod_mem_vonNeumann (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le) ha
      (sUnion_mem_vonNeumann (image_mem_vonNeumann hκ ha hb)))

end ZFSet
