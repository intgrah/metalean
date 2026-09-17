/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.ZFC.VonNeumann
public import Metalean.SetTheory.Cardinal.Inaccessible
public import Metalean.SetTheory.ZFC.Function
import Metalean.Grind

public section

universe u

namespace ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

/-- Denotation of `Type u` -/
@[expose] noncomputable def type (n : Nat) : ZFSet.{u} :=
  V_ (Cardinal.inaccessible n).ord

@[inherit_doc] scoped notation "U_ " => type

variable {n m : Nat} {a b x y : ZFSet.{u}}

@[zfBounds →] theorem mem_type_of_mem (hx : x ∈ U_ n) (hy : y ∈ x) : y ∈ U_ n :=
  isTransitive_vonNeumann _ x hx hy

theorem type_mem_succ : U_ n ∈ U_ (n + 1) :=
  vonNeumann_mem_of_lt <|
    Cardinal.ord_lt_ord.mpr
      (Cardinal.inaccessible_strictMono (Nat.lt_succ_self n))

theorem type_subset_succ (n : Nat) : U_ n ⊆ U_ (n + 1) :=
  fun _ => mem_type_of_mem type_mem_succ

theorem type_subset_add (m k : Nat) : U_ m ⊆ U_ (m + k) := by
  induction k with
  | zero => rfl
  | succ k ih => exact subset_trans ih (type_subset_succ _)

@[zfBounds →] theorem type_mono (h : m ≤ n) : U_ m ⊆ U_ n :=
  Nat.add_sub_cancel' h ▸ type_subset_add m (n - m)

@[zfBounds ←] theorem empty_mem_type : ∅ ∈ U_ n := by
  rw [type, mem_vonNeumann, rank_empty]
  exact Cardinal.ord_inaccessible_isSuccLimit.bot_lt

theorem omega_mem_type : omega ∈ U_ n := by
  rw [type, mem_vonNeumann, omega, rank_mk]
  apply Ordinal.iSup_lt_of_lt_cof
  · simpa [(Cardinal.inaccessible_isInaccessible n).isRegular.cof_ord] using (Cardinal.inaccessible_isInaccessible n).aleph0_lt
  · intro i
    have hrank : ∀ k : Nat,
        Order.succ (PSet.ofNat k).rank <
          (Cardinal.inaccessible n).ord := by
      intro k
      induction k with
      | zero =>
        simpa [PSet.ofNat] using
          Cardinal.ord_inaccessible_isSuccLimit.succ_lt
            Cardinal.ord_inaccessible_isSuccLimit.bot_lt
      | succ k ih =>
        rw [PSet.ofNat, PSet.rank_insert]
        exact Cardinal.ord_inaccessible_isSuccLimit.succ_lt
          (max_lt ih ((Order.lt_succ _).trans ih))
    exact hrank i.down

theorem succ_rank_lt_type (hx : x ∈ U_ n) :
    Order.succ x.rank < (Cardinal.inaccessible n).ord :=
  Cardinal.ord_inaccessible_isSuccLimit.succ_lt (mem_vonNeumann.mp hx)

@[zfBounds ←] theorem singleton_mem_type (hx : x ∈ U_ n) : {x} ∈ U_ n := by
  rw [type, mem_vonNeumann, rank_singleton]
  exact succ_rank_lt_type hx

@[zfBounds ←] theorem powerset_mem_type (hx : x ∈ U_ n) : powerset x ∈ U_ n := by
  rw [type, mem_vonNeumann, rank_powerset]
  exact succ_rank_lt_type hx

@[zfBounds ←] theorem pairing_mem_type (hx : x ∈ U_ n) (hy : y ∈ U_ n) :
    {x, y} ∈ U_ n := by
  rw [type, mem_vonNeumann, rank_pair]
  exact max_lt (succ_rank_lt_type hx) (succ_rank_lt_type hy)

@[zfBounds ←] theorem pair_mem_type (hx : x ∈ U_ n) (hy : y ∈ U_ n) :
    pair x y ∈ U_ n :=
  pairing_mem_type (singleton_mem_type hx) (pairing_mem_type hx hy)

@[zfBounds ←] theorem union_mem_type (hx : x ∈ U_ n) (hy : y ∈ U_ n) :
    x ∪ y ∈ U_ n := by
  rw [type, mem_vonNeumann, rank_union]
  exact max_lt (mem_vonNeumann.mp hx) (mem_vonNeumann.mp hy)

theorem sUnion_mem_type (hx : x ∈ U_ n) : ⋃₀ x ∈ U_ n := by
  rw [type, mem_vonNeumann]
  exact (rank_sUnion_le x).trans_lt (mem_vonNeumann.mp hx)

theorem mem_type_of_subset (hy : y ∈ U_ n) (hxy : x ⊆ y) : x ∈ U_ n :=
  mem_type_of_mem (powerset_mem_type hy) (mem_powerset.mpr hxy)

@[zfBounds ←] theorem sep_mem_type {p : ZFSet → Prop} (hx : x ∈ U_ n) :
    x.sep p ∈ U_ n :=
  mem_type_of_subset hx fun _ hz => (mem_sep.mp hz).1

theorem card_lt_inaccessible (hx : x ∈ U_ n) :
    card x < Cardinal.inaccessible n :=
  (card_mono (subset_vonNeumann_self x)).trans_lt <| by
    rw [card_vonNeumann]
    exact Cardinal.preBeth_lt_inaccessible (mem_vonNeumann.mp hx)

@[zfBounds ←] theorem image_mem_type {f : ZFSet → ZFSet} [Definable₁ f]
    (hx : x ∈ U_ n) (hf : ∀ y ∈ x, f y ∈ U_ n) :
    image f x ∈ U_ n := by
  let g : Shrink x → ZFSet := fun i => f ((equivShrink x).symm i).1
  have himage : image f x = range g := by
    ext y
    rw [mem_image, mem_range]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨equivShrink x ⟨z, hz⟩, by simp [g]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨((equivShrink x).symm i).1, ((equivShrink x).symm i).2, rfl⟩
  rw [type, mem_vonNeumann, himage, rank_range]
  apply Ordinal.iSup_lt_of_lt_cof
  · rw [(Cardinal.inaccessible_isInaccessible n).isRegular.cof_ord]
    exact card_lt_inaccessible hx
  · intro i
    exact succ_rank_lt_type (hf _ ((equivShrink x).symm i).2)

theorem range_mem_type {k : Nat} {f : Fin k → ZFSet.{u}} (hf : ∀ i, f i ∈ U_ n) :
    range f ∈ U_ n := by
  induction k with
  | zero =>
    exact mem_type_of_subset empty_mem_type fun _ hx =>
      have ⟨i, _⟩ := mem_range.mp hx
      i.elim0
  | succ k ih =>
    refine mem_type_of_subset
      (union_mem_type (singleton_mem_type (hf 0)) (ih fun i => hf i.succ)) fun x hx => ?_
    have ⟨i, hi⟩ := mem_range.mp hx
    cases i using Fin.cases with
    | zero => exact mem_union.mpr (.inl (mem_singleton.mpr hi.symm))
    | succ i => exact mem_union.mpr (.inr (mem_range.mpr ⟨i, hi⟩))

theorem prod_mem_type (hx : x ∈ U_ n) (hy : y ∈ U_ n) : prod x y ∈ U_ n := by
  rw [prod, pairSep]
  exact sep_mem_type (powerset_mem_type
    (powerset_mem_type (union_mem_type hx hy)))

theorem fst_mem_type {p : ZFSet} (hp : p ∈ U_ n) : fst p ∈ U_ n := by
  by_cases h : ∃ x y, p = pair x y
  · obtain ⟨x, y, rfl⟩ := h
    have hs : {x} ∈ U_ n := mem_type_of_mem hp (by simp [pair])
    exact mem_type_of_mem hs (by simp)
  · rw [fst, dite_eq_right h]
    exact empty_mem_type

theorem snd_mem_type {p : ZFSet} (hp : p ∈ U_ n) : snd p ∈ U_ n := by
  by_cases h : ∃ x y, p = pair x y
  · obtain ⟨x, y, rfl⟩ := h
    have hs : {x, y} ∈ U_ n := mem_type_of_mem hp (by simp [pair])
    exact mem_type_of_mem hs (by simp)
  · rw [snd, dite_eq_right h]
    exact empty_mem_type

theorem pi_mem_type (ha : a ∈ U_ n)
    (hb : ∀ x ∈ a, app b x ∈ U_ n) : pi a b ∈ U_ n :=
  sep_mem_type
    (powerset_mem_type (prod_mem_type ha
      (sUnion_mem_type (image_mem_type ha hb))))

@[zfBounds ←] theorem sigma_mem_type (ha : a ∈ U_ n)
    (hb : ∀ x ∈ a, app b x ∈ U_ n) : σ a b ∈ U_ n :=
  sep_mem_type (prod_mem_type ha (sUnion_mem_type (image_mem_type ha hb)))

end ZFSet
