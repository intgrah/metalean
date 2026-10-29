/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.VonNeumann
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

@[zfBounds →] theorem type_mono (h : m ≤ n) : U_ m ⊆ U_ n :=
  vonNeumann_subset_of_le (Cardinal.ord_le_ord.mpr (Cardinal.inaccessible_strictMono.monotone h))

@[zfBounds ←] theorem empty_mem_type : ∅ ∈ U_ n := by
  rw [type, mem_vonNeumann, rank_empty]
  exact Cardinal.ord_inaccessible_isSuccLimit.bot_lt

theorem omega_mem_type : omega ∈ U_ n :=
  omega_mem_vonNeumann (by
    simpa using Cardinal.ord_lt_ord.mpr (Cardinal.inaccessible_isInaccessible n).aleph0_lt)

@[zfBounds ←] theorem singleton_mem_type (hx : x ∈ U_ n) : {x} ∈ U_ n :=
  singleton_mem_vonNeumann Cardinal.ord_inaccessible_isSuccLimit hx

@[zfBounds ←] theorem powerset_mem_type (hx : x ∈ U_ n) : powerset x ∈ U_ n :=
  powerset_mem_vonNeumann Cardinal.ord_inaccessible_isSuccLimit hx

@[zfBounds ←] theorem pairing_mem_type (hx : x ∈ U_ n) (hy : y ∈ U_ n) : {x, y} ∈ U_ n :=
  pairing_mem_vonNeumann Cardinal.ord_inaccessible_isSuccLimit hx hy

@[zfBounds ←] theorem pair_mem_type (hx : x ∈ U_ n) (hy : y ∈ U_ n) : pair x y ∈ U_ n :=
  pair_mem_vonNeumann Cardinal.ord_inaccessible_isSuccLimit hx hy

@[zfBounds ←] theorem union_mem_type (hx : x ∈ U_ n) (hy : y ∈ U_ n) : x ∪ y ∈ U_ n :=
  union_mem_vonNeumann hx hy

theorem sUnion_mem_type (hx : x ∈ U_ n) : ⋃₀ x ∈ U_ n := sUnion_mem_vonNeumann hx

theorem mem_type_of_subset (hy : y ∈ U_ n) (hxy : x ⊆ y) : x ∈ U_ n :=
  mem_vonNeumann_of_subset hxy hy

@[zfBounds ←] theorem sep_mem_type {p : ZFSet → Prop} (hx : x ∈ U_ n) : x.sep p ∈ U_ n :=
  mem_type_of_subset hx sep_subset

@[zfBounds ←] theorem image_mem_type {f : ZFSet → ZFSet}
    (hx : x ∈ U_ n) (hf : ∀ y ∈ x, f y ∈ U_ n) : image f x ∈ U_ n :=
  image_mem_vonNeumann (Cardinal.inaccessible_isInaccessible n) hx hf

theorem range_mem_type {ι : Type*} [Small.{u} ι] {f : ι → ZFSet.{u}}
    (hι : Cardinal.mk (Shrink.{u} ι) < Cardinal.inaccessible n)
    (hf : ∀ i, f i ∈ U_ n) : range f ∈ U_ n := by
  rw [type, mem_vonNeumann, rank_range, ← (equivShrink ι).symm.iSup_comp]
  apply Ordinal.iSup_lt_of_lt_cof
  · rwa [(Cardinal.inaccessible_isInaccessible n).isRegular.cof_ord]
  · intro i
    exact Cardinal.ord_inaccessible_isSuccLimit.succ_lt (mem_vonNeumann.mp (hf _))

theorem prod_mem_type (hx : x ∈ U_ n) (hy : y ∈ U_ n) : prod x y ∈ U_ n :=
  prod_mem_vonNeumann Cardinal.ord_inaccessible_isSuccLimit hx hy

theorem fst_mem_type {p : ZFSet} (hp : p ∈ U_ n) : fst p ∈ U_ n :=
  fst_mem_vonNeumann Cardinal.ord_inaccessible_isSuccLimit.bot_lt hp

theorem snd_mem_type {p : ZFSet} (hp : p ∈ U_ n) : snd p ∈ U_ n :=
  snd_mem_vonNeumann Cardinal.ord_inaccessible_isSuccLimit.bot_lt hp

theorem pi_mem_type (ha : a ∈ U_ n)
    (hb : ∀ x ∈ a, app b x ∈ U_ n) : pi a b ∈ U_ n :=
  pi_mem_vonNeumann (Cardinal.inaccessible_isInaccessible n) ha hb

@[zfBounds ←] theorem sigma_mem_type (ha : a ∈ U_ n)
    (hb : ∀ x ∈ a, app b x ∈ U_ n) : σ a b ∈ U_ n :=
  sigma_mem_vonNeumann (Cardinal.inaccessible_isInaccessible n) ha hb

end ZFSet
