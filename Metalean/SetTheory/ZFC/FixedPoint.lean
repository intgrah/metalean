/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.SetTheory.ZFC.Basic

public section

namespace ZFSet

@[expose] def lfp (b : ZFSet) (Φ : ZFSet → ZFSet) : ZFSet :=
  b.sep fun z => ∀ x ∈ powerset b, Φ x ⊆ x → z ∈ x

variable {b : ZFSet} {Φ : ZFSet → ZFSet}

theorem lfp_subset : lfp b Φ ⊆ b := by
  intro z hz
  rw [lfp, mem_sep] at hz
  exact hz.1

theorem lfp_least {x : ZFSet} (hxb : x ⊆ b) (hcl : Φ x ⊆ x) : lfp b Φ ⊆ x := by
  intro z hz
  rw [lfp, mem_sep] at hz
  exact hz.2 x (mem_powerset.mpr hxb) hcl

theorem lfp_closed (hmaps : Set.MapsTo Φ (Set.Iic b) (Set.Iic b))
    (hmono : MonotoneOn Φ (Set.Iic b)) : Φ (lfp b Φ) ⊆ lfp b Φ := by
  intro y hy
  rw [lfp, mem_sep]
  refine ⟨hmaps lfp_subset hy, fun x hx hcl => ?_⟩
  have hxb := mem_powerset.mp hx
  exact hcl (hmono lfp_subset hxb (lfp_least hxb hcl) hy)

theorem lfp_unfold (hmaps : Set.MapsTo Φ (Set.Iic b) (Set.Iic b))
    (hmono : MonotoneOn Φ (Set.Iic b)) : lfp b Φ ⊆ Φ (lfp b Φ) :=
  lfp_least (hmaps lfp_subset)
    (hmono (hmaps lfp_subset) lfp_subset (lfp_closed hmaps hmono))

theorem lfp_fixed (hmaps : Set.MapsTo Φ (Set.Iic b) (Set.Iic b))
    (hmono : MonotoneOn Φ (Set.Iic b)) : Φ (lfp b Φ) = lfp b Φ :=
  subset_antisymm (lfp_closed hmaps hmono) (lfp_unfold hmaps hmono)

end ZFSet
