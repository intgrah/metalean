/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Order.FixedPoints
public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.SetTheory.ZFC.Basic

public section

namespace ZFSet

def subsetOrderIso (b : ZFSet) : Set.Iic b ≃o Set.Iic (b : Set ZFSet) where
  toEquiv := (Equiv.subtypeEquivRight fun _ => mem_powerset.symm).trans (powersetEquiv b)
  map_rel_iff' := Iff.rfl

noncomputable instance (b : ZFSet) : CompleteLattice (Set.Iic b) :=
  let e := subsetOrderIso b
  letI : InfSet (Set.Iic b) := ⟨fun s => e.symm (sInf (e '' s))⟩
  completeLatticeOfInf _ fun s => by
    constructor
    · intro x hx
      change e.symm (sInf (e '' s)) ≤ x
      exact e.symm_apply_le.mpr (sInf_le (Set.mem_image_of_mem e hx))
    · intro x hx
      change x ≤ e.symm (sInf (e '' s))
      apply e.le_symm_apply.mpr
      exact le_sInf fun y ⟨z, hz, heq⟩ => heq ▸ e.monotone (hx hz)

@[expose] noncomputable def lfp (b : ZFSet) (Φ : ZFSet → ZFSet) : ZFSet :=
  (sInf {x : Set.Iic b | Φ x ⊆ x}).1

variable {b : ZFSet} {Φ : ZFSet → ZFSet}

theorem lfp_subset : lfp b Φ ⊆ b := (sInf {x : Set.Iic b | Φ x ⊆ x}).2

theorem lfp_least {x : ZFSet} (hxb : x ⊆ b) (hcl : Φ x ⊆ x) : lfp b Φ ⊆ x :=
  sInf_le (a := (⟨x, hxb⟩ : Set.Iic b)) hcl

theorem mem_lfp {z : ZFSet} :
    z ∈ lfp b Φ ↔ z ∈ b ∧ ∀ x ∈ powerset b, Φ x ⊆ x → z ∈ x := by
  refine ⟨fun h => ⟨lfp_subset h, fun x hx hcl => lfp_least (mem_powerset.mp hx) hcl h⟩,
    fun ⟨hz, h⟩ => ?_⟩
  have hs : ({z} : ZFSet) ⊆ b := fun x hx => mem_singleton.mp hx ▸ hz
  have : (⟨{z}, hs⟩ : Set.Iic b) ≤ sInf {x : Set.Iic b | Φ x ⊆ x} :=
    le_sInf fun x hx y hy => mem_singleton.mp hy ▸ h x (mem_powerset.mpr x.2) hx
  exact this (mem_singleton.mpr rfl)

theorem lfp_fixed (hmaps : Set.MapsTo Φ (Set.Iic b) (Set.Iic b))
    (hmono : MonotoneOn Φ (Set.Iic b)) : Φ (lfp b Φ) = lfp b Φ := by
  let f : Set.Iic b →o Set.Iic b :=
    ⟨fun x => ⟨Φ x, hmaps x.2⟩, fun x y h => hmono x.2 y.2 h⟩
  exact congrArg Subtype.val f.map_lfp

theorem lfp_closed (hmaps : Set.MapsTo Φ (Set.Iic b) (Set.Iic b))
    (hmono : MonotoneOn Φ (Set.Iic b)) : Φ (lfp b Φ) ⊆ lfp b Φ :=
  (lfp_fixed hmaps hmono).le

theorem lfp_unfold (hmaps : Set.MapsTo Φ (Set.Iic b) (Set.Iic b))
    (hmono : MonotoneOn Φ (Set.Iic b)) : lfp b Φ ⊆ Φ (lfp b Φ) :=
  (lfp_fixed hmaps hmono).ge

end ZFSet
