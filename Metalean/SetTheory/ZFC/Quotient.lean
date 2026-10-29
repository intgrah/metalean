/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Logic.Relation
public import Metalean.SetTheory.ZFC.Function

@[expose] public section

namespace ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {a c x y v : ZFSet} {r : ZFSet → ZFSet → Prop}

def equivClosure (a : ZFSet) (r : ZFSet → ZFSet → Prop) (x : ZFSet) : ZFSet :=
  a.sep (Relation.EqvGen (fun x y => x ∈ a ∧ y ∈ a ∧ r x y) x)

theorem equivClosure_subset : equivClosure a r x ⊆ a := sep_subset

theorem self_mem_equivClosure (hx : x ∈ a) : x ∈ equivClosure a r x :=
  mem_sep.mpr ⟨hx, .refl x⟩

theorem equivClosure_eq_of_rel (hx : x ∈ a) (hy : y ∈ a) (hr : r x y) :
    equivClosure a r x = equivClosure a r y := by
  have h : Relation.EqvGen (fun x y => x ∈ a ∧ y ∈ a ∧ r x y) x y :=
    .rel x y ⟨hx, hy, hr⟩
  ext v
  simp only [equivClosure, mem_sep]
  exact and_congr_right fun _ => ⟨fun hv => .trans _ _ _ (.symm _ _ h) hv,
    fun hv => .trans _ _ _ h hv⟩

theorem eq_of_mem_equivClosure {β : Sort*} {f : ZFSet → β}
    (hcompat : ∀ x ∈ a, ∀ y ∈ a, r x y → f x = f y)
    (hv : v ∈ equivClosure a r x) : f v = f x := by
  have he : Equivalence (fun x y : ZFSet => f x = f y) :=
    ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  exact (he.eqvGen_iff.mp
    (Relation.EqvGen.mono (fun _ _ h => hcompat _ h.1 _ h.2.1 h.2.2)
      _ _ (mem_sep.mp hv).2)).symm

noncomputable def quotient (a : ZFSet) (r : ZFSet → ZFSet → Prop) : ZFSet :=
  image (equivClosure a r) a

@[simp] theorem mem_quotient : c ∈ quotient a r ↔ ∃ x ∈ a, c = equivClosure a r x :=
  mem_image'

noncomputable def quotientLift (f : ZFSet → ZFSet) (c : ZFSet) : ZFSet :=
  ⋃₀ image f c

theorem quotientLift_equivClosure {f : ZFSet → ZFSet} (hx : x ∈ a)
    (hcompat : ∀ x ∈ a, ∀ y ∈ a, r x y → f x = f y) :
    quotientLift f (equivClosure a r x) = f x := by
  ext z
  rw [quotientLift, mem_sUnion_image]
  exact ⟨fun ⟨y, hy, hz⟩ => eq_of_mem_equivClosure hcompat hy ▸ hz,
    fun hz => ⟨x, self_mem_equivClosure hx, hz⟩⟩

end ZFSet
