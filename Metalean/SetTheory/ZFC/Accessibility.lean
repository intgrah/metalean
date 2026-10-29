/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.ZFC.Basic

@[expose] public section

namespace ZFSet

variable {α a : ZFSet} {r : ZFSet → ZFSet → Prop}

def accSet (α : ZFSet) (r : ZFSet → ZFSet → Prop) : ZFSet :=
  α.sep (Acc fun b a => b ∈ α ∧ r b a)

theorem accSet_subset : accSet α r ⊆ α := sep_subset

theorem accSet_intro (ha : a ∈ α)
    (h : ∀ b ∈ α, r b a → b ∈ accSet α r) : a ∈ accSet α r :=
  mem_sep.mpr ⟨ha, .intro a fun b hb => (mem_sep.mp (h b hb.1 hb.2)).2⟩

theorem accSet_inv (ha : a ∈ accSet α r) (b : ZFSet) (hb : b ∈ α) (hr : r b a) :
    b ∈ accSet α r :=
  mem_sep.mpr ⟨hb, (mem_sep.mp ha).2.inv ⟨hb, hr⟩⟩

end ZFSet
