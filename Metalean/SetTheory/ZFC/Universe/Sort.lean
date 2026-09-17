/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Truth
public import Metalean.SetTheory.ZFC.Universe.Type
import Metalean.Grind

public section

universe u

namespace ZFSet

variable {n k : Nat}

theorem truth_mem_type (n : Nat) : truth ∈ U_ n :=
  powerset_mem_type (singleton_mem_type empty_mem_type)

/-- Denotation of `Sort u` -/
@[expose] noncomputable def sort : Nat → ZFSet.{u}
  | 0 => truth
  | n + 1 => U_ n

@[inherit_doc] scoped notation "S_ " => sort

theorem sort_mem_succ : ∀ n : Nat, S_ n ∈ S_ (n + 1)
  | 0 => truth_mem_type 0
  | _ + 1 => type_mem_succ

@[zfBounds →] theorem mem_type_of_mem_sort : ∀ {n k : Nat}, n ≤ k + 1 → ∀ {x : ZFSet.{u}},
    x ∈ S_ n → x ∈ U_ k
  | 0, k, _, _, hx => mem_type_of_mem (truth_mem_type k) hx
  | _ + 1, _, h, _, hx => type_mono (Nat.le_of_succ_le_succ h) hx

end ZFSet
