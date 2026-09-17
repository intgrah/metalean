/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Data.Set.Finite.Basic

public section

universe u

namespace Cardinal

noncomputable def nth (s : Set Cardinal.{u}) : Nat → Cardinal.{u}
  | 0 => sInf s
  | n + 1 => sInf (s ∩ Set.Ioi (nth s n))

variable {s : Set Cardinal.{u}} {c : Cardinal.{u}}

private theorem inter_Ioi_nonempty (hs : s.Infinite) (h : (s ∩ Set.Iic c).Finite) :
    (s ∩ Set.Ioi c).Nonempty :=
  not_not.mp fun hne => hs (h.subset fun x hx =>
    ⟨hx, Set.mem_Iic.mpr (not_lt.mp fun hlt => hne ⟨x, hx, Set.mem_Ioi.mpr hlt⟩)⟩)

private theorem nth_spec (hs : s.Infinite) (n : Nat) :
    nth s n ∈ s ∧ (s ∩ Set.Iic (nth s n)).Finite := by
  induction n with
  | zero =>
    exact ⟨csInf_mem hs.nonempty, (Set.finite_singleton (sInf s)).subset fun _ hx =>
      le_antisymm hx.2 (csInf_le' hx.1)⟩
  | succ n ih =>
    refine ⟨(csInf_mem (inter_Ioi_nonempty hs ih.2)).1,
      (ih.2.union (Set.finite_singleton (nth s (n + 1)))).subset fun x hx => ?_⟩
    rcases le_or_gt x (nth s n) with h | h
    · exact .inl ⟨hx.1, h⟩
    · exact .inr (le_antisymm hx.2 (csInf_le' ⟨hx.1, h⟩))

theorem nth_mem (hs : s.Infinite) (n : Nat) : nth s n ∈ s := (nth_spec hs n).1

theorem nth_strictMono (hs : s.Infinite) : StrictMono (nth s) :=
  strictMono_nat_of_lt_succ fun n =>
    (csInf_mem (inter_Ioi_nonempty hs (nth_spec hs n).2)).2

end Cardinal
