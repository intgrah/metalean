/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public section

namespace List

theorem foldr_max_le_of_mem {x : Nat} {L : List Nat} (h : x ∈ L) : x ≤ L.foldr Nat.max 0 := by
  induction h with
  | head _ => exact Nat.le_max_left _ _
  | tail _ h ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem le_foldr_max_iff {x : Nat} : ∀ {L : List Nat},
    x ≤ L.foldr Nat.max 0 → x = 0 ∨ ∃ y ∈ L, x ≤ y
  | [] => fun h => Or.inl (Nat.le_zero.mp h)
  | y :: L' => fun h => by
    by_cases hxy : x ≤ y
    · exact Or.inr ⟨y, mem_cons_self, hxy⟩
    · have : x ≤ L'.foldr Nat.max 0 := by grind
      exact (le_foldr_max_iff this).imp_right fun ⟨z, hmem, hle⟩ =>
        ⟨z, mem_cons_of_mem _ hmem, hle⟩

theorem foldr_max_le_of_all {x : Nat} : ∀ {L : List Nat},
    (∀ y ∈ L, y ≤ x) → L.foldr Nat.max 0 ≤ x
  | [] => fun _ => Nat.zero_le _
  | _ :: _ => fun h => Nat.max_le.mpr
    ⟨h _ mem_cons_self,
      foldr_max_le_of_all fun _ hy => h _ (mem_cons_of_mem _ hy)⟩

theorem foldr_max_append (ys : List Nat) : ∀ xs : List Nat,
    (xs ++ ys).foldr Nat.max 0 = Nat.max (xs.foldr Nat.max 0) (ys.foldr Nat.max 0)
  | [] => rfl
  | x :: xs => by simp [foldr_max_append ys xs]

theorem foldr_max_map_succ : ∀ {L : List Nat}, L ≠ [] →
    (L.map (· + 1)).foldr Nat.max 0 = L.foldr Nat.max 0 + 1
  | [] => fun h => absurd rfl h
  | [_] => by simp
  | _ :: y :: L => fun _ => by
    have := foldr_max_map_succ (L := y :: L) (cons_ne_nil _ _)
    grind

end List
