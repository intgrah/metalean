/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Data.W.Cardinal

public section

universe u

namespace Cardinal

theorem IsInaccessible.wType_lt {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {α : Type u} {β : α → Type u} (hα : Cardinal.mk α < κ) (hβ : ∀ a, Cardinal.mk (β a) < κ) :
    Cardinal.mk (WType β) < κ := by
  let μ := max ℵ₀ (max (Cardinal.mk α) (sum fun a => Cardinal.mk (β a)))
  have hμ : μ < κ := max_lt hκ.aleph0_lt
    (max_lt hα (sum_lt_of_isRegular hκ.isRegular hα hβ))
  have hω : ℵ₀ ≤ μ := le_max_left _ _
  have hαμ : Cardinal.mk α ≤ μ := (le_max_left _ _).trans (le_max_right _ _)
  have hβμ (a) : Cardinal.mk (β a) ≤ μ :=
    (le_sum (fun a => Cardinal.mk (β a)) a).trans ((le_max_right _ _).trans (le_max_right _ _))
  apply lt_of_le_of_lt (WType.cardinalMk_le_of_le (κ := (2 : Cardinal) ^ μ) ?_)
    (hκ.isStrongLimit.isStrongPrelimit hμ)
  calc
    (sum fun a => ((2 : Cardinal) ^ μ) ^ Cardinal.mk (β a)) ≤ sum fun _ : α => (2 : Cardinal) ^ μ :=
      sum_le_sum _ _ fun a => by
        calc
          ((2 : Cardinal) ^ μ) ^ Cardinal.mk (β a) ≤ ((2 : Cardinal) ^ μ) ^ μ :=
            power_le_power_left (power_ne_zero μ (by simp)) (hβμ a)
          _ = (2 : Cardinal) ^ μ := by rw [← power_mul, mul_eq_self hω]
    _ = Cardinal.mk α * (2 : Cardinal) ^ μ := sum_const' _ _
    _ ≤ (2 : Cardinal) ^ μ := mul_le_of_le (hω.trans (cantor μ).le)
      (hαμ.trans (cantor μ).le) le_rfl

axiom exists_inaccessibles :
  ∃ κ : Nat → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

noncomputable def inaccessible : Nat → Cardinal.{u} :=
  exists_inaccessibles.choose

theorem inaccessible_strictMono : StrictMono inaccessible :=
  exists_inaccessibles.choose_spec.1

theorem inaccessible_isInaccessible (n : Nat) :
    (inaccessible n).IsInaccessible :=
  exists_inaccessibles.choose_spec.2 n

variable {n : Nat}

theorem ord_inaccessible_isSuccLimit :
    Order.IsSuccLimit (inaccessible n).ord :=
  isSuccLimit_ord (inaccessible_isInaccessible n).aleph0_lt.le

end Cardinal
