/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.SetTheory.Cardinal.Regular

public section

universe u

namespace Cardinal

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
