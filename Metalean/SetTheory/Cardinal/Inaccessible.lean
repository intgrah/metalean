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

theorem preBeth_lt_inaccessible {o : Ordinal}
    (ho : o < (inaccessible n).ord) :
    preBeth o < inaccessible n := by
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    rw [preBeth, show (⨆ a : Set.Iio o, 2 ^ preBeth a.1) = ⨆ a : o.ToType,
      (2 : Cardinal) ^ preBeth (Ordinal.ToType.mk.symm a).1 from Ordinal.ToType.mk.symm.iSup_comp (g := fun a : Set.Iio o => (2 : Cardinal) ^ preBeth a.1).symm]
    apply iSup_lt_of_lt_cof_ord
    · rw [(inaccessible_isInaccessible n).isRegular.cof_ord, mk_toType]
      exact lt_ord.mp ho
    · intro a
      have ⟨a, ha⟩ := Ordinal.ToType.mk.symm a
      exact (inaccessible_isInaccessible n).isStrongLimit.isStrongPrelimit
        (ih a ha (ha.trans ho))

end Cardinal
