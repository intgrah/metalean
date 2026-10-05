/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Data.Fin

@[expose] public section

namespace Metalean

abbrev Var := Fin

namespace Var

variable {n : Nat}

instance : DecidableEq (Var n) := inferInstanceAs (DecidableEq (Fin n))

abbrev db (v : Var n) : Nat := n - 1 - v.val

@[simp] theorem db_last : db (Fin.last n) = 0 := by
  simp [db]

@[simp] theorem db_castAdd (v : Var n) (m : Nat) :
    db (v.castAdd m) = v.db + m := by
  simp [db]
  omega

@[simp] theorem db_castSucc (v : Var n) : db v.castSucc = v.db + 1 := by
  simp [db]
  omega

@[simp] theorem db_natAdd (m : Nat) (v : Var n) :
    db (Fin.natAdd m v) = v.db := by
  simp [db]
  omega

@[simp] theorem db_castLE {m : Nat} (v : Var n) (h : n ≤ m) :
    db (v.castLE h) = v.db + (m - n) := by
  simp [db]
  omega

end Var

end Metalean
