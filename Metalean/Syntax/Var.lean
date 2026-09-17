/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Fin

@[expose] public section

namespace Metalean

abbrev Var := Fin

namespace Var

variable {n : Nat}

instance : DecidableEq (Var n) := inferInstanceAs (DecidableEq (Fin n))

def db (v : Var n) : Nat := n - 1 - v.val

def ofDb (i : Nat) (h : i < n) : Var n := ⟨n - 1 - i, by omega⟩

@[simp] theorem db_ofDb (i : Nat) (h : i < n) : (ofDb i h).db = i := by
  simp only [db, ofDb]
  omega

@[simp] theorem ofDb_db (v : Var n) (h : v.db < n) : ofDb v.db h = v := by
  apply Fin.ext
  simp only [db, ofDb]
  have := v.isLt
  omega

theorem db_lt (v : Var n) : v.db < n := by
  have := v.isLt
  simp only [db]
  omega

@[simp] theorem db_last : db (Fin.last n) = 0 := by
  simp [db]

@[simp] theorem db_castAdd (v : Var n) (m : Nat) :
    db (v.castAdd m) = v.db + m := by
  have := v.isLt
  simp only [db, Fin.val_castAdd]
  omega

@[simp] theorem db_castSucc (v : Var n) : db v.castSucc = v.db + 1 := by
  have := v.isLt
  simp only [db, Fin.val_castSucc]
  omega

@[simp] theorem db_natAdd (m : Nat) (v : Var n) :
    db (Fin.natAdd m v) = v.db := by
  have := v.isLt
  simp only [db, Fin.val_natAdd]
  omega

@[simp] theorem db_castLE {m : Nat} (v : Var n) (h : n ≤ m) :
    db (v.castLE h) = v.db + (m - n) := by
  have := v.isLt
  simp only [db, Fin.castLE]
  omega

end Var

end Metalean
