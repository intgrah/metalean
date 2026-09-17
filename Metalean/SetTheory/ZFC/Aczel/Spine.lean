/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Aczel

@[expose] public noncomputable section

namespace ZFSet

universe u

variable {k m n : Nat}

def Aczel.apps (f : ZFSet) (args : Fin k → ZFSet) : ZFSet :=
  Fin.foldl k (fun f i => app f (args i)) f

theorem Aczel.apps_succ (f : ZFSet) (args : Fin (k + 1) → ZFSet) :
    apps f args = apps (app f (args 0)) fun i => args i.succ :=
  Fin.foldl_succ ..

@[simp] theorem Aczel.apps_snoc (f : ZFSet) (args : Fin k → ZFSet) (a : ZFSet) :
    apps f (Fin.snoc args a) = app (apps f args) a := by
  unfold apps
  rw [Fin.foldl_succ_last]
  simp

theorem Aczel.apps_of_zero (hk : k = 0) (f : ZFSet) (args : Fin k → ZFSet) :
    apps f args = f := by
  subst hk
  rfl

end ZFSet
