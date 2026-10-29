/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Aczel
public import Metalean.SetTheory.ZFC.Coding

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

def Aczel.appTuple (f values : ZFSet) : Nat → ZFSet
  | 0 => f
  | k + 1 => app (appTuple f (fst values) k) (snd values)

theorem Aczel.appTuple_encode (fn : ZFSet) (γ : Fin k → ZFSet) :
    appTuple fn (encode γ) k = apps fn γ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [appTuple, show encode γ = pair (encode (Fin.init γ)) (γ (Fin.last k)) from rfl,
      fst_pair, snd_pair, ih, ← apps_snoc, Fin.snoc_init_self]

end ZFSet
