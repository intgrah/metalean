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

def Aczel.pis : {k : Nat} → (Fin k → ZFSet) → ((Fin k → ZFSet) → ZFSet) → ZFSet
  | 0, _, leaf => leaf ![]
  | k + 1, domains, leaf =>
    pis (Fin.init domains) fun values => pi (domains (Fin.last k)) fun value =>
      leaf (Fin.snoc values value)

theorem Aczel.pis_congr {domains : Fin k → ZFSet} {leaf₁ leaf₂ : (Fin k → ZFSet) → ZFSet}
    (h : ∀ values, (∀ i, values i ∈ domains i) → leaf₁ values = leaf₂ values) :
    pis domains leaf₁ = pis domains leaf₂ := by
  induction k with
  | zero => exact h ![] (fun i => i.elim0)
  | succ k ih =>
    apply ih
    intro values hvalues
    apply pi_congr
    intro value hvalue
    exact h (Fin.snoc values value) fun i => by
      cases i using Fin.lastCases with
      | last => simpa using hvalue
      | cast i => simpa [Fin.init] using hvalues i

theorem Aczel.apps_mem_pis {domains : Fin k → ZFSet}
    {leaf : (Fin k → ZFSet) → ZFSet} {fn : ZFSet} {values : Fin k → ZFSet}
    (hfn : fn ∈ pis domains leaf) (hvalues : ∀ i, values i ∈ domains i) :
    apps fn values ∈ leaf values := by
  induction k with
  | zero =>
    have : values = ![] := Subsingleton.elim _ _
    subst values
    exact hfn
  | succ k ih =>
    have h := app_mem (ih hfn (fun i => hvalues i.castSucc)) (hvalues (Fin.last k))
    rw [ZFSet.app_map (hvalues (Fin.last k))] at h
    change app (apps fn (Fin.init values)) (values (Fin.last k)) ∈
      leaf (Fin.snoc (Fin.init values) (values (Fin.last k))) at h
    simpa only [← apps_snoc, Fin.snoc_init_self] using h

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
