/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Env
public import Metalean.Meta.ZF
public import Metalean.SetTheory.ZFC.Aczel.Spine
public import Metalean.SetTheory.ZFC.Universe.Sort
public import Metalean.Syntax.Substitution
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean

open CategoryTheory ZFSet

universe u

attribute [local instance 2000] Classical.allZFSetDefinable

@[derive_functor ζ, derive_functor ℓ instL levelFunctor via Level.category]
inductive Atom (ζ : Sigs) (ℓ : Nat) : Type (u + 1) where
  | const {kind : ConstKind} {nlevels : Nat}
    (η : Head ζ (.const kind nlevels)) (ls : Fin nlevels → Level ℓ)
  | ind {ι : IndSig} (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (vps : Fin ι.nparams → ZFSet.{u})
    (vis : Fin (ι.nindices s) → ZFSet.{u})
  | ctor {ι : IndSig} (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (ls : Fin ι.nlevels → Level ℓ)
    (vps : Fin ι.nparams → ZFSet.{u})
    (vfds : Fin (ι.ctors s c).nfields → ZFSet.{u})
    (vrecFds : Fin (ι.ctors s c).nrecFields → ZFSet.{u})
  | recr {ι : IndSig} (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (l : Level ℓ)
    (vps : Fin ι.nparams → ZFSet.{u})
    (vms : Fin ι.nsorts → ZFSet.{u})
    (vmins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → ZFSet.{u})
    (vis : Fin (ι.nindices s) → ZFSet.{u}) (vmaj : ZFSet.{u})
  | quot (η : Head ζ .quot) (l : Level ℓ) (αv rv : ZFSet.{u})
  | quotMk (η : Head ζ .quot) (l : Level ℓ) (αv rv av : ZFSet.{u})
  | quotLift (η : Head ζ .quot) (l₁ l₂ : Level ℓ)
    (αv rv βv fv hv av : ZFSet.{u})
  | quotInd (η : Head ζ .quot) (l : Level ℓ)
    (αv rv βv fv av : ZFSet.{u})

variable {ζ ζ₁ ζ₂ ζ₃ : Sigs} {ℓ ℓ' : Nat} {ε : Atom ζ ℓ → ZFSet} {ν : Param ℓ → Nat}

instance : InstLevel (Param ℓ → Level ℓ') (Atom ζ ℓ) (Atom ζ ℓ') where
  inst ls a := a.instL ls

namespace Atom

def unstep (sig : Sig) : Atom (.snoc ζ sig) ℓ → Option (Atom ζ ℓ)
  | .const η ls => η.unstep.map fun η => .const η ls
  | .ind η s ls vps vis => η.unstep.map fun η => .ind η s ls vps vis
  | .ctor η s c ls vps vfds vrecFds => η.unstep.map fun η => .ctor η s c ls vps vfds vrecFds
  | .recr η s ls u vps vms vmins vis vmaj =>
    η.unstep.map fun η => .recr η s ls u vps vms vmins vis vmaj
  | .quot η l αv rv => η.unstep.map fun η => .quot η l αv rv
  | .quotMk η l αv rv av => η.unstep.map fun η => .quotMk η l αv rv av
  | .quotLift η l₁ l₂ αv rv βv fv hv av =>
    η.unstep.map fun η => .quotLift η l₁ l₂ αv rv βv fv hv av
  | .quotInd η l αv rv βv fv av => η.unstep.map fun η => .quotInd η l αv rv βv fv av

@[simp] theorem unstep_map_step (sig : Sig) (a : Atom ζ ℓ) :
    (a.map (.step .refl : ζ ⟶ ζ.snoc sig)).unstep sig = some a := by
  cases a <;> rfl

end Atom

def AtomsMap (pre : ζ₁ ⟶ ζ₂) (ε₁ : Atom ζ₁ ℓ → ZFSet) (ε₂ : Atom ζ₂ ℓ → ZFSet) : Prop :=
  ε₂ ∘ Atom.map pre = ε₁

theorem AtomsMap.trans {pre₁ : ζ₁ ⟶ ζ₂} {pre₂ : ζ₂ ⟶ ζ₃}
    {ε₁ : Atom ζ₁ ℓ → ZFSet} {ε₂ : Atom ζ₂ ℓ → ZFSet} {ε₃ : Atom ζ₃ ℓ → ZFSet} :
    AtomsMap pre₁ ε₁ ε₂ →
    AtomsMap pre₂ ε₂ ε₃ →
    AtomsMap (pre₁ ≫ pre₂) ε₁ ε₃ := by
  intro h₁ h₂
  funext a
  calc
    _ = _ := congrArg ε₃ <| (Atom.functor ℓ).map_comp_apply pre₁ pre₂ a
    _ = _ := congrFun h₂ _
    _ = _ := congrFun h₁ a

namespace Expr

set_option hygiene false in
notation:max ε:max "[" ν "; " γ "]⟦" e "⟧" => Expr.denote ε ν γ e

noncomputable def denote {n : Nat} (ε : Atom ζ ℓ → ZFSet) (ν : Param ℓ → Nat)
    (γ : Fin n → ZFSet) : Expr ζ ℓ n → ZFSet
  | .var v =>
    γ v
  | .sort l =>
    S_ (l.eval ν)
  | .const η ls =>
    ε <| .const η ls
  | .ind η s ls ps is =>
    ε <| .ind η s ls (ε[ν; γ]⟦ps ·⟧) (ε[ν; γ]⟦is ·⟧)
  | .ctor η s c ls ps fds recFds =>
    ε <| .ctor η s c ls (ε[ν; γ]⟦ps ·⟧) (ε[ν; γ]⟦fds ·⟧) (ε[ν; γ]⟦recFds ·⟧)
  | .recr η s ls l ps ms mins is maj =>
    ε <| .recr η s ls l (ε[ν; γ]⟦ps ·⟧) (ε[ν; γ]⟦ms ·⟧) (ε[ν; γ]⟦mins · ·⟧) (ε[ν; γ]⟦is ·⟧) ε[ν; γ]⟦maj⟧
  | .quot η l α r =>
    ε <| .quot η l ε[ν; γ]⟦α⟧ ε[ν; γ]⟦r⟧
  | .quotMk η l α r a =>
    ε <| .quotMk η l ε[ν; γ]⟦α⟧ ε[ν; γ]⟦r⟧ ε[ν; γ]⟦a⟧
  | .quotLift η l₁ l₂ α r β f h a =>
    ε <| .quotLift η l₁ l₂ ε[ν; γ]⟦α⟧ ε[ν; γ]⟦r⟧ ε[ν; γ]⟦β⟧ ε[ν; γ]⟦f⟧ ε[ν; γ]⟦h⟧ ε[ν; γ]⟦a⟧
  | .quotInd η l α r β f a =>
    ε <| .quotInd η l ε[ν; γ]⟦α⟧ ε[ν; γ]⟦r⟧ ε[ν; γ]⟦β⟧ ε[ν; γ]⟦f⟧ ε[ν; γ]⟦a⟧
  | .app f a =>
    Aczel.app ε[ν; γ]⟦f⟧ ε[ν; γ]⟦a⟧
  | .lam t body =>
    Aczel.lam ε[ν; γ]⟦t⟧ fun x => ε[ν; Fin.snoc γ x]⟦body⟧
  | .forallE t body =>
    Aczel.pi ε[ν; γ]⟦t⟧ fun x => ε[ν; Fin.snoc γ x]⟦body⟧
  | .letE _ value body =>
    ε[ν; Fin.snoc γ ε[ν; γ]⟦value⟧]⟦body⟧

@[app_unexpander denote]
meta def denote_unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $ε $ν $γ $e) => `($ε[$ν; $γ]⟦$e⟧)
  | _ => throw ()

notation:max ε:max "[" γ "]⟦" e "⟧" => denote ε ![] γ e

@[simp] theorem denote_map {ε₁ : Atom ζ₁ ℓ → ZFSet} {ε₂ : Atom ζ₂ ℓ → ZFSet}
    (pre : ζ₁ ⟶ ζ₂) (hatoms : AtomsMap pre ε₁ ε₂)
    {n : Nat} (γ : Fin n → ZFSet) (e : Expr ζ₁ ℓ n) :
    ε₂[ν; γ]⟦e.map pre⟧ = ε₁[ν; γ]⟦e⟧ := by
  subst hatoms
  induction e <;> simp! [*]

@[simp] theorem denote_instL {ℓ' n : Nat} (ε : Atom ζ ℓ' → ZFSet)
    (ν : Param ℓ' → Nat) (ls : Param ℓ → Level ℓ') (γ : Fin n → ZFSet) (e : Expr ζ ℓ n) :
    ε[ν; γ]⟦e{ls}⟧ =
      (fun a : Atom ζ ℓ => ε a{ls})[Level.eval ν ∘ ls; γ]⟦e⟧ := by
  induction e <;> simp! [Level.eval_inst, *] <;> rfl

private theorem denote_snoc_lift {m n : Nat} (γ : Fin n → ZFSet) (ρ : Ren m n) (x : ZFSet) :
    Fin.snoc γ x ∘ ρ.lift = Fin.snoc (γ ∘ ρ) x := by
  funext v
  cases v using Fin.lastCases <;> simp

@[simp] theorem denote_rename {m n : Nat} (γ : Fin n → ZFSet) (ρ : Ren m n) (e : Expr ζ ℓ m) :
    ε[ν; γ]⟦e.rename ρ⟧ = ε[ν; γ ∘ ρ]⟦e⟧ := by
  induction e generalizing n <;> simp! [denote_snoc_lift, *]

@[simp] theorem denote_wkFrom {n : Nat} (γ : Fin (n + 1) → ZFSet) (cut : Nat) (e : Expr ζ ℓ n) :
    ε[ν; γ]⟦e.wkFrom cut⟧ = ε[ν; fun v => γ (Ren.wkFrom cut v)]⟦e⟧ :=
  e.denote_rename γ (Ren.wkFrom cut)

@[simp] theorem denote_wk {n : Nat} (γ : Fin n → ZFSet) (x : ZFSet) (e : Expr ζ ℓ n) :
    ε[ν; Fin.snoc γ x]⟦e.wk⟧ = ε[ν; γ]⟦e⟧ := by
  rw [wk, denote_wkFrom]
  congr 1
  funext v
  simp

@[simp] theorem denote_wkN {n k : Nat} (γ : Fin (n + k) → ZFSet) (e : Expr ζ ℓ n) :
    ε[ν; γ]⟦e.wkN k⟧ = ε[ν; fun v => γ (v.castAdd k)]⟦e⟧ := by
  simp [wkN_eq_rename, Ren.wkN, Function.comp_def]

@[simp] theorem denote_wkClosed {n : Nat} (γ : Fin n → ZFSet) (e : Expr ζ ℓ 0) :
    ε[ν; γ]⟦e.wkClosed⟧ = ε[ν; ![]]⟦e⟧ := by
  induction n with
  | zero => simp [wkClosed, Subsingleton.elim γ ![]]
  | succ n ih =>
    rw [wkClosed, ← Fin.snoc_init_self γ, denote_wk]
    exact ih _

theorem denote_substLiftN {m n k : Nat} (γ : Fin (n + k) → ZFSet)
    (σ : Subst ζ ℓ m n) :
    (ε[ν; γ]⟦σ.liftN k ·⟧) =
      Fin.append (ε[ν; fun v => γ (v.castAdd k)]⟦σ ·⟧)
        fun v => γ (Fin.natAdd n v) := by
  funext v
  cases v using Fin.addCases <;> simp!

private theorem denote_substLift {m n : Nat} (γ : Fin n → ZFSet) (σ : Subst ζ ℓ m n) (x : ZFSet) :
    (ε[ν; Fin.snoc γ x]⟦σ.lift ·⟧) = Fin.snoc (ε[ν; γ]⟦σ ·⟧) x := by
  funext v
  cases v using Fin.lastCases <;> simp!

@[simp] theorem denote_subst {m n : Nat} (γ : Fin n → ZFSet) (σ : Subst ζ ℓ m n)
    (e : Expr ζ ℓ m) :
    ε[ν; γ]⟦e.subst σ⟧ = ε[ν; (ε[ν; γ]⟦σ ·⟧)]⟦e⟧ := by
  induction e generalizing n <;> simp! [denote_substLift, *]

@[simp] theorem denote_inst {n : Nat} (γ : Fin n → ZFSet) (e : Expr ζ ℓ n)
    (e' : Expr ζ ℓ (n + 1)) :
    ε[ν; γ]⟦e'.inst e⟧ = ε[ν; Fin.snoc γ ε[ν; γ]⟦e⟧]⟦e'⟧ := by
  rw [inst, denote_subst]
  congr 1
  funext v
  cases v using Fin.lastCases <;> simp! [Subst.id]

@[simp] theorem denote_apps {k n : Nat} (γ : Fin n → ZFSet) (e : Expr ζ ℓ n)
    (args : Fin k → Expr ζ ℓ n) :
    ε[ν; γ]⟦e.apps args⟧ = Aczel.apps ε[ν; γ]⟦e⟧
      (ε[ν; γ]⟦args ·⟧) := by
  induction args using Fin.snocInduction generalizing e with
  | elim0 => simp [Aczel.apps]
  | snoc args arg ih =>
    have h := Fin.comp_snoc (denote ε ν γ) args arg
    simp only [Function.comp_def] at h
    simp! [apps_last, ih, h]

@[simp] theorem denote_applyBound {k n : Nat} (γ : Fin (n + k) → ZFSet) (e : Expr ζ ℓ n) :
    ε[ν; γ]⟦e.applyBound k⟧ = Aczel.apps
      ε[ν; fun v => γ (v.castAdd k)]⟦e⟧ fun v => γ (Fin.natAdd n v) := by
  simp! [applyBound_eq_apps]

end Expr

end Metalean
