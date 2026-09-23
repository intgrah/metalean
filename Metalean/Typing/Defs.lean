/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Env
public import Metalean.Syntax.Inductive.Iota
public import Metalean.Syntax.Quot
public import Metalean.Syntax.Structure
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean

variable {ζ : Sigs}

set_option hygiene false in
notation:65 E "[" Γ "]" " ⊢ " e₁:51 " ≡ " e₂:51 " : " t:lead => Defeq E Γ e₁ e₂ t
set_option hygiene false in
notation:65 E "[" Γ "]" " ⊢ " e:51 " : " t:lead => Defeq E Γ e e t

/-- Definitional equality with regularity -/
judgement Defeq (E : Env ζ) {ℓ : Nat} :
    {n : Nat} → Ctx ζ ℓ 0 n → Expr ζ ℓ n → Expr ζ ℓ n → Expr ζ ℓ n → Prop where

  E[Γ] ⊢ Γ.get v : .sort l
  ──────────────────── var {n} {Γ : Ctx ζ ℓ 0 n} {v : Var n} {l}
  E[Γ] ⊢ .var v : Γ.get v

  E[Γ] ⊢ e₁ ≡ e₂ : t
  ──────────────────── symm {n} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t}
  E[Γ] ⊢ e₂ ≡ e₁ : t

  E[Γ] ⊢ e₁ ≡ e₂ : t
  E[Γ] ⊢ e₂ ≡ e₃ : t
  ──────────────────── trans {n} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ e₃ t}
  E[Γ] ⊢ e₁ ≡ e₃ : t

  ──────────────────── sortDF {n} {Γ : Ctx ζ ℓ 0 n} {l}
  E[Γ] ⊢ .sort l : .sort (.succ l)

  E[Γ] ⊢ ((E.get η).constType.instL ls).wkClosed : .sort l
  ──────────────────── constDF {n nlevels kind} {Γ : Ctx ζ ℓ 0 n}
    {η : Head ζ (.const kind nlevels)} {ls l}
  E[Γ] ⊢ .const η ls : ((E.get η).constType.instL ls).wkClosed

  ∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p
  ∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i
  ──────────────────── indDF {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s ls ps₁ ps₂ is₁ is₂}
  E[Γ] ⊢ .ind η s ls ps₁ is₁ ≡ .ind η s ls ps₂ is₂ :
    .sort ((E.get η).block.level.inst ls)

  ∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p
  ∀ f, E[Γ] ⊢ fds₁ f ≡ fds₂ f :
    (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
      (Fin.append ps₁ fun previous : Fin f.val => fds₁ (previous.castLE f.isLt.le))
  ∀ f, E[Γ] ⊢ recFds₁ f ≡ recFds₂ f :
    (((E.get η).block.ctors s c).recursive f).instantiatedType
      η ls ps₁ (Fin.append ps₁ fds₁)
  ∀ f, E[Γ] ⊢ ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f ≡
    ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps₂ fds₂ f :
      .sort (fieldLevels f)
  ∀ f, E[Γ] ⊢ ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f ≡
    ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps₂ fds₂ f :
      .sort (recFieldLevels f)
  E[Γ] ⊢ .ind η s ls ps₁
      (((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁) ≡
    .ind η s ls ps₂
      (((E.get η).block.ctors s c).targetIndex ls ps₂ fds₂) :
      .sort ((E.get η).block.level.inst ls)
  ──────────────────── ctorDF {n} {Γ : Ctx ζ ℓ 0 n} {ι} {η : Head ζ (.inductive ι)}
    {s c ls ps₁ ps₂ fds₁ fds₂ recFds₁ recFds₂}
    {fieldLevels : Fin (ι.ctors s c).nfields → Level ℓ}
    {recFieldLevels : Fin (ι.ctors s c).nrecFields → Level ℓ}
  E[Γ] ⊢ .ctor η s c ls ps₁ fds₁ recFds₁ ≡ .ctor η s c ls ps₂ fds₂ recFds₂ :
    .ind η s ls ps₁ (((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁)

  (E.get η).block.RecAllowed l
  ∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p
  ∀ s, E[Γ] ⊢ ms₁ s ≡ ms₂ s : (E.get η).block.motiveType η ls ps₁ l s
  ∀ s c, E[Γ] ⊢ mins₁ s c ≡ mins₂ s c : (E.get η).block.caseFnType η ls ps₁ ms₁ s c
  ∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i
  E[Γ] ⊢ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁
  E[Γ] ⊢ Inductive.motiveResult (ms₁ s) is₁ maj₁ ≡
    Inductive.motiveResult (ms₂ s) is₂ maj₂ : .sort l
  ──────────────────── recrDF {n} {Γ : Ctx ζ ℓ 0 n} {ι} {η : Head ζ (.inductive ι)}
    {s ls l ps₁ ps₂ ms₁ ms₂ mins₁ mins₂ is₁ is₂ maj₁ maj₂}
  E[Γ] ⊢ .recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁ ≡
    .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ :
      Inductive.motiveResult (ms₁ s) is₁ maj₁

  E[Γ] ⊢ t : .sort l₁
  E[Γ.snoc t] ⊢ t' : .sort l₂
  E[Γ] ⊢ f₁ ≡ f₂ : .forallE t t'
  E[Γ] ⊢ a₁ ≡ a₂ : t
  E[Γ] ⊢ t'.inst a₁ ≡ t'.inst a₂ : .sort l₂
  ──────────────────── appDF {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ f₁ f₂ a₁ a₂ t t'}
  E[Γ] ⊢ .app f₁ a₁ ≡ .app f₂ a₂ : t'.inst a₁

  E[Γ] ⊢ t₁ ≡ t₂ : .sort l₁
  E[Γ.snoc t₁] ⊢ t' : .sort l₂
  E[Γ.snoc t₂] ⊢ t' : .sort l₂
  E[Γ.snoc t₁] ⊢ e₁' ≡ e₂' : t'
  E[Γ.snoc t₂] ⊢ e₁' ≡ e₂' : t'
  ──────────────────── lamDF {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ t₁ t₂ e₁' e₂' t'}
  E[Γ] ⊢ .lam t₁ e₁' ≡ .lam t₂ e₂' : .forallE t₁ t'

  E[Γ] ⊢ t₁ ≡ t₂ : .sort l₁
  E[Γ.snoc t₁] ⊢ t₁' ≡ t₂' : .sort l₂
  E[Γ.snoc t₂] ⊢ t₁' ≡ t₂' : .sort l₂
  ──────────────────── forallEDF {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ t₁ t₂ t₁' t₂'}
  E[Γ] ⊢ .forallE t₁ t₁' ≡ .forallE t₂ t₂' : .sort (.imax l₁ l₂)

  E[Γ] ⊢ t₁ ≡ t₂ : .sort l
  E[Γ] ⊢ e₁ ≡ e₂ : t₁
  ──────────────────── defeqDF {n} {Γ : Ctx ζ ℓ 0 n} {l e₁ e₂ t₁ t₂}
  E[Γ] ⊢ e₁ ≡ e₂ : t₂

  E[Γ] ⊢ t : .sort l₁
  E[Γ.snoc t] ⊢ t' : .sort l₂
  E[Γ.snoc t] ⊢ e' : t'
  E[Γ] ⊢ e : t
  E[Γ] ⊢ t'.inst e : .sort l₂
  E[Γ] ⊢ e'.inst e : t'.inst e
  ──────────────────── beta {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ e t e' t'}
  E[Γ] ⊢ .app (.lam t e') e ≡ e'.inst e : t'.inst e

  E[Γ] ⊢ t : .sort l₁
  E[Γ] ⊢ v : t
  E[Γ] ⊢ r : .sort l₂
  E[Γ] ⊢ e'.inst v : r
  ──────────────────── zeta {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ t v r e'}
  E[Γ] ⊢ .letE t v e' ≡ e'.inst v : r

  E[Γ] ⊢ t : .sort l₁
  E[Γ.snoc t] ⊢ t' : .sort l₂
  E[Γ.snoc t] ⊢ t.wk : .sort l₁
  E[Γ.snoc t] ⊢ e.wk : .forallE t.wk (t'.wkFrom n)
  E[Γ] ⊢ e : .forallE t t'
  ──────────────────── eta {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ e t t'}
  E[Γ] ⊢ .lam t (.app e.wk (.var (Fin.last n))) ≡ e : .forallE t t'

  ∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p
  E[Γ] ⊢ maj : .ind η s ls ps is
  E[Γ] ⊢ h.rebuildTerm η ls ps maj : .ind η s ls ps is
  ──────────────────── etaStruct {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s c ls ps is maj}
    (h : (E.get η).block.IsStructure s c)
  E[Γ] ⊢ h.rebuildTerm η ls ps maj ≡ maj : .ind η s ls ps is

  E[Γ] ⊢ p : .prop
  E[Γ] ⊢ h₁ : p
  E[Γ] ⊢ h₂ : p
  ──────────────────── proofIrrel {n} {Γ : Ctx ζ ℓ 0 n} {p h₁ h₂}
  E[Γ] ⊢ h₁ ≡ h₂ : p

  (E.get η).block.RecAllowed u
  ∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p
  ∀ s, E[Γ] ⊢ ms s : (E.get η).block.motiveType η ls ps u s
  ∀ s c, E[Γ] ⊢ mins s c : (E.get η).block.caseFnType η ls ps ms s c
  ∀ f, E[Γ] ⊢ fds f :
    (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
      (Fin.append ps fun previous : Fin f.val =>
        fds (previous.castLE f.isLt.le))
  ∀ f, E[Γ] ⊢ recFds f :
    (((E.get η).block.ctors s c).recursive f).instantiatedType η ls ps
      (Fin.append ps fds)
  E[Γ] ⊢ (E.get η).block.iotaType η ls ps ms s c fds recFds : .sort u
  E[Γ] ⊢ (E.get η).block.iotaLhs η ls u ps ms mins s c fds recFds :
    (E.get η).block.iotaType η ls ps ms s c fds recFds
  E[Γ] ⊢ (E.get η).block.iotaRhs η ls u ps ms mins s c fds recFds :
    (E.get η).block.iotaType η ls ps ms s c fds recFds
  ──────────────────── iota {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s c ls u ps ms mins fds recFds}
  E[Γ] ⊢ (E.get η).block.iotaLhs η ls u ps ms mins s c fds recFds ≡
    (E.get η).block.iotaRhs η ls u ps ms mins s c fds recFds :
      (E.get η).block.iotaType η ls ps ms s c fds recFds

  E[Γ] ⊢ α₁ ≡ α₂ : .sort l
  E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁
  ──────────────────── quotDF {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot} {l α₁ α₂ r₁ r₂}
  E[Γ] ⊢ .quot η l α₁ r₁ ≡ .quot η l α₂ r₂ : .sort l

  E[Γ] ⊢ α₁ ≡ α₂ : .sort l
  E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁
  E[Γ] ⊢ a₁ ≡ a₂ : α₁
  ──────────────────── quotMkDF {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot}
    {l α₁ α₂ r₁ r₂ a₁ a₂}
  E[Γ] ⊢ .quotMk η l α₁ r₁ a₁ ≡ .quotMk η l α₂ r₂ a₂ : .quot η l α₁ r₁

  E[Γ] ⊢ α₁ ≡ α₂ : .sort l₁
  E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁
  E[Γ] ⊢ β₁ ≡ β₂ : .sort l₂
  E[Γ] ⊢ f₁ ≡ f₂ : .forallE α₁ β₁.wk
  E[Γ] ⊢ h₁ ≡ h₂ : Quot.compatType (E.get η).eqHead l₂ α₁ r₁ β₁ f₁
  E[Γ] ⊢ a₁ ≡ a₂ : .quot η l₁ α₁ r₁
  ──────────────────── quotLiftDF {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot}
    {l₁ l₂ α₁ α₂ r₁ r₂ β₁ β₂ f₁ f₂ h₁ h₂ a₁ a₂}
  E[Γ] ⊢ .quotLift η l₁ l₂ α₁ r₁ β₁ f₁ h₁ a₁ ≡
    .quotLift η l₁ l₂ α₂ r₂ β₂ f₂ h₂ a₂ : β₁

  E[Γ] ⊢ α₁ ≡ α₂ : .sort l
  E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁
  E[Γ] ⊢ β₁ ≡ β₂ : Quot.motiveType η l α₁ r₁
  E[Γ] ⊢ f₁ ≡ f₂ : Quot.minorType η l α₁ r₁ β₁
  E[Γ] ⊢ a₁ ≡ a₂ : .quot η l α₁ r₁
  E[Γ] ⊢ .app β₁ a₁ ≡ .app β₂ a₂ : .prop
  ──────────────────── quotIndDF {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot}
    {l α₁ α₂ r₁ r₂ β₁ β₂ f₁ f₂ a₁ a₂}
  E[Γ] ⊢ .quotInd η l α₁ r₁ β₁ f₁ a₁ ≡ .quotInd η l α₂ r₂ β₂ f₂ a₂ : .app β₁ a₁

  E[Γ] ⊢ α : .sort l₁
  E[Γ] ⊢ r : Quot.relType α
  E[Γ] ⊢ β : .sort l₂
  E[Γ] ⊢ f : .forallE α β.wk
  E[Γ] ⊢ h : Quot.compatType (E.get η).eqHead l₂ α r β f
  E[Γ] ⊢ a : α
  E[Γ] ⊢ .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ α r a) : β
  E[Γ] ⊢ .app f a : β
  ──────────────────── quotIota {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot}
    {l₁ l₂ α r β f h a}
  E[Γ] ⊢ .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ α r a) ≡ .app f a : β

  E[Γ] ⊢ ((E.get η).constType.instL ls).wkClosed : .sort u
  E[Γ] ⊢ ((E.get η).defValue.instL ls).wkClosed :
    ((E.get η).constType.instL ls).wkClosed
  ──────────────────── delta {n nlevels : Nat} {Γ : Ctx ζ ℓ 0 n}
    {η : Head ζ (.const .def nlevels)} {ls u}
  E[Γ] ⊢ .const η ls ≡ ((E.get η).defValue.instL ls).wkClosed :
    ((E.get η).constType.instL ls).wkClosed

namespace Defeq

@[app_unexpander Defeq]
meta def unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $E $Γ $e₁ $e₂ $t) =>
    if e₁ == e₂ then
      `($E[$Γ] ⊢ $e₁ : $t)
    else
      `($E[$Γ] ⊢ $e₁ ≡ $e₂ : $t)
  | _ => throw ()

variable {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}

theorem left :
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    E[Γ] ⊢ e₁ : t :=
  fun h => h.trans h.symm

theorem right :
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    E[Γ] ⊢ e₂ : t :=
  fun h => h.symm.trans h

end Defeq

variable {E : Env ζ} {ℓ n m : Nat} {Γ Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m}

theorem Defeq.regular {e₁ e₂ t : Expr ζ ℓ n} :
    E[Γ] ⊢ e₁ ≡ e₂ : t →
    ∃ l : Level ℓ, E[Γ] ⊢ t : .sort l := by
  intro h
  induction h with
  | var ht => exact ⟨_, ht⟩
  | symm _ ih => exact ih
  | trans _ _ ih₁ => exact ih₁
  | sortDF => exact ⟨_, .sortDF⟩
  | constDF htype => exact ⟨_, htype.left⟩
  | indDF => exact ⟨_, .sortDF⟩
  | ctorDF _ _ _ _ _ htype => exact ⟨_, htype.left⟩
  | recrDF _ _ _ _ _ _ htype => exact ⟨_, htype.left⟩
  | appDF _ _ _ _ htype => exact ⟨_, htype.left⟩
  | lamDF ht ht' => exact ⟨_, .forallEDF ht.left ht' ht'⟩
  | forallEDF => exact ⟨_, .sortDF⟩
  | defeqDF ht => exact ⟨_, ht.right⟩
  | beta _ _ _ _ htype => exact ⟨_, htype⟩
  | zeta _ _ htype => exact ⟨_, htype⟩
  | eta ht ht' => exact ⟨_, .forallEDF ht ht' ht'⟩
  | etaStruct _ _ _ _ _ ihmaj _ => exact ihmaj
  | proofIrrel hp => exact ⟨_, hp⟩
  | iota _ _ _ _ _ _ htype _ _ _ _ _ _ _ _ _ _ => exact ⟨_, htype⟩
  | quotDF => exact ⟨_, .sortDF⟩
  | quotMkDF hα hr =>
    exact ⟨_, .quotDF hα.left hr.left⟩
  | quotLiftDF _ _ hβ => exact ⟨_, hβ.left⟩
  | quotIndDF _ _ _ _ _ htype => exact ⟨_, htype.left⟩
  | quotIota _ _ hβ => exact ⟨_, hβ.left⟩
  | delta htype => exact ⟨_, htype⟩

def SubstWF (E : Env ζ) {ℓ n m : Nat} (Γ₁ : Ctx ζ ℓ 0 n) (Γ₂ : Ctx ζ ℓ 0 m) (σ : Subst ζ ℓ n m) : Prop :=
  ∀ v : Var n, E[Γ₂] ⊢ σ v : (Γ₁.get v).subst σ

notation:65 E "[" Γ₂ "]" " ⊢ " σ:51 " ⊣ " Γ₁:51 => SubstWF E Γ₁ Γ₂ σ

@[app_unexpander SubstWF]
meta def SubstWF.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $E $Γ₁ $Γ₂ $σ) => `($E[$Γ₂] ⊢ $σ ⊣ $Γ₁)
  | _ => throw ()

def SubstEq (E : Env ζ) {ℓ n m : Nat} (Γ₁ : Ctx ζ ℓ 0 n) (Γ₂ : Ctx ζ ℓ 0 m)
    (σ₁ σ₂ : Subst ζ ℓ n m) : Prop :=
  ∀ v : Var n, E[Γ₂] ⊢ σ₁ v ≡ σ₂ v : (Γ₁.get v).subst σ₁

notation:65 E "[" Γ₂ "]" " ⊢ " σ₁:51 " ≡ " σ₂:51 " ⊣ " Γ₁:51 => SubstEq E Γ₁ Γ₂ σ₁ σ₂

@[app_unexpander SubstEq]
meta def SubstEq.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $E $Γ₁ $Γ₂ $σ₁ $σ₂) => `($E[$Γ₂] ⊢ $σ₁ ≡ $σ₂ ⊣ $Γ₁)
  | _ => throw ()

theorem SubstEq.left {σ₁ σ₂ : Subst ζ ℓ n m} :
    E[Γ₂] ⊢ σ₁ ≡ σ₂ ⊣ Γ₁ →
    E[Γ₂] ⊢ σ₁ ⊣ Γ₁ :=
  fun h v => (h v).left

@[implicit_reducible] def IsType (E : Env ζ) {ℓ n : Nat}
    (Γ : Ctx ζ ℓ 0 n) (t : Expr ζ ℓ n) : Prop :=
  ∃ u, E[Γ] ⊢ t : .sort u

notation:65 E "[" Γ "]" " ⊢ " t:51 " typ" => IsType E Γ t

def CtxWF (E : Env ζ) {ℓ n : Nat} (Γ : Ctx ζ ℓ 0 n) : Prop :=
  Γ.Forall fun Γ₁ t => E[Γ₁] ⊢ t typ

notation:65 E "[" Γ "]" " ⊢ " "ok" => CtxWF E Γ

variable (E) {ι : IndSig} (I : Inductive ζ ι) {nfields : Nat} {s : Fin ι.nsorts}

include E

def TeleWF (P : Level ℓ → Prop) (Γ : Ctx ζ ℓ 0 n) (Δ : Ctx ζ ℓ n m) : Prop :=
  Δ.Forall fun Δ' t => ∃ u, P u ∧ E[Γ ++ Δ'] ⊢ t : .sort u

def Inductive.IdxWF (Γ : Ctx ζ ℓ 0 n) (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n) (is : Fin (ι.nindices s) → Expr ζ ℓ n) : Prop :=
  ∀ i, E[Γ] ⊢ is i : I.indexType ls s ps is i

structure FieldWF (Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields))
    (fd : Field ζ ι nfields) : Prop where
  typeExact : E[Γ] ⊢ fd.type : .sort fd.level
  levelOK : I.LevelOK fd.level

structure RecFieldWF (Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields))
    {arity : Nat} (fd : RecField ζ ι nfields arity s) : Prop where
  tele : TeleWF E I.LevelOK Γ fd.tele
  indices :
    I.IdxWF E (Γ ++ fd.tele) s Level.param (fun p => .var ⟨p.val, by omega⟩) fd.indices

structure CtorWF {csig : CtorSig ι.nsorts} (ctor : Ctor ζ ι s csig) : Prop where
  ordinary : ∀ f,
    FieldWF E I (I.params ++ ctor.ordinaryTeleAux f.val (by omega)) (ctor.ordinary f)
  recursive : ∀ f,
    RecFieldWF E I (I.params ++ ctor.ordinaryTele) (ctor.recursive f)
  targetIndices :
    I.IdxWF E (I.params ++ ctor.ordinaryTele) s Level.param
      (fun p => .var ⟨p.val, by omega⟩) ctor.targetIndices

structure InductiveWF (E : Env ζ) (I : Inductive ζ ι) : Prop where
  params : TeleWF E (fun _ => True) .nil I.params
  indices : ∀ s : Fin ι.nsorts,
    TeleWF E (fun _ => True) I.params (I.indices s)
  ctors : ∀ (s : Fin ι.nsorts) (c : Fin (ι.nctors s)),
    CtorWF E I (I.ctors s c)

end Metalean
