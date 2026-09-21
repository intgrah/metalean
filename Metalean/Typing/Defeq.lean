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
notation:65 E "[" Γ "]" " ⊢ " e₁ " ≡ " e₂ " : " t:lead => Defeq E Γ e₁ e₂ t
set_option hygiene false in
notation:65 E "[" Γ "]" " ⊢ " e " : " t:lead => Defeq E Γ e e t

judgement Defeq (E : Env ζ) {ℓ : Nat} :
    {n : Nat} → Ctx ζ ℓ 0 n → Expr ζ ℓ n → Expr ζ ℓ n → Expr ζ ℓ n → Prop where

  /-- Variable -/
  ──────────────────── var {n} {Γ : Ctx ζ ℓ 0 n} {v}
  E[Γ] ⊢ .var v : Γ.get v

  /-- Symmetry -/
  E[Γ] ⊢ e₁ ≡ e₂ : t
  ──────────────────── symm {n} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t}
  E[Γ] ⊢ e₂ ≡ e₁ : t

  /-- Transitivity -/
  E[Γ] ⊢ e₁ ≡ e₂ : t
  E[Γ] ⊢ e₂ ≡ e₃ : t
  ──────────────────── trans {n} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ e₃ t}
  E[Γ] ⊢ e₁ ≡ e₃ : t

  /-- Sort -/
  ──────────────────── sortDF {n} {Γ : Ctx ζ ℓ 0 n} {l}
  E[Γ] ⊢ .sort l : .sort (.succ l)

  /-- Constant -/
  ──────────────────── constDF {n nlevels kind} {Γ : Ctx ζ ℓ 0 n}
    {η : Head ζ (.const kind nlevels)} {ls}
  E[Γ] ⊢ .const η ls ≡ .const η ls :
    ((E.get η).constType.instL ls).wkClosed

  /-- Inductive type former -/
  ∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p
  ∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i
  ──────────────────── indDF {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s ls ps₁ ps₂ is₁ is₂}
  E[Γ] ⊢ .ind η s ls ps₁ is₁ ≡ .ind η s ls ps₂ is₂ : .sort ((E.get η).block.level.inst ls)

  /-- Inductive type constructor -/
  ∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
    (E.get η).block.paramType ls ps₁ p
  ∀ f, E[Γ] ⊢ fds₁ f ≡ fds₂ f :
    ((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
      (Fin.append ps₁ fun previous : Fin f.val => fds₁ (previous.castLE f.isLt.le))
  ∀ f, E[Γ] ⊢ recFds₁ f ≡ recFds₂ f :
    (((E.get η).block.ctors s c).recursive f).instantiatedType η ls ps₁
      (Fin.append ps₁ fds₁)
  ──────────────────── ctorDF {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s c ls ps₁ ps₂ fds₁ fds₂ recFds₁ recFds₂}
  E[Γ] ⊢ .ctor η s c ls ps₁ fds₁ recFds₁ ≡ .ctor η s c ls ps₂ fds₂ recFds₂ :
    .ind η s ls ps₁ (((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁)

  /-- Inductive type recursor -/
  (E.get η).block.RecAllowed l
  ∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p
  ∀ s, E[Γ] ⊢ ms₁ s ≡ ms₂ s : (E.get η).block.motiveType η ls ps₁ l s
  ∀ s c, E[Γ] ⊢ mins₁ s c ≡ mins₂ s c : (E.get η).block.caseFnType η ls ps₁ ms₁ s c
  ∀ i, E[Γ] ⊢ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i
  E[Γ] ⊢ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁
  ──────────────────── recrDF {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)}
    {s ls l ps₁ ps₂ ms₁ ms₂ mins₁ mins₂ is₁ is₂ maj₁ maj₂}
  E[Γ] ⊢ .recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁ ≡
    .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ :
      Inductive.motiveResult (ms₁ s) is₁ maj₁

  /-- Congruence in application -/
  E[Γ] ⊢ f₁ ≡ f₂ : .forallE t t'
  E[Γ] ⊢ a₁ ≡ a₂ : t
  ──────────────────── appDF {n} {Γ : Ctx ζ ℓ 0 n} {f₁ f₂ a₁ a₂ t t'}
  E[Γ] ⊢ .app f₁ a₁ ≡ .app f₂ a₂ : t'.inst a₁

  /-- Congruence in λ -/
  E[Γ] ⊢ t₁ ≡ t₂ : .sort l
  E[Γ.snoc t₁] ⊢ e₁' ≡ e₂' : t'
  ──────────────────── lamDF {n} {Γ : Ctx ζ ℓ 0 n} {l e₁' e₂' t' t₁ t₂}
  E[Γ] ⊢ .lam t₁ e₁' ≡ .lam t₂ e₂' : .forallE t₁ t'

  /-- Congruence in Π -/
  E[Γ] ⊢ t₁ ≡ t₂ : .sort l₁
  E[Γ.snoc t₁] ⊢ t₁' ≡ t₂' : .sort l₂
  ──────────────────── forallEDF {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ t₁' t₂' t₁ t₂}
  E[Γ] ⊢ .forallE t₁ t₁' ≡ .forallE t₂ t₂' : .sort (.imax l₁ l₂)

  /-- Conversion -/
  E[Γ] ⊢ t₁ ≡ t₂ : .sort l
  E[Γ] ⊢ e₁ ≡ e₂ : t₁
  ──────────────────── defeqDF {n} {Γ : Ctx ζ ℓ 0 n} {l e₁ e₂ t₁ t₂}
  E[Γ] ⊢ e₁ ≡ e₂ : t₂

  /-- β reduction -/
  E[Γ.snoc t] ⊢ e' : t'
  E[Γ] ⊢ e : t
  ──────────────────── beta {n} {Γ : Ctx ζ ℓ 0 n} {e t e' t'}
  E[Γ] ⊢ .app (.lam t e') e ≡ e'.inst e : t'.inst e

  /-- ζ reduction -/
  E[Γ] ⊢ t : .sort l
  E[Γ] ⊢ v : t
  E[Γ] ⊢ e'.inst v : r
  ──────────────────── zeta {n} {Γ : Ctx ζ ℓ 0 n} {l t v e' r}
  E[Γ] ⊢ .letE t v e' ≡ e'.inst v : r

  /-- η reduction -/
  E[Γ] ⊢ e : .forallE t t'
  ──────────────────── eta {n} {Γ : Ctx ζ ℓ 0 n} {e t t'}
  E[Γ] ⊢ .lam t (.app e.wk (.var (Fin.last n))) ≡ e : .forallE t t'

  /-- η reduction for structure-like inductives -/
  ∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p
  E[Γ] ⊢ maj : .ind η s ls ps is
  ──────────────────── etaStruct {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s c ls ps is maj} (h : (E.get η).block.IsStructure s c)
  E[Γ] ⊢ h.rebuildTerm η ls ps maj ≡ maj : .ind η s ls ps is

  /-- Proof irrelevance -/
  E[Γ] ⊢ p : .prop
  E[Γ] ⊢ h₁ : p
  E[Γ] ⊢ h₂ : p
  ──────────────────── proofIrrel {n} {Γ : Ctx ζ ℓ 0 n} {p h₁ h₂}
  E[Γ] ⊢ h₁ ≡ h₂ : p

  /-- ι reduction -/
  (E.get η).block.RecAllowed l
  ∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p
  ∀ s, E[Γ] ⊢ ms s : (E.get η).block.motiveType η ls ps l s
  ∀ s c, E[Γ] ⊢ mins s c : (E.get η).block.caseFnType η ls ps ms s c
  ∀ f, E[Γ] ⊢ fds f : ((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
      (Fin.append ps fun previous : Fin f.val => fds (previous.castLE f.isLt.le))
  ∀ f, E[Γ] ⊢ recFds f :
    (((E.get η).block.ctors s c).recursive f).instantiatedType
      η ls ps (Fin.append ps fds)
  ──────────────────── iota {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s c ls l ps ms mins fds recFds}
  E[Γ] ⊢ (E.get η).block.iotaLhs η ls l ps ms mins s c fds recFds ≡
    (E.get η).block.iotaRhs η ls l ps ms mins s c fds recFds :
      (E.get η).block.iotaType η ls ps ms s c fds recFds

  /-- Quotient type former -/
  E[Γ] ⊢ α₁ ≡ α₂ : .sort l
  E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁
  ──────────────────── quotDF {n} {Γ : Ctx ζ ℓ 0 n} {η l α₁ α₂ r₁ r₂}
  E[Γ] ⊢ .quot η l α₁ r₁ ≡ .quot η l α₂ r₂ : .sort l

  /-- Quotient constructor -/
  E[Γ] ⊢ α₁ ≡ α₂ : .sort l
  E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁
  E[Γ] ⊢ a₁ ≡ a₂ : α₁
  ──────────────────── quotMkDF {n} {Γ : Ctx ζ ℓ 0 n} {η l α₁ α₂ r₁ r₂ a₁ a₂}
  E[Γ] ⊢ .quotMk η l α₁ r₁ a₁ ≡ .quotMk η l α₂ r₂ a₂ : .quot η l α₁ r₁

  /-- Quotient lift -/
  E[Γ] ⊢ α₁ ≡ α₂ : .sort l₁
  E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁
  E[Γ] ⊢ β₁ ≡ β₂ : .sort l₂
  E[Γ] ⊢ f₁ ≡ f₂ : .forallE α₁ β₁.wk
  E[Γ] ⊢ h₁ ≡ h₂ : Quot.compatType (E.get η).eqHead l₂ α₁ r₁ β₁ f₁
  E[Γ] ⊢ a₁ ≡ a₂ : .quot η l₁ α₁ r₁
  ──────────────────── quotLiftDF {n} {Γ : Ctx ζ ℓ 0 n}
    {η l₁ l₂ α₁ α₂ r₁ r₂ β₁ β₂ f₁ f₂ h₁ h₂ a₁ a₂}
  E[Γ] ⊢ .quotLift η l₁ l₂ α₁ r₁ β₁ f₁ h₁ a₁ ≡
    .quotLift η l₁ l₂ α₂ r₂ β₂ f₂ h₂ a₂ : β₁

  /-- Quotient induction -/
  E[Γ] ⊢ α₁ ≡ α₂ : .sort l
  E[Γ] ⊢ r₁ ≡ r₂ : Quot.relType α₁
  E[Γ] ⊢ β₁ ≡ β₂ : Quot.motiveType η l α₁ r₁
  E[Γ] ⊢ f₁ ≡ f₂ : Quot.minorType η l α₁ r₁ β₁
  E[Γ] ⊢ a₁ ≡ a₂ : .quot η l α₁ r₁
  ──────────────────── quotIndDF {n} {Γ : Ctx ζ ℓ 0 n}
    {η l α₁ α₂ r₁ r₂ β₁ β₂ f₁ f₂ a₁ a₂}
  E[Γ] ⊢ .quotInd η l α₁ r₁ β₁ f₁ a₁ ≡
    .quotInd η l α₂ r₂ β₂ f₂ a₂ : .app β₁ a₁

  /-- Quotient computation -/
  E[Γ] ⊢ α : .sort l₁
  E[Γ] ⊢ r : Quot.relType α
  E[Γ] ⊢ β : .sort l₂
  E[Γ] ⊢ f : .forallE α β.wk
  E[Γ] ⊢ h : Quot.compatType (E.get η).eqHead l₂ α r β f
  E[Γ] ⊢ a : α
  E[Γ] ⊢ .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ α r a) : β
  E[Γ] ⊢ .app f a : β
  ──────────────────── quotIota {n} {Γ : Ctx ζ ℓ 0 n} {η l₁ l₂ α r β f h a}
  E[Γ] ⊢ .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ α r a) ≡ .app f a : β

  /-- δ reduction i.e. unfolding -/
  ──────────────────── delta {n nlevels : Nat} {Γ : Ctx ζ ℓ 0 n}
    {η : Head ζ (.const .def nlevels)} {ls}
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

end Defeq

def IsType (E : Env ζ) {ℓ n} (Γ : Ctx ζ ℓ 0 n) (t : Expr ζ ℓ n) : Prop :=
  ∃ l, E[Γ] ⊢ t : .sort l

notation:65 E "[" Γ "]" " ⊢ " t " typ" => IsType E Γ t

@[app_unexpander IsType]
meta def IsType.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $E $Γ $t) => `($E[$Γ] ⊢ $t typ)
  | _ => throw ()

end Metalean
