/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Env
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean

variable {ζ : Sigs}

set_option hygiene false in
notation:65 E "[" Γ "]" " ⊢ₛ " e₁:51 " ≡ " e₂:51 " : " t:lead => DefeqStrong E Γ e₁ e₂ t
set_option hygiene false in
notation:65 E "[" Γ "]" " ⊢ₛ " e:51 " : " t:lead => DefeqStrong E Γ e e t

/-- Definitional equality with regularity -/
judgement DefeqStrong (E : Env ζ) {ℓ : Nat} :
    {n : Nat} → Ctx ζ ℓ 0 n → Expr ζ ℓ n → Expr ζ ℓ n → Expr ζ ℓ n → Prop where

  E[Γ] ⊢ₛ Γ.get v : .sort l
  ──────────────────── var {n} {Γ : Ctx ζ ℓ 0 n} {v : Var n} {l}
  E[Γ] ⊢ₛ .var v : Γ.get v

  E[Γ] ⊢ₛ e₁ ≡ e₂ : t
  ──────────────────── symm {n} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t}
  E[Γ] ⊢ₛ e₂ ≡ e₁ : t

  E[Γ] ⊢ₛ e₁ ≡ e₂ : t
  E[Γ] ⊢ₛ e₂ ≡ e₃ : t
  ──────────────────── trans {n} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ e₃ t}
  E[Γ] ⊢ₛ e₁ ≡ e₃ : t

  ──────────────────── sortDF {n} {Γ : Ctx ζ ℓ 0 n} {l}
  E[Γ] ⊢ₛ .sort l : .sort (.succ l)

  E[Γ] ⊢ₛ ((E.get η).constType.instL ls).wkClosed : .sort l
  ──────────────────── constDF {n nlevels kind} {Γ : Ctx ζ ℓ 0 n}
    {η : Head ζ (.const kind nlevels)} {ls l}
  E[Γ] ⊢ₛ .const η ls : ((E.get η).constType.instL ls).wkClosed

  ∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p
  ∀ i, E[Γ] ⊢ₛ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i
  ──────────────────── indDF {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s ls ps₁ ps₂ is₁ is₂}
  E[Γ] ⊢ₛ .ind η s ls ps₁ is₁ ≡ .ind η s ls ps₂ is₂ :
    .sort ((E.get η).block.level.inst ls)

  ∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p
  ∀ f, E[Γ] ⊢ₛ fds₁ f ≡ fds₂ f :
    (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
      (Fin.append ps₁ fun previous : Fin f.val => fds₁ (previous.castLE f.isLt.le))
  ∀ f, E[Γ] ⊢ₛ recFds₁ f ≡ recFds₂ f :
    (((E.get η).block.ctors s c).recursive f).instantiatedType
      η ls ps₁ (Fin.append ps₁ fds₁)
  ∀ f, E[Γ] ⊢ₛ ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f ≡
    ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps₂ fds₂ f :
      .sort (fieldLevels f)
  ∀ f, E[Γ] ⊢ₛ ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f ≡
    ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps₂ fds₂ f :
      .sort (recFieldLevels f)
  E[Γ] ⊢ₛ .ind η s ls ps₁
      (((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁) ≡
    .ind η s ls ps₂
      (((E.get η).block.ctors s c).targetIndex ls ps₂ fds₂) :
      .sort ((E.get η).block.level.inst ls)
  ──────────────────── ctorDF {n} {Γ : Ctx ζ ℓ 0 n} {ι} {η : Head ζ (.inductive ι)}
    {s c ls ps₁ ps₂ fds₁ fds₂ recFds₁ recFds₂}
    {fieldLevels : Fin (ι.ctors s c).nfields → Level ℓ}
    {recFieldLevels : Fin (ι.ctors s c).nrecFields → Level ℓ}
  E[Γ] ⊢ₛ .ctor η s c ls ps₁ fds₁ recFds₁ ≡ .ctor η s c ls ps₂ fds₂ recFds₂ :
    .ind η s ls ps₁ (((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁)

  (E.get η).block.RecAllowed l
  ∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p
  ∀ s, E[Γ] ⊢ₛ ms₁ s ≡ ms₂ s : (E.get η).block.motiveType η ls ps₁ l s
  ∀ s c, E[Γ] ⊢ₛ mins₁ s c ≡ mins₂ s c : (E.get η).block.caseFnType η ls ps₁ ms₁ s c
  ∀ i, E[Γ] ⊢ₛ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i
  E[Γ] ⊢ₛ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁
  E[Γ] ⊢ₛ Inductive.motiveResult (ms₁ s) is₁ maj₁ ≡
    Inductive.motiveResult (ms₂ s) is₂ maj₂ : .sort l
  ──────────────────── recrDF {n} {Γ : Ctx ζ ℓ 0 n} {ι} {η : Head ζ (.inductive ι)}
    {s ls l ps₁ ps₂ ms₁ ms₂ mins₁ mins₂ is₁ is₂ maj₁ maj₂}
  E[Γ] ⊢ₛ .recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁ ≡
    .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ :
      Inductive.motiveResult (ms₁ s) is₁ maj₁

  E[Γ] ⊢ₛ t : .sort l₁
  E[Γ.snoc t] ⊢ₛ t' : .sort l₂
  E[Γ] ⊢ₛ f₁ ≡ f₂ : .forallE t t'
  E[Γ] ⊢ₛ a₁ ≡ a₂ : t
  E[Γ] ⊢ₛ t'.inst a₁ ≡ t'.inst a₂ : .sort l₂
  ──────────────────── appDF {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ f₁ f₂ a₁ a₂ t t'}
  E[Γ] ⊢ₛ .app f₁ a₁ ≡ .app f₂ a₂ : t'.inst a₁

  E[Γ] ⊢ₛ t₁ ≡ t₂ : .sort l₁
  E[Γ.snoc t₁] ⊢ₛ t' : .sort l₂
  E[Γ.snoc t₂] ⊢ₛ t' : .sort l₂
  E[Γ.snoc t₁] ⊢ₛ e₁' ≡ e₂' : t'
  E[Γ.snoc t₂] ⊢ₛ e₁' ≡ e₂' : t'
  ──────────────────── lamDF {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ t₁ t₂ e₁' e₂' t'}
  E[Γ] ⊢ₛ .lam t₁ e₁' ≡ .lam t₂ e₂' : .forallE t₁ t'

  E[Γ] ⊢ₛ t₁ ≡ t₂ : .sort l₁
  E[Γ.snoc t₁] ⊢ₛ t₁' ≡ t₂' : .sort l₂
  E[Γ.snoc t₂] ⊢ₛ t₁' ≡ t₂' : .sort l₂
  ──────────────────── forallEDF {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ t₁ t₂ t₁' t₂'}
  E[Γ] ⊢ₛ .forallE t₁ t₁' ≡ .forallE t₂ t₂' : .sort (.imax l₁ l₂)

  E[Γ] ⊢ₛ t₁ ≡ t₂ : .sort l
  E[Γ] ⊢ₛ e₁ ≡ e₂ : t₁
  ──────────────────── defeqDF {n} {Γ : Ctx ζ ℓ 0 n} {l e₁ e₂ t₁ t₂}
  E[Γ] ⊢ₛ e₁ ≡ e₂ : t₂

  E[Γ] ⊢ₛ t : .sort l₁
  E[Γ.snoc t] ⊢ₛ t' : .sort l₂
  E[Γ.snoc t] ⊢ₛ e' : t'
  E[Γ] ⊢ₛ e : t
  E[Γ] ⊢ₛ t'.inst e : .sort l₂
  E[Γ] ⊢ₛ e'.inst e : t'.inst e
  ──────────────────── beta {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ e t e' t'}
  E[Γ] ⊢ₛ .app (.lam t e') e ≡ e'.inst e : t'.inst e

  E[Γ] ⊢ₛ t : .sort l₁
  E[Γ] ⊢ₛ v : t
  E[Γ] ⊢ₛ r : .sort l₂
  E[Γ] ⊢ₛ e'.inst v : r
  ──────────────────── zeta {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ t v r e'}
  E[Γ] ⊢ₛ .letE t v e' ≡ e'.inst v : r

  E[Γ] ⊢ₛ t : .sort l₁
  E[Γ.snoc t] ⊢ₛ t' : .sort l₂
  E[Γ.snoc t] ⊢ₛ t.wk : .sort l₁
  E[Γ.snoc t] ⊢ₛ e.wk : .forallE t.wk (t'.wkFrom n)
  E[Γ] ⊢ₛ e : .forallE t t'
  ──────────────────── eta {n} {Γ : Ctx ζ ℓ 0 n} {l₁ l₂ e t t'}
  E[Γ] ⊢ₛ .lam t (.app e.wk (.var (Fin.last n))) ≡ e : .forallE t t'

  ∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p
  E[Γ] ⊢ₛ maj : .ind η s ls ps is
  E[Γ] ⊢ₛ h.rebuildTerm η ls ps maj : .ind η s ls ps is
  ──────────────────── etaStruct {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s c ls ps is maj}
    (h : (E.get η).block.IsStructure s c)
  E[Γ] ⊢ₛ h.rebuildTerm η ls ps maj ≡ maj : .ind η s ls ps is

  E[Γ] ⊢ₛ p : .prop
  E[Γ] ⊢ₛ h₁ : p
  E[Γ] ⊢ₛ h₂ : p
  ──────────────────── proofIrrel {n} {Γ : Ctx ζ ℓ 0 n} {p h₁ h₂}
  E[Γ] ⊢ₛ h₁ ≡ h₂ : p

  (E.get η).block.RecAllowed u
  ∀ p, E[Γ] ⊢ₛ ps p : (E.get η).block.paramType ls ps p
  ∀ s, E[Γ] ⊢ₛ ms s : (E.get η).block.motiveType η ls ps u s
  ∀ s c, E[Γ] ⊢ₛ mins s c : (E.get η).block.caseFnType η ls ps ms s c
  ∀ f, E[Γ] ⊢ₛ fds f :
    (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
      (Fin.append ps fun previous : Fin f.val =>
        fds (previous.castLE f.isLt.le))
  ∀ f, E[Γ] ⊢ₛ recFds f :
    (((E.get η).block.ctors s c).recursive f).instantiatedType η ls ps
      (Fin.append ps fds)
  E[Γ] ⊢ₛ (E.get η).block.iotaType η ls ps ms s c fds recFds : .sort u
  E[Γ] ⊢ₛ (E.get η).block.iotaLhs η ls u ps ms mins s c fds recFds :
    (E.get η).block.iotaType η ls ps ms s c fds recFds
  E[Γ] ⊢ₛ (E.get η).block.iotaRhs η ls u ps ms mins s c fds recFds :
    (E.get η).block.iotaType η ls ps ms s c fds recFds
  ──────────────────── iota {n} {Γ : Ctx ζ ℓ 0 n} {ι}
    {η : Head ζ (.inductive ι)} {s c ls u ps ms mins fds recFds}
  E[Γ] ⊢ₛ (E.get η).block.iotaLhs η ls u ps ms mins s c fds recFds ≡
    (E.get η).block.iotaRhs η ls u ps ms mins s c fds recFds :
      (E.get η).block.iotaType η ls ps ms s c fds recFds

  E[Γ] ⊢ₛ α₁ ≡ α₂ : .sort l
  E[Γ] ⊢ₛ r₁ ≡ r₂ : Quot.relType α₁
  ──────────────────── quotDF {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot} {l α₁ α₂ r₁ r₂}
  E[Γ] ⊢ₛ .quot η l α₁ r₁ ≡ .quot η l α₂ r₂ : .sort l

  E[Γ] ⊢ₛ α₁ ≡ α₂ : .sort l
  E[Γ] ⊢ₛ r₁ ≡ r₂ : Quot.relType α₁
  E[Γ] ⊢ₛ a₁ ≡ a₂ : α₁
  ──────────────────── quotMkDF {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot}
    {l α₁ α₂ r₁ r₂ a₁ a₂}
  E[Γ] ⊢ₛ .quotMk η l α₁ r₁ a₁ ≡ .quotMk η l α₂ r₂ a₂ : .quot η l α₁ r₁

  E[Γ] ⊢ₛ α₁ ≡ α₂ : .sort l₁
  E[Γ] ⊢ₛ r₁ ≡ r₂ : Quot.relType α₁
  E[Γ] ⊢ₛ β₁ ≡ β₂ : .sort l₂
  E[Γ] ⊢ₛ f₁ ≡ f₂ : .forallE α₁ β₁.wk
  E[Γ] ⊢ₛ h₁ ≡ h₂ : Quot.compatType (E.get η).eqHead l₂ α₁ r₁ β₁ f₁
  E[Γ] ⊢ₛ a₁ ≡ a₂ : .quot η l₁ α₁ r₁
  ──────────────────── quotLiftDF {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot}
    {l₁ l₂ α₁ α₂ r₁ r₂ β₁ β₂ f₁ f₂ h₁ h₂ a₁ a₂}
  E[Γ] ⊢ₛ .quotLift η l₁ l₂ α₁ r₁ β₁ f₁ h₁ a₁ ≡
    .quotLift η l₁ l₂ α₂ r₂ β₂ f₂ h₂ a₂ : β₁

  E[Γ] ⊢ₛ α₁ ≡ α₂ : .sort l
  E[Γ] ⊢ₛ r₁ ≡ r₂ : Quot.relType α₁
  E[Γ] ⊢ₛ β₁ ≡ β₂ : Quot.motiveType η l α₁ r₁
  E[Γ] ⊢ₛ f₁ ≡ f₂ : Quot.minorType η l α₁ r₁ β₁
  E[Γ] ⊢ₛ a₁ ≡ a₂ : .quot η l α₁ r₁
  E[Γ] ⊢ₛ .app β₁ a₁ ≡ .app β₂ a₂ : .prop
  ──────────────────── quotIndDF {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot}
    {l α₁ α₂ r₁ r₂ β₁ β₂ f₁ f₂ a₁ a₂}
  E[Γ] ⊢ₛ .quotInd η l α₁ r₁ β₁ f₁ a₁ ≡ .quotInd η l α₂ r₂ β₂ f₂ a₂ : .app β₁ a₁

  E[Γ] ⊢ₛ α : .sort l₁
  E[Γ] ⊢ₛ r : Quot.relType α
  E[Γ] ⊢ₛ β : .sort l₂
  E[Γ] ⊢ₛ f : .forallE α β.wk
  E[Γ] ⊢ₛ h : Quot.compatType (E.get η).eqHead l₂ α r β f
  E[Γ] ⊢ₛ a : α
  E[Γ] ⊢ₛ .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ α r a) : β
  E[Γ] ⊢ₛ .app f a : β
  ──────────────────── quotIota {n} {Γ : Ctx ζ ℓ 0 n} {η : Head ζ .quot}
    {l₁ l₂ α r β f h a}
  E[Γ] ⊢ₛ .quotLift η l₁ l₂ α r β f h (.quotMk η l₁ α r a) ≡ .app f a : β

  E[Γ] ⊢ₛ ((E.get η).constType.instL ls).wkClosed : .sort u
  E[Γ] ⊢ₛ ((E.get η).defValue.instL ls).wkClosed :
    ((E.get η).constType.instL ls).wkClosed
  ──────────────────── delta {n nlevels : Nat} {Γ : Ctx ζ ℓ 0 n}
    {η : Head ζ (.const .def nlevels)} {ls u}
  E[Γ] ⊢ₛ .const η ls ≡ ((E.get η).defValue.instL ls).wkClosed :
    ((E.get η).constType.instL ls).wkClosed

namespace DefeqStrong

@[app_unexpander DefeqStrong]
meta def unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $E $Γ $e₁ $e₂ $t) =>
    if e₁ == e₂ then
      `($E[$Γ] ⊢ₛ $e₁ : $t)
    else
      `($E[$Γ] ⊢ₛ $e₁ ≡ $e₂ : $t)
  | _ => throw ()

variable {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}

theorem left :
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ] ⊢ₛ e₁ : t :=
  fun h => h.trans h.symm

theorem right :
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ] ⊢ₛ e₂ : t :=
  fun h => h.symm.trans h

theorem defeq :
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    E[Γ] ⊢ e₁ ≡ e₂ : t := by
  intro h
  induction h with
  | var => exact .var
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | sortDF => exact .sortDF
  | constDF => exact .constDF
  | indDF _ _ hps his => exact .indDF hps his
  | ctorDF _ _ _ _ _ _ hps hfields hrecFields _ _ =>
    exact .ctorDF hps hfields hrecFields
  | recrDF hallowed _ _ _ _ _ _ hps hms hmins his hmaj _ =>
    exact .recrDF hallowed hps hms hmins his hmaj
  | appDF _ _ _ _ _ _ _ ihf ihe _ => exact .appDF ihf ihe
  | lamDF _ _ _ _ _ iht _ _ ihbody _ => exact .lamDF iht ihbody
  | forallEDF _ _ _ iht ihbody _ => exact .forallEDF iht ihbody
  | defeqDF _ _ iht ihe => exact .defeqDF iht ihe
  | beta _ _ _ _ _ _ _ _ ihbody ihe _ _ => exact .beta ihbody ihe
  | zeta _ _ _ _ iht ihv _ ihbody => exact .zeta iht ihv ihbody
  | eta _ _ _ _ _ _ _ _ _ ihe => exact .eta ihe
  | etaStruct h _ _ _ ihps ihmaj _ => exact .etaStruct h ihps ihmaj
  | proofIrrel _ _ _ _ ihh ihh' => exact .proofIrrel ‹_› ihh ihh'
  | iota hallowed _ _ _ _ _ _ _ _ ihps ihms ihmins ihfields ihrecFields _ _ _ =>
    exact .iota hallowed ihps ihms ihmins ihfields ihrecFields
  | quotDF _ _ ihα ihr => exact .quotDF ihα ihr
  | quotMkDF _ _ _ ihα ihr iha => exact .quotMkDF ihα ihr iha
  | quotLiftDF _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    exact .quotLiftDF ihα ihr ihβ ihf ihh iha
  | quotIndDF _ _ _ _ _ _ ihα ihr ihβ ihf iha _ =>
    exact .quotIndDF ihα ihr ihβ ihf iha
  | quotIota _ _ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha ihlhs ihrhs =>
    exact .quotIota ihα ihr ihβ ihf ihh iha ihlhs ihrhs
  | delta => exact .delta

end DefeqStrong

section

variable {E : Env ζ} {ℓ n m : Nat} {Γ Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m}

theorem DefeqStrong.regular {e₁ e₂ t : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    ∃ l : Level ℓ, E[Γ] ⊢ₛ t : .sort l := by
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

def SubstWFStrong (E : Env ζ) {ℓ n m : Nat} (Γ₁ : Ctx ζ ℓ 0 n) (Γ₂ : Ctx ζ ℓ 0 m) (σ : Subst ζ ℓ n m) : Prop :=
  ∀ v : Var n, E[Γ₂] ⊢ₛ σ v : (Γ₁.get v).subst σ

notation:65 E "[" Γ₂ "]" " ⊢ₛ " σ:51 " ⊣ " Γ₁:51 => SubstWFStrong E Γ₁ Γ₂ σ

@[app_unexpander SubstWFStrong]
meta def SubstWFStrong.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $E $Γ₁ $Γ₂ $σ) => `($E[$Γ₂] ⊢ₛ $σ ⊣ $Γ₁)
  | _ => throw ()

def SubstEqStrong (E : Env ζ) {ℓ n m : Nat} (Γ₁ : Ctx ζ ℓ 0 n) (Γ₂ : Ctx ζ ℓ 0 m)
    (σ₁ σ₂ : Subst ζ ℓ n m) : Prop :=
  ∀ v : Var n, E[Γ₂] ⊢ₛ σ₁ v ≡ σ₂ v : (Γ₁.get v).subst σ₁

notation:65 E "[" Γ₂ "]" " ⊢ₛ " σ₁:51 " ≡ " σ₂:51 " ⊣ " Γ₁:51 => SubstEqStrong E Γ₁ Γ₂ σ₁ σ₂

@[app_unexpander SubstEqStrong]
meta def SubstEqStrong.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $E $Γ₁ $Γ₂ $σ₁ $σ₂) => `($E[$Γ₂] ⊢ₛ $σ₁ ≡ $σ₂ ⊣ $Γ₁)
  | _ => throw ()

theorem SubstEqStrong.left {σ₁ σ₂ : Subst ζ ℓ n m} :
    E[Γ₂] ⊢ₛ σ₁ ≡ σ₂ ⊣ Γ₁ →
    E[Γ₂] ⊢ₛ σ₁ ⊣ Γ₁ :=
  fun h v => (h v).left

@[implicit_reducible] def IsTypeStrong (E : Env ζ) {ℓ n : Nat}
    (Γ : Ctx ζ ℓ 0 n) (t : Expr ζ ℓ n) : Prop :=
  ∃ u, E[Γ] ⊢ₛ t : .sort u

notation:65 E "[" Γ "]" " ⊢ₛ " t:51 " typ" => IsTypeStrong E Γ t

def CtxWFStrong (E : Env ζ) {ℓ n : Nat} (Γ : Ctx ζ ℓ 0 n) : Prop :=
  Γ.Forall fun Γ₁ t => E[Γ₁] ⊢ₛ t typ

notation:65 E "[" Γ "]" " ⊢ₛ " "ok" => CtxWFStrong E Γ

end

variable (E : Env ζ) {ℓ n m : Nat}
  {ι : IndSig} (I : Inductive ζ ι)
  {nfields : Nat}

include E

def WFTeleStrong (P : Level ℓ → Prop)
    (Γ : Ctx ζ ℓ 0 n) (Δ : Ctx ζ ℓ n m) : Prop :=
  Δ.Forall fun Δ' t => ∃ u, P u ∧ E[Γ ++ Δ'] ⊢ₛ t : .sort u

def Inductive.IdxWFStrong (Γ : Ctx ζ ℓ 0 n)
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) : Prop :=
  ∀ i, E[Γ] ⊢ₛ is i : I.indexType ls s ps is i

structure Field.WFStrong (Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields))
    (fd : Field ζ ι nfields) : Prop where
  typeExact : E[Γ] ⊢ₛ fd.type : .sort fd.level
  levelOK : I.LevelOK fd.level

variable {s : Fin ι.nsorts}

structure RecField.WFStrong (Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields))
    {arity : Nat} (fd : RecField ζ ι nfields arity s) : Prop where
  tele : WFTeleStrong E I.LevelOK Γ fd.tele
  indices :
    I.IdxWFStrong E (Γ ++ fd.tele) s Level.param
      (fun p => .var ⟨p.val, by omega⟩) fd.indices

structure Ctor.WFStrong {csig : CtorSig ι.nsorts} (ctor : Ctor ζ ι s csig) : Prop where
  ordinary : ∀ f,
    Field.WFStrong E I
      (I.params ++ ctor.ordinaryTeleAux f.val (by omega))
      (ctor.ordinary f)
  recursive : ∀ f,
    RecField.WFStrong E I (I.params ++ ctor.ordinaryTele)
      (ctor.recursive f)
  targetIndices :
    I.IdxWFStrong E (I.params ++ ctor.ordinaryTele) s Level.param
      (fun p => .var ⟨p.val, by omega⟩) ctor.targetIndices

end Metalean
