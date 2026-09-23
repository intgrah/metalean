/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Whnf
public import Metalean.Checker.Eta
public import Metalean.Decide
public import Metalean.Control
public import Metalean.Typing.Substitution
public import Metalean.Typing.Telescope
public import Metalean.Metatheory.Conversion
public import Metalean.Metatheory.Injectivity
public import Metalean.Metatheory.SubjectReduction
import Metalean.Typing.Env
import Metalean.Meta.IfRfl
import Metalean.Metatheory.Unique

@[expose] public section

namespace Metalean.Checker

open Frontend (Failure)

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

mutual

partial def whnfType {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) (t₁ : Expr ζ ℓ n) (ht : E[Γ] ⊢ t₁ typ) :
    Except Failure {t₂ : Expr ζ ℓ n // E[Γ] ⊢ t₁ ≡ t₂ typ} := do
  let ⟨_, hty⟩ ← infer hE hΓ t₁
  let ⟨t₂, hred⟩ ← whnf hE hΓ t₁ hty
  pure ⟨t₂, have ⟨_, htu⟩ := ht; .ofDefEq (hred.retype hE hΓ htu)⟩

partial def ensureSort {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {e t : Expr ζ ℓ n} (hty : E[Γ] ⊢ e : t) :
    Except Failure {l : Level ℓ // E[Γ] ⊢ e : .sort l} := do
  let ⟨.sort l, hred⟩ ← whnfType hE hΓ t hty.regular | throw (.reject .notSort)
  pure ⟨l, hred.conv hty⟩

partial def ensureForall {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) {e t : Expr ζ ℓ n} (hty : E[Γ] ⊢ e : t) :
    Except Failure ((t₁ : Expr ζ ℓ n) × {t' : Expr ζ ℓ (n + 1) //
      E[Γ] ⊢ e : .forallE t₁ t'}) := do
  let ⟨.forallE t₁ t', hred⟩ ← whnfType hE hΓ t hty.regular | throw (.reject .notForall)
  pure ⟨t₁, t', hred.conv hty⟩

partial def infer (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok) :
    (e : Expr ζ ℓ n) → Except Failure {t : Expr ζ ℓ n // E[Γ] ⊢ e : t}
  | .var v => pure ⟨Γ.get v, hΓ.var v⟩
  | .sort l => pure ⟨.sort (.succ l), .sortDF⟩
  | .const η ls =>
    pure ⟨(E.get η).constType{ls}.wkClosed,
      have ⟨_, htype⟩ := (hE.entryWF η).constType (Γ := Γ) ls
      .constDF htype⟩
  | .ind η s ls ps is => do
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      checkAgainst hE hΓ (ps p) ((E.get η).block.paramType ls ps p)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      checkAgainst hE hΓ (is i) ((E.get η).block.indexType ls s ps is i)
    pure ⟨.sort (E.get η).block.level{ls},
      .indDF hps his⟩
  | .ctor η s c ls ps fds recFds => do
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      checkAgainst hE hΓ (ps p) ((E.get η).block.paramType ls ps p)
    let ⟨hfds⟩ ← Fin.sequenceM fun f =>
      checkAgainst hE hΓ (fds f)
        (((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
    let ⟨hrecFds⟩ ← Fin.sequenceM fun f =>
      checkAgainst hE hΓ (recFds f)
        (((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f)
    pure ⟨.ind η s ls ps fun index => ((E.get η).block.ctors s c).targetIndex ls ps fds index,
      (by
        have hi := (hE.entryWF η).block
        exact .ctorDF hps hfds hrecFds
          (fun f => (hi.ctors s c).ordinaryFieldExpr_congr hi.params f hps (fun g _ => hfds g))
          (fun f => ((hi.ctors s c).recursiveFieldExpr_congr hi.params rfl f hps hfds).choose_spec)
          ((hE.entryWF η).ctorType s c hps hfds))⟩
  | .recr η s ls l ps ms mins is maj => do
    let ⟨hrec⟩ ← guardProofOr ((E.get η).block.RecAllowed l) (.reject .recursorLevel)
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      checkAgainst hE hΓ (ps p) ((E.get η).block.paramType ls ps p)
    let ⟨hms⟩ ← Fin.sequenceM fun t =>
      checkAgainst hE hΓ (ms t) ((E.get η).block.motiveType η ls ps l t)
    let ⟨hmins⟩ ← Fin.sequenceM fun t => Fin.sequenceM fun c =>
      checkAgainst hE hΓ (mins t c) ((E.get η).block.caseFnType η ls ps ms t c)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      checkAgainst hE hΓ (is i) ((E.get η).block.indexType ls s ps is i)
    let ⟨hmaj⟩ ← checkAgainst hE hΓ maj (.ind η s ls ps is)
    pure ⟨Inductive.motiveResult (ms s) is maj,
      .recrDF hrec hps hms hmins his hmaj
        ((hE.entryWF η).block.motiveResult_congr hΓ hps hms his hmaj)⟩
  | .quot _ l α r => do
    let ⟨hα⟩ ← checkAgainst hE hΓ α (.sort l)
    let ⟨hr⟩ ← checkAgainst hE hΓ r (Quot.relType α)
    pure ⟨.sort l, .quotDF hα hr⟩
  | .quotMk η l α r e => do
    let ⟨hα⟩ ← checkAgainst hE hΓ α (.sort l)
    let ⟨hr⟩ ← checkAgainst hE hΓ r (Quot.relType α)
    let ⟨he⟩ ← checkAgainst hE hΓ e α
    pure ⟨.quot η l α r, .quotMkDF hα hr he⟩
  | .quotLift η l₁ l₂ α r β f h a => do
    let ⟨hα⟩ ← checkAgainst hE hΓ α (.sort l₁)
    let ⟨hr⟩ ← checkAgainst hE hΓ r (Quot.relType α)
    let ⟨hβ⟩ ← checkAgainst hE hΓ β (.sort l₂)
    let ⟨hf⟩ ← checkAgainst hE hΓ f (.forallE α β.wk)
    let ⟨hcompat⟩ ← checkAgainst hE hΓ h (Quot.compatType (E.get η).eqHead l₂ α r β f)
    let ⟨ha⟩ ← checkAgainst hE hΓ a (.quot η l₁ α r)
    pure ⟨β, .quotLiftDF hα hr hβ hf hcompat ha⟩
  | .quotInd η l α r β f e => do
    let ⟨hα⟩ ← checkAgainst hE hΓ α (.sort l)
    let ⟨hr⟩ ← checkAgainst hE hΓ r (Quot.relType α)
    let ⟨hβ⟩ ← checkAgainst hE hΓ β (Quot.motiveType η l α r)
    let ⟨hf⟩ ← checkAgainst hE hΓ f (Quot.minorType η l α r β)
    let ⟨he⟩ ← checkAgainst hE hΓ e (.quot η l α r)
    pure ⟨.app β e, .quotIndDF hα hr hβ hf he
      (.appDF (.quotDF hα.left hr.left) .sortDF hβ he .sortDF)⟩
  | .app e e₁ => do
    let ⟨_, hfn⟩ ← infer hE hΓ e
    let ⟨t, t', hpi⟩ ← ensureForall hE hΓ hfn
    let ⟨t₁, harg⟩ ← infer hE hΓ e₁
    have hinv : E[Γ] ⊢ t typ ∧ E[Γ.snoc t] ⊢ t' typ :=
      have ⟨_, hty⟩ := hpi.regular
      hty.forallE_inv
    let ⟨hconv⟩ ← checkTypeEq hE hΓ t₁ t harg.regular hinv.1
    pure ⟨t'.inst e₁, (by
      have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := hinv
      exact .appDF ht ht' hpi (hconv.conv harg) (ht'.inst_congr (hconv.conv harg)))⟩
  | .lam t e' => do
    let ⟨l, ht⟩ ← checkIsType hE hΓ t
    let ⟨t', he'⟩ ← infer hE (hΓ.snoc ⟨l, ht⟩) e'
    pure ⟨.forallE t t',
      have ⟨_, ht'⟩ := he'.regular
      .lamDF ht ht' ht' he' he'⟩
  | .forallE t t' => do
    let ⟨l, ht⟩ ← checkIsType hE hΓ t
    let ⟨l₁, ht'⟩ ← checkIsType hE (hΓ.snoc ⟨l, ht⟩) t'
    pure ⟨.sort (.imax l l₁), .forallEDF ht ht' ht'⟩
  | .letE t v e' => do
    let ⟨_, ht⟩ ← checkIsType hE hΓ t
    let ⟨hv⟩ ← checkAgainst hE hΓ v t
    let ⟨r, hb⟩ ← infer hE hΓ (e'.inst v)
    pure ⟨r,
      have ⟨_, hr⟩ := hb.regular
      (Defeq.zeta ht hv hr hb).left⟩

partial def checkIsType (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) (t : Expr ζ ℓ n) :
    Except Failure {l : Level ℓ // E[Γ] ⊢ t : .sort l} := do
  let ⟨_, hts⟩ ← infer hE hΓ t
  ensureSort hE hΓ hts

partial def checkAgainst (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    (e t₁ : Expr ζ ℓ n) : Except Failure (PLift (E[Γ] ⊢ e : t₁)) := do
  let ⟨l, ht⟩ ← checkIsType hE hΓ t₁
  let ⟨t₂, he⟩ ← infer hE hΓ e
  let ⟨hconv⟩ ← checkTypeEq hE hΓ t₂ t₁ he.regular ⟨l, ht⟩
  pure ⟨hconv.conv he⟩

partial def isDefEqAt (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    (t e₁ e₂ : Expr ζ ℓ n) : Except Failure (PLift (E[Γ] ⊢ e₁ ≡ e₂ : t)) := do
  let ⟨l, ht⟩ ← checkIsType hE hΓ t
  let ⟨he₁⟩ ← checkAgainst hE hΓ e₁ t
  let ⟨he₂⟩ ← checkAgainst hE hΓ e₂ t
  isDefEq hE hΓ l t e₁ e₂ ht he₁ he₂

partial def checkTypeEq (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    (t t₁ : Expr ζ ℓ n) (ht : E[Γ] ⊢ t typ) (ht₁ : E[Γ] ⊢ t₁ typ) :
    Except Failure (PLift (E[Γ] ⊢ t ≡ t₁ typ)) :=
  match t.decEq? t₁ with
  | .ok ⟨he⟩ =>
    pure ⟨have ⟨_, htu⟩ := ht; he ▸ .ofDefEq htu⟩
  | .error _ =>
    match whnfType hE hΓ t ht, whnfType hE hΓ t₁ ht₁ with
    | .ok ⟨.sort l, hred⟩, .ok ⟨.sort l₁, hred₁⟩ => do
      let ⟨rfl⟩ ← guardProofOr (l = l₁) (.reject .notDefEq)
      pure ⟨hred.trans hred₁.symm⟩
    | .ok ⟨.forallE t₂ t₂', hred⟩, .ok ⟨.forallE t₃ t₃', hred₁⟩ => do
      have hinv : E[Γ] ⊢ t₂ typ ∧ E[Γ.snoc t₂] ⊢ t₂' typ :=
        have ⟨_, hpi⟩ := hred.right
        hpi.forallE_inv
      have hinv₁ : E[Γ] ⊢ t₃ typ ∧ E[Γ.snoc t₃] ⊢ t₃' typ :=
        have ⟨_, hpi⟩ := hred₁.right
        hpi.forallE_inv
      let ⟨hpi⟩ ← isForallEq hE hΓ t₂ t₃ t₂' t₃' hinv hinv₁
      pure ⟨hred.trans (hpi.trans hred₁.symm)⟩
    | _, _ => do
      let ⟨l, htl⟩ ← checkIsType hE hΓ t
      let ⟨l₁, htl₁⟩ ← checkIsType hE hΓ t₁
      let ⟨rfl⟩ ← guardProofOr (l = l₁) (.reject .notDefEq)
      let ⟨hc⟩ ← isDefEq hE hΓ (.succ l) (.sort l) t t₁
        .sortDF htl htl₁
      pure ⟨.ofDefEq hc⟩

partial def isForallEq (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) (t₁ t₂ : Expr ζ ℓ n) (t₁' t₂' : Expr ζ ℓ (n + 1))
    (ht₁ : E[Γ] ⊢ t₁ typ ∧ E[Γ.snoc t₁] ⊢ t₁' typ)
    (ht₂ : E[Γ] ⊢ t₂ typ ∧ E[Γ.snoc t₂] ⊢ t₂' typ) :
    Except Failure (PLift (E[Γ] ⊢ .forallE t₁ t₁' ≡ .forallE t₂ t₂' typ)) := do
  let ⟨hdom⟩ ← checkTypeEq hE hΓ t₁ t₂ ht₁.1 ht₂.1
  have hcod₂ : E[Γ.snoc t₁] ⊢ t₂' typ :=
    have ⟨u, hcl⟩ := ht₂.2
    ⟨u, Defeq.snocConvTy hdom.symm hcl⟩
  let ⟨hcod⟩ ← checkTypeEq hE (hΓ.snoc ht₁.1) t₁' t₂' ht₁.2 hcod₂
  pure ⟨TypeEq.forallE_congr' hE hΓ hdom hcod⟩

partial def isDefEq (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    (l : Level ℓ) (t e₁ e₂ : Expr ζ ℓ n) (ht : E[Γ] ⊢ t : .sort l)
    (he₁ : E[Γ] ⊢ e₁ : t) (he₂ : E[Γ] ⊢ e₂ : t) :
    Except Failure (PLift (E[Γ] ⊢ e₁ ≡ e₂ : t)) := do
  if let .ok ⟨heq⟩ := e₁.decEq? e₂ then return ⟨heq ▸ he₁⟩
  if hzero : l = .zero then
    return ⟨by
      subst hzero
      exact .proofIrrel ht he₁ he₂⟩
  let ⟨e₃, hstep₁⟩ ← whnf hE hΓ e₁ he₁
  let ⟨e₄, hstep₂⟩ ← whnf hE hΓ e₂ he₂
  have he₃ := hstep₁.right
  have he₄ := hstep₂.right
  let ⟨hc⟩ ←
    (do let ⟨rfl⟩ ← e₃.decEq? e₄; pure ⟨he₃⟩) <|>
    isDefEqCore hE hΓ t e₃ e₄ he₃ he₄ <|>
    isDefEqStruct hE hΓ t e₃ e₄ he₃ he₄ <|>
    isDefEqUnitLike hE hΓ t e₃ e₄ he₃ he₄
  pure ⟨hstep₁.trans (hc.trans hstep₂.symm)⟩

partial def whnf (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) (e₁ : Expr ζ ℓ n) {t : Expr ζ ℓ n}
    (he : E[Γ] ⊢ e₁ : t) :
    Except Failure {e₂ : Expr ζ ℓ n // E[Γ] ⊢ e₁ ≡ e₂ : t} := do
  let ⟨e₂, hr₁⟩ ← whnfCore E e₁
  have h₁ := WHRedS.defeq hE hΓ hr₁ he
  let .ok ⟨e₃, h₂⟩ := whnfStep hE hΓ e₂ h₁.right
    | return ⟨e₂, h₁⟩
  let ⟨e₄, hr₂⟩ ← whnfCore E e₃
  have h₃ := h₂.trans (WHRedS.defeq hE hΓ hr₂ h₂.right)
  if e₂.decEq? e₄ matches .ok _ then return ⟨e₂, h₁⟩
  let ⟨e₅, h₄⟩ ← whnf hE hΓ e₄ h₃.right
  pure ⟨e₅, h₁.trans (h₃.trans h₄)⟩

partial def whnfStep (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) {t : Expr ζ ℓ n} :
    (e₁ : Expr ζ ℓ n) → E[Γ] ⊢ e₁ : t →
    Except Failure {e₂ : Expr ζ ℓ n // E[Γ] ⊢ e₁ ≡ e₂ : t}
  | .app f₁ a => fun he => do
    let ⟨_, hf⟩ ← infer hE hΓ f₁
    let ⟨f₂, hr⟩ ← whnf hE hΓ f₁ hf
    if f₁.decEq? f₂ matches .ok _ then throw (.reject .notDefEq)
    pure ⟨.app f₂ a, (Frame.app a).plug_defeq hE hΓ (hr.retype hE hΓ) he⟩
  | .recr η s ls l ps ms mins is maj₁ => fun he =>
    kLikeStep hE hΓ (.recr η s ls l ps ms mins is maj₁) he <|> do
      let ⟨hmaj⟩ ← checkAgainst hE hΓ maj₁ (.ind η s ls ps is)
      let ⟨maj₂, hm⟩ ← whnf hE hΓ maj₁ hmaj
      let ⟨maj₃, hη⟩ ←
        (do
          if (E.get η).block.level{ls} = .zero then throw (.reject .notDefEq)
          etaStruct hE hΓ maj₂ hm.right) <|>
        pure ⟨maj₂, hm.right⟩
      if maj₁.decEq? maj₃ matches .ok _ then throw (.reject .notDefEq)
      have hmajor := hm.trans hη
      pure ⟨.recr η s ls l ps ms mins is maj₃,
        (Frame.recr η s ls l ps ms mins is).plug_defeq hE hΓ (hmajor.retype hE hΓ) he⟩
  | .quotLift η l₁ l₂ α r β f h a₁ => fun he => do
    let ⟨ha⟩ ← checkAgainst hE hΓ a₁ (.quot η l₁ α r)
    let ⟨a₂, hr⟩ ← whnf hE hΓ a₁ ha
    if a₁.decEq? a₂ matches .ok _ then throw (.reject .notDefEq)
    pure ⟨.quotLift η l₁ l₂ α r β f h a₂,
      (Frame.quotLift η l₁ l₂ α r β f h).plug_defeq hE hΓ (hr.retype hE hΓ) he⟩
  | .quotInd η l α r β f a₁ => fun he => do
    let ⟨ha⟩ ← checkAgainst hE hΓ a₁ (.quot η l α r)
    let ⟨a₂, hr⟩ ← whnf hE hΓ a₁ ha
    if a₁.decEq? a₂ matches .ok _ then throw (.reject .notDefEq)
    pure ⟨.quotInd η l α r β f a₂,
      (Frame.quotInd η l α r β f).plug_defeq hE hΓ (hr.retype hE hΓ) he⟩
  | _ => fun _ => throw (.reject .notDefEq)

partial def etaStruct (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) (e₁ : Expr ζ ℓ n) {t : Expr ζ ℓ n}
    (he : E[Γ] ⊢ e₁ : t) :
    Except Failure {e₂ : Expr ζ ℓ n // E[Γ] ⊢ e₁ ≡ e₂ : t} := do
  if e₁ matches .ctor .. then throw (.reject .notDefEq)
  let ⟨.ind (ι := ι) η s ls ps is, ht⟩ ← whnfType hE hΓ t he.regular
    | throw (.reject .notDefEq)
  let ⟨hc⟩ ← guardProofOr (ι.nctors s = 1) (.reject .notDefEq)
  let c : Fin (ι.nctors s) := ⟨0, by omega⟩
  let ⟨hs⟩ ← guardProofOr ((E.get η).block.IsStructure s c) (.reject .notDefEq)
  let ⟨hps⟩ ← Fin.sequenceM fun p =>
    checkAgainst hE hΓ (ps p) ((E.get η).block.paramType ls ps p)
  pure ⟨hs.rebuildTerm η ls ps e₁, ht.symm.conv (structure_eta hs hE hΓ hps (ht.conv he))⟩

partial def isDefEqStruct (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) (t e₁ e₂ : Expr ζ ℓ n)
    (he₁ : E[Γ] ⊢ e₁ : t) (he₂ : E[Γ] ⊢ e₂ : t) :
    Except Failure (PLift (E[Γ] ⊢ e₁ ≡ e₂ : t)) :=
  (do
    unless e₁ matches .ctor .. do throw (.reject .notDefEq)
    let ⟨e₃, hη⟩ ← etaStruct hE hΓ e₂ he₂
    let ⟨hc⟩ ← isDefEqCore hE hΓ t e₁ e₃ he₁ hη.right
    pure ⟨hc.trans hη.symm⟩) <|>
  do
    unless e₂ matches .ctor .. do throw (.reject .notDefEq)
    let ⟨e₃, hη⟩ ← etaStruct hE hΓ e₁ he₁
    let ⟨hc⟩ ← isDefEqCore hE hΓ t e₃ e₂ hη.right he₂
    pure ⟨hη.trans hc⟩

partial def isDefEqUnitLike (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) (t e₁ e₂ : Expr ζ ℓ n)
    (he₁ : E[Γ] ⊢ e₁ : t) (he₂ : E[Γ] ⊢ e₂ : t) :
    Except Failure (PLift (E[Γ] ⊢ e₁ ≡ e₂ : t)) := do
  let ⟨.ind (ι := ι) η s ls ps is, ht⟩ ← whnfType hE hΓ t he₁.regular
    | throw (.reject .notDefEq)
  let ⟨hc⟩ ← guardProofOr (ι.nctors s = 1) (.reject .notDefEq)
  let c : Fin (ι.nctors s) := ⟨0, by omega⟩
  let ⟨hs⟩ ← guardProofOr ((E.get η).block.IsStructure s c) (.reject .notDefEq)
  let ⟨hf⟩ ← guardProofOr ((ι.ctors s c).nfields = 0) (.reject .notDefEq)
  let ⟨hps⟩ ← Fin.sequenceM fun p =>
    checkAgainst hE hΓ (ps p) ((E.get η).block.paramType ls ps p)
  have hfields : IsEmpty (Fin (ι.ctors s c).nfields) := by
    rw [hf]
    infer_instance
  pure ⟨ht.symm.conv (unit_like_eta hs hfields hE hΓ hps (ht.conv he₁) (ht.conv he₂))⟩

partial def kLikeStep (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) {t : Expr ζ ℓ n} :
    (e₁ : Expr ζ ℓ n) → E[Γ] ⊢ e₁ : t →
    Except Failure {e₂ : Expr ζ ℓ n // E[Γ] ⊢ e₁ ≡ e₂ : t}
  | .recr (ι := ι) η s ls l ps ms mins is maj => fun he => do
    unless ι.nsorts = 1 do throw (.reject .notDefEq)
    let ⟨hp⟩ ← guardProofOr ((E.get η).block.level = .zero) (.reject .notDefEq)
    let ⟨hc⟩ ← guardProofOr (ι.nctors s = 1) (.reject .notDefEq)
    let c : Fin (ι.nctors s) := ⟨0, by omega⟩
    let ⟨hf⟩ ← guardProofOr ((ι.ctors s c).nfields = 0) (.reject .notDefEq)
    let ⟨hr⟩ ← guardProofOr ((ι.ctors s c).nrecFields = 0) (.reject .notDefEq)
    let fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n := fun f => by omega
    let recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n := fun f => by omega
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      checkAgainst hE hΓ (ps p) ((E.get η).block.paramType ls ps p)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      checkAgainst hE hΓ (is i) ((E.get η).block.indexType ls s ps is i)
    let ⟨hmaj⟩ ← checkAgainst hE hΓ maj (.ind η s ls ps is)
    let ⟨hctor⟩ ← checkAgainst hE hΓ
      (.ctor η s c ls ps fds recFds) (.ind η s ls ps is)
    have hprop : E[Γ] ⊢ .ind η s ls ps is : .prop := by
      have hind := Defeq.indDF hps fun i => his i
      rwa [hp] at hind
    pure ⟨_, WHRed.klike_defeq hE hΓ hprop hmaj hctor he⟩
  | _ => fun _ => throw (.reject .notDefEq)

partial def isDefEqCore (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    (t : Expr ζ ℓ n) :
    (e e₁ : Expr ζ ℓ n) → E[Γ] ⊢ e : t → E[Γ] ⊢ e₁ : t →
    Except Failure (PLift (E[Γ] ⊢ e ≡ e₁ : t))
  | .sort l₁, .sort l₂ => fun he _ => do
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    pure ⟨Defeq.retype hE hΓ .sortDF he⟩
  | .forallE t₂ t₂', .forallE t₃ t₃' => fun he he₁ => do
    let ⟨hpi⟩ ← isForallEq hE hΓ t₂ t₃ t₂' t₃' he.forallE_inv he₁.forallE_inv
    pure ⟨by
      have ⟨_, hpi⟩ := hpi.sort_uniq hE hΓ
      exact Defeq.retype hE hΓ hpi he⟩
  | .lam t₂ b, .lam t₃ b₁ => fun he he₁ => do
    have ht₂ : E[Γ] ⊢ t₂ typ :=
      have ⟨_, _, hchain⟩ := Defeq.lam_inv he hΓ
      have ⟨_, hpi⟩ := hchain.right
      hpi.forallE_inv.1
    have ht₃ : E[Γ] ⊢ t₃ typ :=
      have ⟨_, _, hchain⟩ := Defeq.lam_inv he₁ hΓ
      have ⟨_, hpi⟩ := hchain.right
      hpi.forallE_inv.1
    let ⟨hdom⟩ ← checkTypeEq hE hΓ t₂ t₃ ht₂ ht₃
    let ⟨tb, hb⟩ ← infer hE (hΓ.snoc ht₂) b
    let ⟨tb₁, hb₁⟩ ← infer hE (hΓ.snoc ht₂) b₁
    let ⟨hbt⟩ ← checkTypeEq hE (hΓ.snoc ht₂) tb₁ tb hb₁.regular hb.regular
    let ⟨lb, htb⟩ ← checkIsType hE (hΓ.snoc ht₂) tb
    let ⟨hbEq⟩ ← isDefEq hE (hΓ.snoc ht₂) lb tb b b₁ htb hb (hbt.conv hb₁)
    pure ⟨by
      have ⟨_, hdom_sort⟩ := hdom.sort_uniq hE hΓ
      exact Defeq.retype hE hΓ
        (.lamDF hdom_sort htb (hdom_sort.snocConv htb) hbEq (hdom_sort.snocConv hbEq)) he⟩
  | .lam t₂ b, e₁ => fun he _ => do
    let ⟨_, hfn⟩ ← infer hE hΓ e₁
    let ⟨t₃, t₃', hpi⟩ ← ensureForall hE hΓ hfn
    let ⟨hlam⟩ ← isDefEqAt hE hΓ (.forallE t₃ t₃') (.lam t₂ b)
      (.lam t₃ (.app e₁.wk (.var (Fin.last n))))
    pure ⟨by
      have ⟨_, htype⟩ := hpi.regular
      have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := htype.forallE_inv
      have heta := Defeq.eta ht ht' (by simpa [Expr.wk] using ht.wk t₃)
        (by simpa [Expr.wk] using hpi.wk t₃) hpi
      exact Defeq.retype hE hΓ (hlam.trans heta) he⟩
  | e, .lam t₂ b => fun he _ => do
    let ⟨_, hfn⟩ ← infer hE hΓ e
    let ⟨t₃, t₃', hpi⟩ ← ensureForall hE hΓ hfn
    let ⟨hlam⟩ ← isDefEqAt hE hΓ (.forallE t₃ t₃')
      (.lam t₃ (.app e.wk (.var (Fin.last n)))) (.lam t₂ b)
    pure ⟨by
      have ⟨_, htype⟩ := hpi.regular
      have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := htype.forallE_inv
      have heta := Defeq.eta ht ht' (by simpa [Expr.wk] using ht.wk t₃)
        (by simpa [Expr.wk] using hpi.wk t₃) hpi
      exact Defeq.retype hE hΓ (heta.symm.trans hlam) he⟩
  | .const (kind := kind) (nlevels := nlevels) η ls,
      .const (kind := kind₁) (nlevels := nlevels₁) η₁ ls₁ => fun he _ => do
    let ⟨rfl⟩ ← guardProofOr (kind = kind₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (nlevels = nlevels₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    pure ⟨he⟩
  | .ind η s ls ps is, .ind η₁ s₁ ls₁ ps₁ is₁ => fun he _ => do
    let ⟨rfl, rfl⟩ ← η.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s = s₁) (.reject .notDefEq)
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      isDefEqAt hE hΓ ((E.get η).block.paramType ls ps p) (ps p) (ps₁ p)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      isDefEqAt hE hΓ ((E.get η).block.indexType ls s ps is i) (is i) (is₁ i)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    pure ⟨Defeq.retype hE hΓ (.indDF hps fun i => his i) he⟩
  | .ctor (ι := ι) η s c ls ps fds recFds, .ctor (ι := ι₁) η₁ s₁ c₁ ls₁ ps₁ fds₁ recFds₁ => fun he _ => do
    let ⟨rfl, rfl⟩ ← η.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s = s₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (c = c₁) (.reject .notDefEq)
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      isDefEqAt hE hΓ ((E.get η).block.paramType ls ps p) (ps p) (ps₁ p)
    let ⟨hfds⟩ ← Fin.sequenceM fun f =>
      isDefEqAt hE hΓ
        (((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
        (fds f) (fds₁ f)
    let ⟨hrecFds⟩ ← Fin.sequenceM fun f =>
      isDefEqAt hE hΓ
        (((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f)
        (recFds f) (recFds₁ f)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    pure ⟨by
      have hi := (hE.entryWF η).block
      exact Defeq.retype hE hΓ
        (.ctorDF hps hfds hrecFds
          (fun f => (hi.ctors s c).ordinaryFieldExpr_congr hi.params f hps (fun g _ => hfds g))
          (fun f => ((hi.ctors s c).recursiveFieldExpr_congr hi.params rfl f hps hfds).choose_spec)
          ((hE.entryWF η).ctorType s c hps hfds)) he⟩
  | .recr η s ls l ps ms mins is maj, .recr η₁ s₁ ls₁ l₁ ps₁ ms₁ mins₁ is₁ maj₁ => fun he _ => do
    let ⟨rfl, rfl⟩ ← η.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s = s₁) (.reject .notDefEq)
    let ⟨hrec⟩ ← guardProofOr ((E.get η).block.RecAllowed l) (.reject .recursorLevel)
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      isDefEqAt hE hΓ ((E.get η).block.paramType ls ps p) (ps p) (ps₁ p)
    let ⟨hms⟩ ← Fin.sequenceM fun t =>
      isDefEqAt hE hΓ ((E.get η).block.motiveType η ls ps l t) (ms t) (ms₁ t)
    let ⟨hmins⟩ ← Fin.sequenceM fun t => Fin.sequenceM fun c =>
      isDefEqAt hE hΓ ((E.get η).block.caseFnType η ls ps ms t c)
        (mins t c) (mins₁ t c)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      isDefEqAt hE hΓ ((E.get η).block.indexType ls s ps is i) (is i) (is₁ i)
    let ⟨hmaj⟩ ← isDefEqAt hE hΓ (.ind η s ls ps is) maj maj₁
    let ⟨rfl⟩ ← guardProofOr (l = l₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    pure ⟨Defeq.retype hE hΓ
      (.recrDF hrec hps hms hmins his hmaj
        ((hE.entryWF η).block.motiveResult_congr hΓ hps hms his hmaj)) he⟩
  | .quot η l₁ α r, .quot η₁ l₂ α₁ r₁ => fun he _ => do
    let ⟨hα⟩ ← isDefEqAt hE hΓ (.sort l₁) α α₁
    let ⟨hr⟩ ← isDefEqAt hE hΓ (Quot.relType α) r r₁
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    pure ⟨Defeq.retype hE hΓ (.quotDF hα hr) he⟩
  | .quotMk η l₁ α r a, .quotMk η₁ l₂ α₁ r₁ a₁ => fun he _ => do
    let ⟨hα⟩ ← isDefEqAt hE hΓ (.sort l₁) α α₁
    let ⟨hr⟩ ← isDefEqAt hE hΓ (Quot.relType α) r r₁
    let ⟨ha⟩ ← isDefEqAt hE hΓ α a a₁
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    pure ⟨Defeq.retype hE hΓ (.quotMkDF hα hr ha) he⟩
  | .quotLift η l₁ l₂ α r β f h a, .quotLift η₁ l₁' l₂' α₁ r₁ β₁ f₁ h₁ a₁ => fun he _ => do
    let ⟨hα⟩ ← isDefEqAt hE hΓ (.sort l₁) α α₁
    let ⟨hr⟩ ← isDefEqAt hE hΓ (Quot.relType α) r r₁
    let ⟨hβ⟩ ← isDefEqAt hE hΓ (.sort l₂) β β₁
    let ⟨hf⟩ ← isDefEqAt hE hΓ (.forallE α β.wk) f f₁
    let ⟨hcompat⟩ ← isDefEqAt hE hΓ (Quot.compatType (E.get η).eqHead l₂ α r β f) h h₁
    let ⟨ha⟩ ← isDefEqAt hE hΓ (.quot η l₁ α r) a a₁
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₁') (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l₂ = l₂') (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    pure ⟨Defeq.retype hE hΓ (.quotLiftDF hα hr hβ hf hcompat ha) he⟩
  | .quotInd η l₁ α r β f a, .quotInd η₁ l₂ α₁ r₁ β₁ f₁ a₁ => fun he _ => do
    let ⟨hα⟩ ← isDefEqAt hE hΓ (.sort l₁) α α₁
    let ⟨hr⟩ ← isDefEqAt hE hΓ (Quot.relType α) r r₁
    let ⟨hβ⟩ ← isDefEqAt hE hΓ (Quot.motiveType η l₁ α r) β β₁
    let ⟨hf⟩ ← isDefEqAt hE hΓ (Quot.minorType η l₁ α r β) f f₁
    let ⟨ha⟩ ← isDefEqAt hE hΓ (.quot η l₁ α r) a a₁
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    pure ⟨Defeq.retype hE hΓ
      (.quotIndDF hα hr hβ hf ha
        (.appDF (.quotDF hα.left hr.left) .sortDF hβ ha .sortDF)) he⟩
  | .app f a, .app f₁ a₁ => fun he _ => do
    let ⟨_, hfn⟩ ← infer hE hΓ f
    let ⟨t₂, t₂', hpi⟩ ← ensureForall hE hΓ hfn
    let ⟨_, hfn₁⟩ ← infer hE hΓ f₁
    let ⟨t₃, t₃', hpi₁⟩ ← ensureForall hE hΓ hfn₁
    let ⟨hpiEq⟩ ← checkTypeEq hE hΓ (.forallE t₃ t₃') (.forallE t₂ t₂')
      hpi₁.regular hpi.regular
    let ⟨lπ, hπ⟩ ← checkIsType hE hΓ (.forallE t₂ t₂')
    let ⟨hfeq⟩ ← isDefEq hE hΓ lπ (.forallE t₂ t₂') f f₁ hπ hpi (hpiEq.conv hpi₁)
    have hinv : E[Γ] ⊢ t₂ typ ∧ E[Γ.snoc t₂] ⊢ t₂' typ :=
      have ⟨_, hty⟩ := hpi.regular
      Defeq.forallE_inv hty
    let ⟨ta, harg⟩ ← infer hE hΓ a
    let ⟨hac⟩ ← checkTypeEq hE hΓ ta t₂ harg.regular hinv.1
    let ⟨ta₁, harg₁⟩ ← infer hE hΓ a₁
    let ⟨hac₁⟩ ← checkTypeEq hE hΓ ta₁ t₂ harg₁.regular hinv.1
    let ⟨ldom, hdom⟩ ← checkIsType hE hΓ t₂
    let ⟨haeq⟩ ← isDefEq hE hΓ ldom t₂ a a₁ hdom (hac.conv harg) (hac₁.conv harg₁)
    pure ⟨by
      have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := hinv
      exact Defeq.retype hE hΓ (.appDF ht ht' hfeq haeq (ht'.inst_congr haeq)) he⟩
  | _, _ => fun _ _ => throw (.reject .notDefEq)

end

def isProp (hE : EnvWF E) (t : Expr ζ ℓ 0) : Except Failure Bool := do
  let ⟨l, _⟩ ← checkIsType hE .nil t
  pure (decide (l = .zero))

def checkAxiom (hE : EnvWF E) (t : Expr ζ ℓ 0) :
    Except Failure (PLift (EntryWF E (.axiom t))) := do
  let ⟨l, ht⟩ ← checkIsType hE .nil t
  pure ⟨.axiom ⟨l, ht⟩⟩

def checkDef (hE : EnvWF E) (t e : Expr ζ ℓ 0) :
    Except Failure (PLift (EntryWF E (.def t e))) := do
  let ⟨l, ht⟩ ← checkIsType hE .nil t
  let ⟨hvalue⟩ ← checkAgainst hE .nil e t
  pure ⟨.def ⟨l, ht⟩ hvalue⟩

def checkOpaque (hE : EnvWF E) (t e : Expr ζ ℓ 0) :
    Except Failure (PLift (EntryWF E (.opaque t))) := do
  let ⟨l, ht⟩ ← checkIsType hE .nil t
  let ⟨hvalue⟩ ← checkAgainst hE .nil e t
  pure ⟨.opaque hvalue ⟨l, ht⟩⟩

end Metalean.Checker
