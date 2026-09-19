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
public import Metalean.Strong.Substitution
public import Metalean.Strong.Telescope
public import Metalean.Metatheory.Conversion
public import Metalean.Metatheory.Injectivity
public import Metalean.Metatheory.SubjectReduction
import Metalean.Strong.Strengthen
import Metalean.Meta.IfRfl
import Metalean.Metatheory.Unique

@[expose] public section

namespace Metalean.Checker

open Frontend (Failure)

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

mutual

partial def whnfType {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (ho : E.Ordered) (hΓ : E[Γ] ⊢ₛ ok) (t₁ : Expr ζ ℓ n) (ht : E[Γ] ⊢ₛ t₁ typ) :
    Except Failure {t₂ : Expr ζ ℓ n // E[Γ] ⊢ₛ t₁ ≡ t₂ typ} := do
  let ⟨_, hty⟩ ← infer ho hΓ t₁
  let ⟨t₂, hred⟩ ← whnf ho hΓ t₁ hty
  pure ⟨t₂, have ⟨_, htu⟩ := ht; .ofDefEq (hred.retype ho hΓ htu)⟩

partial def ensureSort {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (ho : E.Ordered) (hΓ : E[Γ] ⊢ₛ ok) {e t : Expr ζ ℓ n} (hty : E[Γ] ⊢ₛ e : t) :
    Except Failure {l : Level ℓ // E[Γ] ⊢ₛ e : .sort l} := do
  let ⟨.sort l, hred⟩ ← whnfType ho hΓ t hty.regular | throw (.reject .notSort)
  pure ⟨l, hred.convStrong hty⟩

partial def ensureForall {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (ho : E.Ordered) (hΓ : E[Γ] ⊢ₛ ok) {e t : Expr ζ ℓ n} (hty : E[Γ] ⊢ₛ e : t) :
    Except Failure ((t₁ : Expr ζ ℓ n) × {t' : Expr ζ ℓ (n + 1) //
      E[Γ] ⊢ₛ e : .forallE t₁ t'}) := do
  let ⟨.forallE t₁ t', hred⟩ ← whnfType ho hΓ t hty.regular | throw (.reject .notForall)
  pure ⟨t₁, t', hred.convStrong hty⟩

partial def infer (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ₛ ok) :
    (e : Expr ζ ℓ n) → Except Failure {t : Expr ζ ℓ n // E[Γ] ⊢ₛ e : t}
  | .var v => pure ⟨Γ.get v, hΓ.var v⟩
  | .sort l => pure ⟨.sort (.succ l), .sortDF⟩
  | .const η ls =>
    pure ⟨((E.get η).constType.instL ls).wkClosed,
      have ⟨_, htype⟩ := (ho.entryWFStrong η).constType (Γ := Γ) ls
      .constDF htype⟩
  | .ind η s ls ps is => do
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      checkAgainst ho hΓ (ps p) ((E.get η).block.paramType ls ps p)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      checkAgainst ho hΓ (is i) ((E.get η).block.indexType ls s ps is i)
    pure ⟨.sort ((E.get η).block.level.inst ls),
      .indDF hps his⟩
  | .ctor η s c ls ps fds recFds => do
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      checkAgainst ho hΓ (ps p) ((E.get η).block.paramType ls ps p)
    let ⟨hfds⟩ ← Fin.sequenceM fun f =>
      checkAgainst ho hΓ (fds f)
        (((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
          (Fin.append ps fun previous : Fin f.val =>
            fds (previous.castLE f.isLt.le)))
    let ⟨hrecFds⟩ ← Fin.sequenceM fun f =>
      checkAgainst ho hΓ (recFds f)
        ((((E.get η).block.ctors s c).recursive f).instantiatedType η ls ps
          (Fin.append ps fds))
    let ⟨hfieldLevels⟩ ← Fin.sequenceM fun f =>
      (do
        let ⟨_, hty⟩ ← infer ho hΓ (((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
        let ⟨l, h⟩ ← ensureSort ho hΓ hty
        pure ⟨l, h⟩ :
        Except Failure (PLift (∃ l : Level ℓ,
          E[Γ] ⊢ₛ ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f : .sort l)))
    let ⟨hrecFieldLevels⟩ ← Fin.sequenceM fun f =>
      (do
        let ⟨_, hty⟩ ←
          infer ho hΓ (((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f)
        let ⟨l, h⟩ ← ensureSort ho hΓ hty
        pure ⟨l, h⟩ :
        Except Failure (PLift (∃ l : Level ℓ,
          E[Γ] ⊢ₛ ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f : .sort l)))
    let ⟨hind⟩ ← checkAgainst ho hΓ
      (.ind η s ls ps fun index => ((E.get η).block.ctors s c).targetIndex ls ps fds index)
      (.sort ((E.get η).block.level.inst ls))
    pure ⟨.ind η s ls ps fun index => ((E.get η).block.ctors s c).targetIndex ls ps fds index,
      .ctorDF (fieldLevels := fun f => (hfieldLevels f).choose)
        (recFieldLevels := fun f => (hrecFieldLevels f).choose) hps hfds
        hrecFds (fun f => (hfieldLevels f).choose_spec)
        (fun f => (hrecFieldLevels f).choose_spec) hind⟩
  | .recr η s ls l ps ms mins is maj => do
    let ⟨hrec⟩ ← guardProofOr ((E.get η).block.RecAllowed l) (.reject .recursorLevel)
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      checkAgainst ho hΓ (ps p) ((E.get η).block.paramType ls ps p)
    let ⟨hms⟩ ← Fin.sequenceM fun t =>
      checkAgainst ho hΓ (ms t) ((E.get η).block.motiveType η ls ps l t)
    let ⟨hmins⟩ ← Fin.sequenceM fun t => Fin.sequenceM fun c =>
      checkAgainst ho hΓ (mins t c) ((E.get η).block.caseFnType η ls ps ms t c)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      checkAgainst ho hΓ (is i) ((E.get η).block.indexType ls s ps is i)
    let ⟨hmaj⟩ ← checkAgainst ho hΓ maj (.ind η s ls ps is)
    let ⟨hres⟩ ← checkAgainst ho hΓ (Inductive.motiveResult (ms s) is maj) (.sort l)
    pure ⟨Inductive.motiveResult (ms s) is maj,
      .recrDF hrec hps
        hms hmins his
        hmaj hres⟩
  | .quot _ l α r => do
    let ⟨hα⟩ ← checkAgainst ho hΓ α (.sort l)
    let ⟨hr⟩ ← checkAgainst ho hΓ r (Quot.relType α)
    pure ⟨.sort l, .quotDF hα hr⟩
  | .quotMk η l α r e => do
    let ⟨hα⟩ ← checkAgainst ho hΓ α (.sort l)
    let ⟨hr⟩ ← checkAgainst ho hΓ r (Quot.relType α)
    let ⟨he⟩ ← checkAgainst ho hΓ e α
    pure ⟨.quot η l α r, .quotMkDF hα hr he⟩
  | .quotLift η l₁ l₂ α r β f h a => do
    let ⟨hα⟩ ← checkAgainst ho hΓ α (.sort l₁)
    let ⟨hr⟩ ← checkAgainst ho hΓ r (Quot.relType α)
    let ⟨hβ⟩ ← checkAgainst ho hΓ β (.sort l₂)
    let ⟨hf⟩ ← checkAgainst ho hΓ f (.forallE α β.wk)
    let ⟨hcompat⟩ ← checkAgainst ho hΓ h (Quot.compatType (E.get η).eqHead l₂ α r β f)
    let ⟨ha⟩ ← checkAgainst ho hΓ a (.quot η l₁ α r)
    pure ⟨β, .quotLiftDF hα hr hβ hf hcompat ha⟩
  | .quotInd η l α r β f e => do
    let ⟨hα⟩ ← checkAgainst ho hΓ α (.sort l)
    let ⟨hr⟩ ← checkAgainst ho hΓ r (Quot.relType α)
    let ⟨hβ⟩ ← checkAgainst ho hΓ β (Quot.motiveType η l α r)
    let ⟨hf⟩ ← checkAgainst ho hΓ f (Quot.minorType η l α r β)
    let ⟨he⟩ ← checkAgainst ho hΓ e (.quot η l α r)
    let ⟨happ⟩ ← checkAgainst ho hΓ (.app β e) .prop
    pure ⟨.app β e, .quotIndDF hα hr hβ hf he happ⟩
  | .app e e₁ => do
    let ⟨_, hfn⟩ ← infer ho hΓ e
    let ⟨t, t', hpi⟩ ← ensureForall ho hΓ hfn
    let ⟨t₁, harg⟩ ← infer ho hΓ e₁
    have hinv : E[Γ] ⊢ₛ t typ ∧ E[Γ.snoc t] ⊢ₛ t' typ :=
      have ⟨_, hty⟩ := hpi.regular
      hty.forallE_inv
    let ⟨hconv⟩ ← isTypeEq ho hΓ t₁ t harg.regular hinv.1
    pure ⟨t'.inst e₁,
      have harg₁ := hconv.convStrong harg
      have ⟨_, ht⟩ := hinv.1
      have ⟨_, ht'⟩ := hinv.2
      .appDF ht ht' hpi harg₁ (ht'.inst_congr harg₁)⟩
  | .lam t e' => do
    let ⟨_, ht₁⟩ ← infer ho hΓ t
    let ⟨l, ht⟩ ← ensureSort ho hΓ ht₁
    let ⟨t', he'⟩ ← infer ho (hΓ.snoc ⟨l, ht⟩) e'
    pure ⟨.forallE t t',
      have ⟨_, ht'⟩ := he'.regular
      .lamDF ht ht' ht' he' he'⟩
  | .forallE t t' => do
    let ⟨_, ht₁⟩ ← infer ho hΓ t
    let ⟨l, ht⟩ ← ensureSort ho hΓ ht₁
    let ⟨_, ht₂⟩ ← infer ho (hΓ.snoc ⟨l, ht⟩) t'
    let ⟨l₁, ht'⟩ ← ensureSort ho (hΓ.snoc ⟨l, ht⟩) ht₂
    pure ⟨.sort (.imax l l₁), .forallEDF ht ht' ht'⟩
  | .letE t v e' => do
    let ⟨_, ht₁⟩ ← infer ho hΓ t
    let ⟨_, ht⟩ ← ensureSort ho hΓ ht₁
    let ⟨hv⟩ ← checkAgainst ho hΓ v t
    let ⟨r, hb⟩ ← infer ho hΓ (e'.inst v)
    pure ⟨r,
      have ⟨_, hr⟩ := hb.regular
      (DefeqStrong.zeta ht hv hr hb).left⟩

partial def checkAgainst (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ₛ ok)
    (e t₁ : Expr ζ ℓ n) : Except Failure (PLift (E[Γ] ⊢ₛ e : t₁)) := do
  let ⟨_, hts⟩ ← infer ho hΓ t₁
  let ⟨l, ht⟩ ← ensureSort ho hΓ hts
  let ⟨t₂, he⟩ ← infer ho hΓ e
  let ⟨hconv⟩ ← isTypeEq ho hΓ t₂ t₁ he.regular ⟨l, ht⟩
  pure ⟨hconv.convStrong he⟩

partial def isDefEqAt (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ₛ ok)
    (t e₁ e₂ : Expr ζ ℓ n) : Except Failure (PLift (E[Γ] ⊢ₛ e₁ ≡ e₂ : t)) := do
  let ⟨_, hts⟩ ← infer ho hΓ t
  let ⟨l, ht⟩ ← ensureSort ho hΓ hts
  let ⟨he₁⟩ ← checkAgainst ho hΓ e₁ t
  let ⟨he₂⟩ ← checkAgainst ho hΓ e₂ t
  isDefEq ho hΓ l t e₁ e₂ ht he₁ he₂

partial def isTypeEq (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ₛ ok)
    (t t₁ : Expr ζ ℓ n) (ht : E[Γ] ⊢ₛ t typ) (ht₁ : E[Γ] ⊢ₛ t₁ typ) :
    Except Failure (PLift (E[Γ] ⊢ₛ t ≡ t₁ typ)) :=
  match t.decEq? t₁ with
  | .ok ⟨he⟩ =>
    pure ⟨have ⟨_, htu⟩ := ht; he ▸ .ofDefEq htu⟩
  | .error _ =>
    match whnfType ho hΓ t ht, whnfType ho hΓ t₁ ht₁ with
    | .ok ⟨.sort l, hred⟩, .ok ⟨.sort l₁, hred₁⟩ => do
      let ⟨rfl⟩ ← guardProofOr (l = l₁) (.reject .notDefEq)
      pure ⟨hred.trans hred₁.symm⟩
    | .ok ⟨.forallE t₂ t₂', hred⟩, .ok ⟨.forallE t₃ t₃', hred₁⟩ => do
      have hinv : E[Γ] ⊢ₛ t₂ typ ∧ E[Γ.snoc t₂] ⊢ₛ t₂' typ :=
        have ⟨_, hpi⟩ := hred.isType.2
        hpi.forallE_inv
      have hinv₁ : E[Γ] ⊢ₛ t₃ typ ∧ E[Γ.snoc t₃] ⊢ₛ t₃' typ :=
        have ⟨_, hpi⟩ := hred₁.isType.2
        hpi.forallE_inv
      let ⟨hdom⟩ ← isTypeEq ho hΓ t₂ t₃ hinv.1 hinv₁.1
      have hcod₁ : E[Γ.snoc t₂] ⊢ₛ t₃' typ :=
        have ⟨u, hcl⟩ := hinv₁.2
        ⟨u, ((hdom.symm.snocConv ho hΓ).mp hcl.defeq).toStrongOrdered ho
          (hΓ.snoc hinv.1)⟩
      let ⟨hcod⟩ ← isTypeEq ho (hΓ.snoc hinv.1) t₂' t₃' hinv.2 hcod₁
      pure ⟨hred.trans ((IsTypeEq.forallE_congr' ho hΓ hdom hcod).trans hred₁.symm)⟩
    | _, _ => do
      let ⟨_, hts⟩ ← infer ho hΓ t
      let ⟨l, htl⟩ ← ensureSort ho hΓ hts
      let ⟨_, hts₁⟩ ← infer ho hΓ t₁
      let ⟨l₁, htl₁⟩ ← ensureSort ho hΓ hts₁
      let ⟨rfl⟩ ← guardProofOr (l = l₁) (.reject .notDefEq)
      let ⟨hc⟩ ← isDefEq ho hΓ (.succ l) (.sort l) t t₁
        .sortDF htl htl₁
      pure ⟨.ofDefEq hc⟩

partial def isDefEq (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ₛ ok)
    (l : Level ℓ) (t e₁ e₂ : Expr ζ ℓ n) (ht : E[Γ] ⊢ₛ t : .sort l)
    (he₁ : E[Γ] ⊢ₛ e₁ : t) (he₂ : E[Γ] ⊢ₛ e₂ : t) :
    Except Failure (PLift (E[Γ] ⊢ₛ e₁ ≡ e₂ : t)) := do
  if let .ok ⟨heq⟩ := e₁.decEq? e₂ then return ⟨heq ▸ he₁⟩
  if hzero : l = .zero then
    return ⟨by
      subst hzero
      exact .proofIrrel ht he₁ he₂⟩
  let ⟨e₃, hstep₁⟩ ← whnf ho hΓ e₁ he₁
  let ⟨e₄, hstep₂⟩ ← whnf ho hΓ e₂ he₂
  have he₃ := hstep₁.right
  have he₄ := hstep₂.right
  let ⟨hc⟩ ←
    (do let ⟨rfl⟩ ← e₃.decEq? e₄; pure ⟨he₃⟩) <|>
    isDefEqCore ho hΓ t e₃ e₄ he₃ he₄ <|>
    isDefEqStruct ho hΓ t e₃ e₄ he₃ he₄ <|>
    isDefEqUnitLike ho hΓ t e₃ e₄ he₃ he₄
  pure ⟨hstep₁.trans (hc.trans hstep₂.symm)⟩

partial def whnf (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ₛ ok) (e₁ : Expr ζ ℓ n) {t : Expr ζ ℓ n}
    (he : E[Γ] ⊢ₛ e₁ : t) :
    Except Failure {e₂ : Expr ζ ℓ n // E[Γ] ⊢ₛ e₁ ≡ e₂ : t} := do
  let ⟨e₂, hr₁⟩ ← whnfCore E e₁
  have h₁ := WHRedS.defeq ho hΓ hr₁ he
  let .ok ⟨e₃, h₂⟩ := whnfStep ho hΓ e₂ h₁.right
    | return ⟨e₂, h₁⟩
  let ⟨e₄, hr₂⟩ ← whnfCore E e₃
  have h₃ := h₂.trans (WHRedS.defeq ho hΓ hr₂ h₂.right)
  if e₂.decEq? e₄ matches .ok _ then return ⟨e₂, h₁⟩
  let ⟨e₅, h₄⟩ ← whnf ho hΓ e₄ h₃.right
  pure ⟨e₅, h₁.trans (h₃.trans h₄)⟩

partial def whnfStep (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ₛ ok) {t : Expr ζ ℓ n} :
    (e₁ : Expr ζ ℓ n) → E[Γ] ⊢ₛ e₁ : t →
    Except Failure {e₂ : Expr ζ ℓ n // E[Γ] ⊢ₛ e₁ ≡ e₂ : t}
  | .app f₁ a => fun he => do
    let ⟨_, hf⟩ ← infer ho hΓ f₁
    let ⟨f₂, hr⟩ ← whnf ho hΓ f₁ hf
    if f₁.decEq? f₂ matches .ok _ then throw (.reject .notDefEq)
    pure ⟨.app f₂ a, (Frame.app a).plug_defeq ho hΓ (hr.retype ho hΓ) he⟩
  | .recr η s ls l ps ms mins is maj₁ => fun he =>
    kLikeStep ho hΓ (.recr η s ls l ps ms mins is maj₁) he <|> do
      let ⟨hmaj⟩ ← checkAgainst ho hΓ maj₁ (.ind η s ls ps is)
      let ⟨maj₂, hm⟩ ← whnf ho hΓ maj₁ hmaj
      let ⟨maj₃, hη⟩ ←
        (do
          if (E.get η).block.level.inst ls = .zero then throw (.reject .notDefEq)
          etaStruct ho hΓ maj₂ hm.right) <|>
        pure ⟨maj₂, hm.right⟩
      if maj₁.decEq? maj₃ matches .ok _ then throw (.reject .notDefEq)
      have hmajor := hm.trans hη
      pure ⟨.recr η s ls l ps ms mins is maj₃,
        (Frame.recr η s ls l ps ms mins is).plug_defeq ho hΓ (hmajor.retype ho hΓ) he⟩
  | .quotLift η l₁ l₂ α r β f h a₁ => fun he => do
    let ⟨ha⟩ ← checkAgainst ho hΓ a₁ (.quot η l₁ α r)
    let ⟨a₂, hr⟩ ← whnf ho hΓ a₁ ha
    if a₁.decEq? a₂ matches .ok _ then throw (.reject .notDefEq)
    pure ⟨.quotLift η l₁ l₂ α r β f h a₂,
      (Frame.quotLift η l₁ l₂ α r β f h).plug_defeq ho hΓ (hr.retype ho hΓ) he⟩
  | .quotInd η l α r β f a₁ => fun he => do
    let ⟨ha⟩ ← checkAgainst ho hΓ a₁ (.quot η l α r)
    let ⟨a₂, hr⟩ ← whnf ho hΓ a₁ ha
    if a₁.decEq? a₂ matches .ok _ then throw (.reject .notDefEq)
    pure ⟨.quotInd η l α r β f a₂,
      (Frame.quotInd η l α r β f).plug_defeq ho hΓ (hr.retype ho hΓ) he⟩
  | _ => fun _ => throw (.reject .notDefEq)

partial def etaStruct (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ₛ ok) (e₁ : Expr ζ ℓ n) {t : Expr ζ ℓ n}
    (he : E[Γ] ⊢ₛ e₁ : t) :
    Except Failure {e₂ : Expr ζ ℓ n // E[Γ] ⊢ₛ e₁ ≡ e₂ : t} := do
  if e₁ matches .ctor .. then throw (.reject .notDefEq)
  let ⟨.ind (ι := ι) η s ls ps is, ht⟩ ← whnfType ho hΓ t he.regular
    | throw (.reject .notDefEq)
  let ⟨hc⟩ ← guardProofOr (ι.nctors s = 1) (.reject .notDefEq)
  let c : Fin (ι.nctors s) := ⟨0, by omega⟩
  let ⟨hs⟩ ← guardProofOr ((E.get η).block.IsStructure s c) (.reject .notDefEq)
  let ⟨hps⟩ ← Fin.sequenceM fun p =>
    checkAgainst ho hΓ (ps p) ((E.get η).block.paramType ls ps p)
  pure ⟨hs.rebuildTerm η ls ps e₁, ht.symm.convStrong
    (structure_eta ho hs hΓ hps (ht.convStrong he))⟩

partial def isDefEqStruct (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ₛ ok) (t e₁ e₂ : Expr ζ ℓ n)
    (he₁ : E[Γ] ⊢ₛ e₁ : t) (he₂ : E[Γ] ⊢ₛ e₂ : t) :
    Except Failure (PLift (E[Γ] ⊢ₛ e₁ ≡ e₂ : t)) :=
  (do
    unless e₁ matches .ctor .. do throw (.reject .notDefEq)
    let ⟨e₃, hη⟩ ← etaStruct ho hΓ e₂ he₂
    let ⟨hc⟩ ← isDefEqCore ho hΓ t e₁ e₃ he₁ hη.right
    pure ⟨hc.trans hη.symm⟩) <|>
  do
    unless e₂ matches .ctor .. do throw (.reject .notDefEq)
    let ⟨e₃, hη⟩ ← etaStruct ho hΓ e₁ he₁
    let ⟨hc⟩ ← isDefEqCore ho hΓ t e₃ e₂ hη.right he₂
    pure ⟨hη.trans hc⟩

partial def isDefEqUnitLike (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ₛ ok) (t e₁ e₂ : Expr ζ ℓ n)
    (he₁ : E[Γ] ⊢ₛ e₁ : t) (he₂ : E[Γ] ⊢ₛ e₂ : t) :
    Except Failure (PLift (E[Γ] ⊢ₛ e₁ ≡ e₂ : t)) := do
  let ⟨.ind (ι := ι) η s ls ps is, ht⟩ ← whnfType ho hΓ t he₁.regular
    | throw (.reject .notDefEq)
  let ⟨hc⟩ ← guardProofOr (ι.nctors s = 1) (.reject .notDefEq)
  let c : Fin (ι.nctors s) := ⟨0, by omega⟩
  let ⟨hs⟩ ← guardProofOr ((E.get η).block.IsStructure s c) (.reject .notDefEq)
  let ⟨hf⟩ ← guardProofOr ((ι.ctors s c).nfields = 0) (.reject .notDefEq)
  let ⟨hps⟩ ← Fin.sequenceM fun p =>
    checkAgainst ho hΓ (ps p) ((E.get η).block.paramType ls ps p)
  have hfields : IsEmpty (Fin (ι.ctors s c).nfields) := by
    rw [hf]
    infer_instance
  pure ⟨ht.symm.convStrong (unit_like_eta ho hs hfields hΓ
    hps (ht.convStrong he₁) (ht.convStrong he₂))⟩

partial def kLikeStep (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ₛ ok) {t : Expr ζ ℓ n} :
    (e₁ : Expr ζ ℓ n) → E[Γ] ⊢ₛ e₁ : t →
    Except Failure {e₂ : Expr ζ ℓ n // E[Γ] ⊢ₛ e₁ ≡ e₂ : t}
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
      checkAgainst ho hΓ (ps p) ((E.get η).block.paramType ls ps p)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      checkAgainst ho hΓ (is i) ((E.get η).block.indexType ls s ps is i)
    let ⟨hmaj⟩ ← checkAgainst ho hΓ maj (.ind η s ls ps is)
    let ⟨hctor⟩ ← checkAgainst ho hΓ
      (.ctor η s c ls ps fds recFds) (.ind η s ls ps is)
    have hprop : E[Γ] ⊢ₛ .ind η s ls ps is : .prop := by
      have hind := DefeqStrong.indDF hps fun i => his i
      rwa [hp] at hind
    pure ⟨_, WHRed.klike_defeq ho hΓ hprop hmaj hctor he⟩
  | _ => fun _ => throw (.reject .notDefEq)

partial def isDefEqCore (ho : E.Ordered) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ₛ ok)
    (t : Expr ζ ℓ n) :
    (e e₁ : Expr ζ ℓ n) → E[Γ] ⊢ₛ e : t → E[Γ] ⊢ₛ e₁ : t →
    Except Failure (PLift (E[Γ] ⊢ₛ e ≡ e₁ : t))
  | .sort l₁, .sort l₂ => fun he _ => do
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    pure ⟨DefeqStrong.retype ho hΓ .sortDF he⟩
  | .forallE t₂ t₂', .forallE t₃ t₃' => fun he he₁ => do
    have hinv := he.forallE_inv
    have hinv₁ := he₁.forallE_inv
    let ⟨hdom⟩ ← isTypeEq ho hΓ t₂ t₃ hinv.1 hinv₁.1
    have hcod₁ : E[Γ.snoc t₂] ⊢ₛ t₃' typ :=
      have ⟨u, hcl⟩ := hinv₁.2
      ⟨u, ((hdom.symm.snocConv ho hΓ).1 hcl.defeq).toStrongOrdered ho
        (hΓ.snoc hinv.1)⟩
    let ⟨hcod⟩ ← isTypeEq ho (hΓ.snoc hinv.1) t₂' t₃' hinv.2 hcod₁
    pure ⟨by
      have ⟨_, hpi⟩ := (hdom.forallE_congr' ho hΓ hcod).sort_uniq ho hΓ
      exact DefeqStrong.retype ho hΓ hpi he⟩
  | .lam t₂ b, .lam t₃ b₁ => fun he he₁ => do
    have ht₂ : E[Γ] ⊢ₛ t₂ typ :=
      have ⟨_, _, hchain⟩ := DefeqStrong.lam_inv he hΓ
      have ⟨_, hpi⟩ := hchain.isType.2
      hpi.forallE_inv.1
    have ht₃ : E[Γ] ⊢ₛ t₃ typ :=
      have ⟨_, _, hchain⟩ := DefeqStrong.lam_inv he₁ hΓ
      have ⟨_, hpi⟩ := hchain.isType.2
      hpi.forallE_inv.1
    let ⟨hdom⟩ ← isTypeEq ho hΓ t₂ t₃ ht₂ ht₃
    let ⟨tb, hb⟩ ← infer ho (hΓ.snoc ht₂) b
    let ⟨tb₁, hb₁⟩ ← infer ho (hΓ.snoc ht₂) b₁
    let ⟨hbt⟩ ← isTypeEq ho (hΓ.snoc ht₂) tb₁ tb hb₁.regular hb.regular
    let ⟨_, htbty⟩ ← infer ho (hΓ.snoc ht₂) tb
    let ⟨lb, htb⟩ ← ensureSort ho (hΓ.snoc ht₂) htbty
    let ⟨hbEq⟩ ← isDefEq ho (hΓ.snoc ht₂) lb tb b b₁ htb hb (hbt.convStrong hb₁)
    pure ⟨by
      have ⟨_, hdomStrong⟩ := hdom.sort_uniq ho hΓ
      have ⟨_, htbl⟩ := hb.regular
      have htbl₁ := ((hdom.snocConv ho hΓ).mp htbl.defeq).toStrongOrdered ho (hΓ.snoc ht₃)
      have hbEq₁ := ((hdom.snocConv ho hΓ).mp hbEq.defeq).toStrongOrdered ho (hΓ.snoc ht₃)
      exact DefeqStrong.retype ho hΓ (.lamDF hdomStrong htbl htbl₁ hbEq hbEq₁) he⟩
  | .lam t₂ b, e₁ => fun he _ => do
    let ⟨_, hfn⟩ ← infer ho hΓ e₁
    let ⟨t₃, t₃', hpi⟩ ← ensureForall ho hΓ hfn
    have hinv : E[Γ] ⊢ₛ t₃ typ ∧ E[Γ.snoc t₃] ⊢ₛ t₃' typ :=
      have ⟨_, hty⟩ := hpi.regular
      hty.forallE_inv
    have heta : E[Γ] ⊢ₛ .lam t₃ (.app e₁.wk (.var (Fin.last n))) ≡ e₁ : .forallE t₃ t₃' :=
      have ⟨_, ht₃⟩ := hinv.1
      have ⟨_, ht₃'⟩ := hinv.2
      .eta ht₃ ht₃' (by simpa [Expr.wk] using ht₃.wk t₃)
        (by simpa [Expr.wk] using hpi.wk t₃) hpi
    let ⟨hlam⟩ ← isDefEqAt ho hΓ (.forallE t₃ t₃') (.lam t₂ b)
      (.lam t₃ (.app e₁.wk (.var (Fin.last n))))
    pure ⟨DefeqStrong.retype ho hΓ (hlam.trans heta) he⟩
  | e, .lam t₂ b => fun he _ => do
    let ⟨_, hfn⟩ ← infer ho hΓ e
    let ⟨t₃, t₃', hpi⟩ ← ensureForall ho hΓ hfn
    have hinv : E[Γ] ⊢ₛ t₃ typ ∧ E[Γ.snoc t₃] ⊢ₛ t₃' typ :=
      have ⟨_, hty⟩ := hpi.regular
      hty.forallE_inv
    have heta : E[Γ] ⊢ₛ .lam t₃ (.app e.wk (.var (Fin.last n))) ≡ e : .forallE t₃ t₃' :=
      have ⟨_, ht₃⟩ := hinv.1
      have ⟨_, ht₃'⟩ := hinv.2
      .eta ht₃ ht₃' (by simpa [Expr.wk] using ht₃.wk t₃)
        (by simpa [Expr.wk] using hpi.wk t₃) hpi
    let ⟨hlam⟩ ← isDefEqAt ho hΓ (.forallE t₃ t₃')
      (.lam t₃ (.app e.wk (.var (Fin.last n)))) (.lam t₂ b)
    pure ⟨DefeqStrong.retype ho hΓ (heta.symm.trans hlam) he⟩
  | .const (kind := kind) (nlevels := nlevels) η ls,
      .const (kind := kind₁) (nlevels := nlevels₁) η₁ ls₁ => fun he _ => do
    let ⟨rfl⟩ ← guardProofOr (kind = kind₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (nlevels = nlevels₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    let ⟨_, htype⟩ ← infer ho hΓ ((E.get η).constType.instL ls).wkClosed
    let ⟨_, hty⟩ ← ensureSort ho hΓ htype
    pure ⟨DefeqStrong.retype ho hΓ (.constDF hty) he⟩
  | .ind η s ls ps is, .ind η₁ s₁ ls₁ ps₁ is₁ => fun he _ => do
    let ⟨rfl, rfl⟩ ← η.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s = s₁) (.reject .notDefEq)
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      isDefEqAt ho hΓ ((E.get η).block.paramType ls ps p) (ps p) (ps₁ p)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      isDefEqAt ho hΓ ((E.get η).block.indexType ls s ps is i) (is i) (is₁ i)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    pure ⟨DefeqStrong.retype ho hΓ
      (.indDF hps fun i => his i) he⟩
  | .ctor (ι := ι) η s c ls ps fds recFds, .ctor (ι := ι₁) η₁ s₁ c₁ ls₁ ps₁ fds₁ recFds₁ => fun he _ => do
    let ⟨rfl, rfl⟩ ← η.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s = s₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (c = c₁) (.reject .notDefEq)
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      isDefEqAt ho hΓ ((E.get η).block.paramType ls ps p) (ps p) (ps₁ p)
    let ⟨hfds⟩ ← Fin.sequenceM fun f =>
      isDefEqAt ho hΓ
        (((((E.get η).block.ctors s c).ordinaryType f).instL ls).subst
          (Fin.append ps fun previous : Fin f.val =>
            fds (previous.castLE f.isLt.le)))
        (fds f) (fds₁ f)
    let ⟨hrecFds⟩ ← Fin.sequenceM fun f =>
      isDefEqAt ho hΓ
        ((((E.get η).block.ctors s c).recursive f).instantiatedType η ls ps
          (Fin.append ps fds))
        (recFds f) (recFds₁ f)
    let ⟨hfieldLevels⟩ ← Fin.sequenceM fun f => do
      let ⟨_, hty⟩ ←
        infer ho hΓ (((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
      let ⟨l, _⟩ ← ensureSort ho hΓ hty
      let ⟨hd⟩ ← isDefEqAt ho hΓ (.sort l)
        (((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
        (((E.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f)
      pure (⟨l, hd⟩ : PLift (∃ l : Level ℓ,
        E[Γ] ⊢ₛ ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f ≡
          ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds₁ f :
          .sort l))
    let ⟨hrecFieldLevels⟩ ← Fin.sequenceM fun f => do
      let ⟨_, hty⟩ ←
        infer ho hΓ
          (((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f)
      let ⟨l, _⟩ ← ensureSort ho hΓ hty
      let ⟨hd⟩ ← isDefEqAt ho hΓ (.sort l)
        (((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f)
        (((E.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f)
      pure (⟨l, hd⟩ : PLift (∃ l : Level ℓ,
        E[Γ] ⊢ₛ ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f ≡
          ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds₁ f :
          .sort l))
    let ⟨hind⟩ ← isDefEqAt ho hΓ (.sort ((E.get η).block.level.inst ls))
      (.ind η s ls ps fun index =>
        ((E.get η).block.ctors s c).targetIndex ls ps fds index)
      (.ind η s ls ps₁ fun index =>
        ((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁ index)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    pure ⟨DefeqStrong.retype ho hΓ
      (.ctorDF (fieldLevels := fun f => (hfieldLevels f).choose)
        (recFieldLevels := fun f => (hrecFieldLevels f).choose) hps hfds
        hrecFds (fun f => (hfieldLevels f).choose_spec)
        (fun f => (hrecFieldLevels f).choose_spec) hind) he⟩
  | .recr η s ls l ps ms mins is maj, .recr η₁ s₁ ls₁ l₁ ps₁ ms₁ mins₁ is₁ maj₁ => fun he _ => do
    let ⟨rfl, rfl⟩ ← η.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s = s₁) (.reject .notDefEq)
    let ⟨hrec⟩ ← guardProofOr ((E.get η).block.RecAllowed l) (.reject .recursorLevel)
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      isDefEqAt ho hΓ ((E.get η).block.paramType ls ps p) (ps p) (ps₁ p)
    let ⟨hms⟩ ← Fin.sequenceM fun t =>
      isDefEqAt ho hΓ ((E.get η).block.motiveType η ls ps l t) (ms t) (ms₁ t)
    let ⟨hmins⟩ ← Fin.sequenceM fun t => Fin.sequenceM fun c =>
      isDefEqAt ho hΓ ((E.get η).block.caseFnType η ls ps ms t c)
        (mins t c) (mins₁ t c)
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      isDefEqAt ho hΓ ((E.get η).block.indexType ls s ps is i) (is i) (is₁ i)
    let ⟨hmaj⟩ ← isDefEqAt ho hΓ (.ind η s ls ps is) maj maj₁
    let ⟨hres⟩ ← isDefEqAt ho hΓ (.sort l)
      (Inductive.motiveResult (ms s) is maj)
      (Inductive.motiveResult (ms₁ s) is₁ maj₁)
    let ⟨rfl⟩ ← guardProofOr (l = l₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    pure ⟨DefeqStrong.retype ho hΓ
      (.recrDF hrec hps hms
        hmins his hmaj hres) he⟩
  | .quot η l₁ α r, .quot η₁ l₂ α₁ r₁ => fun he _ => do
    let ⟨hα⟩ ← isDefEqAt ho hΓ (.sort l₁) α α₁
    let ⟨hr⟩ ← isDefEqAt ho hΓ (Quot.relType α) r r₁
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    pure ⟨DefeqStrong.retype ho hΓ (.quotDF hα hr) he⟩
  | .quotMk η l₁ α r a, .quotMk η₁ l₂ α₁ r₁ a₁ => fun he _ => do
    let ⟨hα⟩ ← isDefEqAt ho hΓ (.sort l₁) α α₁
    let ⟨hr⟩ ← isDefEqAt ho hΓ (Quot.relType α) r r₁
    let ⟨ha⟩ ← isDefEqAt ho hΓ α a a₁
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    pure ⟨DefeqStrong.retype ho hΓ (.quotMkDF hα hr ha) he⟩
  | .quotLift η l₁ l₂ α r β f h a, .quotLift η₁ l₁' l₂' α₁ r₁ β₁ f₁ h₁ a₁ => fun he _ => do
    let ⟨hα⟩ ← isDefEqAt ho hΓ (.sort l₁) α α₁
    let ⟨hr⟩ ← isDefEqAt ho hΓ (Quot.relType α) r r₁
    let ⟨hβ⟩ ← isDefEqAt ho hΓ (.sort l₂) β β₁
    let ⟨hf⟩ ← isDefEqAt ho hΓ (.forallE α β.wk) f f₁
    let ⟨hcompat⟩ ← isDefEqAt ho hΓ (Quot.compatType (E.get η).eqHead l₂ α r β f) h h₁
    let ⟨ha⟩ ← isDefEqAt ho hΓ (.quot η l₁ α r) a a₁
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₁') (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l₂ = l₂') (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    pure ⟨DefeqStrong.retype ho hΓ
      (.quotLiftDF hα hr hβ hf hcompat ha) he⟩
  | .quotInd η l₁ α r β f a, .quotInd η₁ l₂ α₁ r₁ β₁ f₁ a₁ => fun he _ => do
    let ⟨hα⟩ ← isDefEqAt ho hΓ (.sort l₁) α α₁
    let ⟨hr⟩ ← isDefEqAt ho hΓ (Quot.relType α) r r₁
    let ⟨hβ⟩ ← isDefEqAt ho hΓ (Quot.motiveType η l₁ α r) β β₁
    let ⟨hf⟩ ← isDefEqAt ho hΓ (Quot.minorType η l₁ α r β) f f₁
    let ⟨ha⟩ ← isDefEqAt ho hΓ (.quot η l₁ α r) a a₁
    let ⟨happ⟩ ← isDefEqAt ho hΓ .prop (.app β a) (.app β₁ a₁)
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    pure ⟨DefeqStrong.retype ho hΓ (.quotIndDF hα hr hβ hf ha happ) he⟩
  | .app f a, .app f₁ a₁ => fun he _ => do
    let ⟨_, hfn⟩ ← infer ho hΓ f
    let ⟨t₂, t₂', hpi⟩ ← ensureForall ho hΓ hfn
    let ⟨_, hfn₁⟩ ← infer ho hΓ f₁
    let ⟨t₃, t₃', hpi₁⟩ ← ensureForall ho hΓ hfn₁
    let ⟨hpiEq⟩ ← isTypeEq ho hΓ (.forallE t₃ t₃') (.forallE t₂ t₂')
      hpi₁.regular hpi.regular
    let ⟨_, hπty⟩ ← infer ho hΓ (.forallE t₂ t₂')
    let ⟨lπ, hπ⟩ ← ensureSort ho hΓ hπty
    let ⟨hfeq⟩ ← isDefEq ho hΓ lπ (.forallE t₂ t₂') f f₁ hπ hpi (hpiEq.convStrong hpi₁)
    have hinv : E[Γ] ⊢ₛ t₂ typ ∧ E[Γ.snoc t₂] ⊢ₛ t₂' typ :=
      have ⟨_, hty⟩ := hpi.regular
      DefeqStrong.forallE_inv hty
    let ⟨ta, harg⟩ ← infer ho hΓ a
    let ⟨hac⟩ ← isTypeEq ho hΓ ta t₂ harg.regular hinv.1
    let ⟨ta₁, harg₁⟩ ← infer ho hΓ a₁
    let ⟨hac₁⟩ ← isTypeEq ho hΓ ta₁ t₂ harg₁.regular hinv.1
    let ⟨_, hdomty⟩ ← infer ho hΓ t₂
    let ⟨ldom, hdom⟩ ← ensureSort ho hΓ hdomty
    let ⟨haeq⟩ ← isDefEq ho hΓ ldom t₂ a a₁ hdom
      (hac.convStrong harg) (hac₁.convStrong harg₁)
    pure ⟨
      have ⟨⟨_, ht₂⟩, ⟨_, ht₂'⟩⟩ := hinv
      DefeqStrong.retype ho hΓ
        (.appDF ht₂ ht₂' hfeq haeq (ht₂'.inst_congr haeq)) he⟩
  | _, _ => fun _ _ => throw (.reject .notDefEq)

end

def checkIsType (ho : E.Ordered) (t : Expr ζ ℓ 0) :
    Except Failure {l : Level ℓ // E[.nil] ⊢ₛ t : .sort l} := do
  let ⟨_, hts⟩ ← infer ho .nil t
  ensureSort ho .nil hts

def isProp (ho : E.Ordered) (t : Expr ζ ℓ 0) : Except Failure Bool := do
  let ⟨l, _⟩ ← checkIsType ho t
  pure (decide (l = .zero))

def checkAxiom (ho : E.Ordered) (t : Expr ζ ℓ 0) :
    Except Failure (PLift (Entry.WF E (.axiom t))) := do
  let ⟨l, ht⟩ ← checkIsType ho t
  pure ⟨.axiom ⟨l, ht.defeq⟩⟩

def checkDef (ho : E.Ordered) (t e : Expr ζ ℓ 0) :
    Except Failure (PLift (Entry.WF E (.def t e))) := do
  let ⟨l, ht⟩ ← checkIsType ho t
  let ⟨hvalue⟩ ← checkAgainst ho .nil e t
  pure ⟨.def ⟨l, ht.defeq⟩ hvalue.defeq⟩

def checkOpaque (ho : E.Ordered) (t e : Expr ζ ℓ 0) :
    Except Failure (PLift (Entry.WF E (.opaque t))) := do
  let ⟨l, ht⟩ ← checkIsType ho t
  let ⟨hvalue⟩ ← checkAgainst ho .nil e t
  pure ⟨.opaque hvalue.defeq ⟨l, ht.defeq⟩⟩

end Metalean.Checker
