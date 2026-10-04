/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Slow.Whnf
public import Metalean.Checker.Slow.Eta
public import Metalean.Decide
public import Metalean.Control
public import Metalean.Typing.Substitution
public import Metalean.Typing.Telescope
public import Metalean.Metatheory.Conversion
public import Metalean.Metatheory.Injectivity
public import Metalean.Metatheory.SubjectReduction
public import Metalean.Metatheory.Unique
import Metalean.Typing.Env
import Metalean.Typing.Inversion
import Metalean.Meta.IfRfl

@[expose] public section

namespace Metalean.Checker.Slow

open Frontend (Failure)

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

def etaStruct (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok) {ι : IndSig}
    (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n) (is : Fin (ι.nindices s) → Expr ζ ℓ n)
    (e₁ : Expr ζ ℓ n) (he : E[Γ] ⊢ e₁ : .ind η s ls ps is) :
    Except Failure {e₂ : Expr ζ ℓ n // E[Γ] ⊢ e₁ ≡ e₂ : .ind η s ls ps is} := do
  if e₁ matches .ctor .. then throw (.reject .notDefEq)
  let ⟨hc⟩ ← guardProofOr (ι.nctors s = 1) (.reject .notDefEq)
  let c : Fin (ι.nctors s) := ⟨0, by omega⟩
  let ⟨hs⟩ ← guardProofOr ((E.get η).block.IsStructure s c) (.reject .notDefEq)
  pure ⟨hs.rebuildTerm η ls ps e₁,
    have ⟨_, hind⟩ := he.regular
    structure_eta hs hE hΓ (Defeq.ind_typed hE hind).1 he⟩

mutual

partial def whnfType {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hE : EnvWF E) (hΓ : E[Γ] ⊢ ok) (t₁ : Expr ζ ℓ n) (ht : E[Γ] ⊢ t₁ typ) :
    Except Failure {t₂ : Expr ζ ℓ n // E[Γ] ⊢ t₁ ≡ t₂ typ} := do
  let ⟨t₂, hred⟩ ← whnf hE hΓ t₁ (have ⟨_, htu⟩ := ht; ⟨_, htu⟩)
  pure ⟨t₂, have ⟨_, htu⟩ := ht; .ofDefEq (hred htu)⟩

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
    have hB := (hE.entryWF η).block
    let ⟨hps⟩ ← Fin.sequenceLtM fun p hlt =>
      checkAgainst hE hΓ (ps p) ((E.get η).block.paramType ls ps p)
        (Inductive.paramType_isType hB p hlt)
    let ⟨his⟩ ← Fin.sequenceLtM fun i hlt =>
      checkAgainst hE hΓ (is i) ((E.get η).block.indexType ls s ps is i)
        (Inductive.indexType_isType (hB.indices s) i hΓ hps hlt)
    pure ⟨.sort (E.get η).block.level{ls},
      .indDF hps his⟩
  | .ctor η s c ls ps fds recFds => do
    have hB := (hE.entryWF η).block
    let ⟨hps⟩ ← Fin.sequenceLtM fun p hlt =>
      checkAgainst hE hΓ (ps p) ((E.get η).block.paramType ls ps p)
        (Inductive.paramType_isType hB p hlt)
    let ⟨hfds⟩ ← Fin.sequenceLtM fun f hlt =>
      checkAgainst hE hΓ (fds f)
        (((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
        ⟨_, ((hB.ctors s c).ordinaryFieldExpr_congr hB.params f hps hlt).left⟩
    let ⟨hrecFds⟩ ← Fin.sequenceM fun f =>
      checkAgainst hE hΓ (recFds f)
        (((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f)
        ((hB.ctors s c).recursiveFieldExpr rfl f hΓ hps hfds)
    pure ⟨.ind η s ls ps fun index => ((E.get η).block.ctors s c).targetIndex ls ps fds index,
      .ctorDF hps hfds hrecFds
        (fun f => (hB.ctors s c).ordinaryFieldExpr_congr hB.params f hps (fun g _ => hfds g))
        (fun f => ((hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f hps hfds).choose_spec)
        ((hE.entryWF η).ctorType s c hps hfds)⟩
  | .recr η s ls l ps ms mins is maj => do
    let ⟨hrec⟩ ← guardProofOr ((E.get η).block.RecAllowed ls l) (.reject .recursorLevel)
    have hB := (hE.entryWF η).block
    let ⟨hps⟩ ← Fin.sequenceLtM fun p hlt =>
      checkAgainst hE hΓ (ps p) ((E.get η).block.paramType ls ps p)
        (Inductive.paramType_isType hB p hlt)
    let ⟨hms⟩ ← Fin.sequenceM fun t =>
      checkAgainst hE hΓ (ms t) ((E.get η).block.motiveType η ls ps l t)
        (Inductive.motiveType_congr hB hΓ hps).left
    let ⟨hmins⟩ ← Fin.sequenceM fun t => Fin.sequenceM fun c =>
      checkAgainst hE hΓ (mins t c) ((E.get η).block.caseFnType η ls ps ms t c)
        (Inductive.caseFnType_congr hB hΓ hps hms).left
    let ⟨his⟩ ← Fin.sequenceLtM fun i hlt =>
      checkAgainst hE hΓ (is i) ((E.get η).block.indexType ls s ps is i)
        (Inductive.indexType_isType (hB.indices s) i hΓ hps hlt)
    let ⟨hmaj⟩ ← checkAgainst hE hΓ maj (.ind η s ls ps is) ⟨_, .indDF hps his⟩
    pure ⟨Inductive.motiveResult (ms s) is maj,
      .recrDF hrec hps hms hmins his hmaj
        (hB.motiveResult_congr hΓ hps hms his hmaj)⟩
  | .quot _ l α r => do
    let ⟨hα⟩ ← checkAgainst hE hΓ α (.sort l) ⟨_, .sortDF⟩
    let ⟨hr⟩ ← checkAgainst hE hΓ r (Quot.relType α) ⟨_, Quot.relType_congr hα⟩
    pure ⟨.sort l, .quotDF hα hr⟩
  | .quotMk η l α r e => do
    let ⟨hα⟩ ← checkAgainst hE hΓ α (.sort l) ⟨_, .sortDF⟩
    let ⟨hr⟩ ← checkAgainst hE hΓ r (Quot.relType α) ⟨_, Quot.relType_congr hα⟩
    let ⟨he⟩ ← checkAgainst hE hΓ e α ⟨_, hα⟩
    pure ⟨.quot η l α r, .quotMkDF hα hr he⟩
  | .quotLift η l₁ l₂ α r β f h a => do
    let ⟨hα⟩ ← checkAgainst hE hΓ α (.sort l₁) ⟨_, .sortDF⟩
    let ⟨hr⟩ ← checkAgainst hE hΓ r (Quot.relType α) ⟨_, Quot.relType_congr hα⟩
    let ⟨hβ⟩ ← checkAgainst hE hΓ β (.sort l₂) ⟨_, .sortDF⟩
    have hβwk : E[Γ.snoc α] ⊢ β.wk : .sort l₂ := hβ.wk α
    let ⟨hf⟩ ← checkAgainst hE hΓ f (.forallE α β.wk) ⟨_, .forallEDF hα hβwk hβwk⟩
    let ⟨hcompat⟩ ← checkAgainst hE hΓ h (Quot.compatType (E.get η).eqHead l₂ α r β f)
      (Quot.compatType_isType (hE.eqBlock η) hα hr hβ hf)
    let ⟨ha⟩ ← checkAgainst hE hΓ a (.quot η l₁ α r) ⟨_, .quotDF hα hr⟩
    pure ⟨β, .quotLiftDF hα hr hβ hf hcompat ha⟩
  | .quotInd η l α r β f e => do
    let ⟨hα⟩ ← checkAgainst hE hΓ α (.sort l) ⟨_, .sortDF⟩
    let ⟨hr⟩ ← checkAgainst hE hΓ r (Quot.relType α) ⟨_, Quot.relType_congr hα⟩
    let ⟨hβ⟩ ← checkAgainst hE hΓ β (Quot.motiveType η l α r) (Quot.motiveType_isType hα hr)
    let ⟨hf⟩ ← checkAgainst hE hΓ f (Quot.minorType η l α r β)
      (Quot.minorType_isType hα hr hβ)
    let ⟨he⟩ ← checkAgainst hE hΓ e (.quot η l α r) ⟨_, .quotDF hα hr⟩
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
    let ⟨l, ht⟩ ← checkIsType hE hΓ t
    let ⟨hv⟩ ← checkAgainst hE hΓ v t ⟨l, ht⟩
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
    (e t₁ : Expr ζ ℓ n) (ht : E[Γ] ⊢ t₁ typ) : Except Failure (PLift (E[Γ] ⊢ e : t₁)) := do
  let ⟨t₂, he⟩ ← infer hE hΓ e
  let ⟨hconv⟩ ← checkTypeEq hE hΓ t₂ t₁ he.regular ht
  pure ⟨hconv.conv he⟩

partial def inferTyped (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok) :
    (e : Expr ζ ℓ n) → (∃ t, E[Γ] ⊢ e : t) →
    Except Failure {t : Expr ζ ℓ n // E[Γ] ⊢ e : t}
  | .var v => fun _ => pure ⟨Γ.get v, hΓ.var v⟩
  | .sort l => fun _ => pure ⟨.sort (.succ l), .sortDF⟩
  | .const η ls => fun _ =>
    pure ⟨(E.get η).constType{ls}.wkClosed,
      have ⟨_, htype⟩ := (hE.entryWF η).constType (Γ := Γ) ls
      .constDF htype⟩
  | .ind η _ ls _ _ => fun he => pure ⟨.sort (E.get η).block.level{ls}, UniqTyFrom.typed UniqTyFrom.ind he⟩
  | .ctor η s c ls ps fds _ => fun he =>
    pure ⟨.ind η s ls ps (((E.get η).block.ctors s c).targetIndex ls ps fds), UniqTyFrom.typed UniqTyFrom.ctor he⟩
  | .recr _ s _ _ _ ms _ is maj => fun he =>
    pure ⟨Inductive.motiveResult (ms s) is maj, UniqTyFrom.typed UniqTyFrom.recr he⟩
  | .quot _ l _ _ => fun he => pure ⟨.sort l, UniqTyFrom.typed UniqTyFrom.quot he⟩
  | .quotMk η l α r _ => fun he => pure ⟨.quot η l α r, UniqTyFrom.typed UniqTyFrom.quotMk he⟩
  | .quotLift _ _ _ _ _ β _ _ _ => fun he => pure ⟨β, UniqTyFrom.typed UniqTyFrom.quotLift he⟩
  | .quotInd _ _ _ _ β _ a => fun he => pure ⟨.app β a, UniqTyFrom.typed UniqTyFrom.quotInd he⟩
  | .app f a => fun he => do
    let ⟨_, hf⟩ ← inferTyped hE hΓ f
      (have ⟨_, h⟩ := he; have ⟨_, _, hf, _⟩ := h.app_inv; ⟨_, hf⟩)
    let ⟨_, t', hpi⟩ ← ensureForall hE hΓ hf
    pure ⟨t'.inst a, by
      have ⟨_, h⟩ := he
      have ⟨_, _, hf', ha, _⟩ := h.app_inv
      have ⟨hdom, _⟩ := TypeEq.forallE_inj hE hΓ (Defeq.uniqTy hE hΓ hf' hpi)
      exact UniqTyFrom.typed (UniqTyFrom.app rfl hE hΓ (fun h => Defeq.uniqTy hE hΓ hpi h)
        (hdom.conv ha)) he⟩
  | .lam t b => fun he => do
    have ht : E[Γ] ⊢ t typ :=
      have ⟨_, h⟩ := he
      have ⟨_, _, hT⟩ := h.lam_inv hΓ
      have ⟨_, hpi⟩ := hT.right
      hpi.forallE_inv.1
    let ⟨tb, hb⟩ ← inferTyped hE (hΓ.snoc ht) b
      (have ⟨_, h⟩ := he; have ⟨_, hb, _⟩ := h.lam_inv hΓ; ⟨_, hb⟩)
    pure ⟨.forallE t tb, by
      have ⟨_, ht⟩ := ht
      have ⟨_, htb⟩ := hb.regular
      exact .lamDF ht htb htb hb hb⟩
  | .forallE t t' => fun he => do
    let ⟨l, ht⟩ ← sortOf hE hΓ t
      (have ⟨_, h⟩ := he; have ⟨_, _, ht, _⟩ := h.forallE_ty_inv; ⟨_, ht⟩)
    let ⟨l₁, ht'⟩ ← sortOf hE (hΓ.snoc ⟨l, ht⟩) t'
      (have ⟨_, h⟩ := he; have ⟨_, _, _, ht', _⟩ := h.forallE_ty_inv; ⟨_, ht'⟩)
    pure ⟨.sort (.imax l l₁), .forallEDF ht ht' ht'⟩
  | .letE _ v b => fun he => do
    let ⟨r, hb⟩ ← inferTyped hE hΓ (b.inst v)
      (have ⟨_, h⟩ := he; have ⟨_, _, _, hb, _⟩ := h.letE_inv hΓ; ⟨_, hb⟩)
    pure ⟨r, by
      have ⟨_, h⟩ := he
      have ⟨_, ⟨_, ht⟩, hv, _, _⟩ := h.letE_inv hΓ
      have ⟨_, hr⟩ := hb.regular
      exact (Defeq.zeta ht hv hr hb).left⟩

partial def sortOf (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    (t : Expr ζ ℓ n) (ht : E[Γ] ⊢ t typ) :
    Except Failure {l : Level ℓ // E[Γ] ⊢ t : .sort l} := do
  let ⟨_, hts⟩ ← inferTyped hE hΓ t (have ⟨_, h⟩ := ht; ⟨_, h⟩)
  ensureSort hE hΓ hts

partial def checkTyped (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    (e t₁ : Expr ζ ℓ n) (he : ∃ t, E[Γ] ⊢ e : t) (ht : E[Γ] ⊢ t₁ typ) :
    Except Failure (PLift (E[Γ] ⊢ e : t₁)) := do
  let ⟨t₂, h⟩ ← inferTyped hE hΓ e he
  let ⟨hconv⟩ ← checkTypeEq hE hΓ t₂ t₁ h.regular ht
  pure ⟨hconv.conv h⟩

partial def isDefEqTyped (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n} (hΓ : E[Γ] ⊢ ok)
    (t e₁ e₂ : Expr ζ ℓ n) (he₁ : E[Γ] ⊢ e₁ : t) (he₂ : ∃ t, E[Γ] ⊢ e₂ : t) :
    Except Failure (PLift (E[Γ] ⊢ e₁ ≡ e₂ : t)) := do
  if let .ok ⟨heq⟩ := e₁.decEq? e₂ then return ⟨heq ▸ he₁⟩
  let ⟨h₂⟩ ← checkTyped hE hΓ e₂ t he₂ he₁.regular
  isDefEq hE hΓ t e₁ e₂ he₁ h₂

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
      let ⟨l, htl⟩ ← sortOf hE hΓ t ht
      let ⟨l₁, htl₁⟩ ← sortOf hE hΓ t₁ ht₁
      let ⟨rfl⟩ ← guardProofOr (l = l₁) (.reject .notDefEq)
      let ⟨hc⟩ ← isDefEq hE hΓ (.sort l) t t₁ htl htl₁
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
    (t e₁ e₂ : Expr ζ ℓ n) (he₁ : E[Γ] ⊢ e₁ : t) (he₂ : E[Γ] ⊢ e₂ : t) :
    Except Failure (PLift (E[Γ] ⊢ e₁ ≡ e₂ : t)) := do
  if let .ok ⟨heq⟩ := e₁.decEq? e₂ then return ⟨heq ▸ he₁⟩
  let ⟨l, ht⟩ ← sortOf hE hΓ t he₁.regular
  if hzero : l = .zero then
    return ⟨by
      subst hzero
      exact .proofIrrel ht he₁ he₂⟩
  let ⟨e₃, hstep₁⟩ ← whnf hE hΓ e₁ ⟨_, he₁⟩
  let ⟨e₄, hstep₂⟩ ← whnf hE hΓ e₂ ⟨_, he₂⟩
  have he₃ := (hstep₁ he₁).right
  have he₄ := (hstep₂ he₂).right
  let ⟨hc⟩ ←
    (do let ⟨rfl⟩ ← e₃.decEq? e₄; pure ⟨he₃⟩) <|>
    isDefEqCore hE hΓ t e₃ e₄ he₃ he₄ <|>
    isDefEqEta hE hΓ t e₄ he₄ e₃ he₃ <|>
    (do let ⟨h⟩ ← isDefEqEta hE hΓ t e₃ he₃ e₄ he₄; pure ⟨h.symm⟩) <|>
    isDefEqStruct hE hΓ t e₄ he₄ e₃ he₃ <|>
    (do let ⟨h⟩ ← isDefEqStruct hE hΓ t e₃ he₃ e₄ he₄; pure ⟨h.symm⟩) <|>
    isDefEqUnitLike hE hΓ t e₃ e₄ he₃ he₄
  pure ⟨(hstep₁ he₁).trans (hc.trans (hstep₂ he₂).symm)⟩

partial def whnf (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) (e₁ : Expr ζ ℓ n) (he : ∃ t, E[Γ] ⊢ e₁ : t) :
    Except Failure {e₂ : Expr ζ ℓ n //
      ∀ {t}, E[Γ] ⊢ e₁ : t → E[Γ] ⊢ e₁ ≡ e₂ : t} := do
  let ⟨e₂, hr₁⟩ ← whnfCore E e₁
  have h₁ {t} (h : E[Γ] ⊢ e₁ : t) : E[Γ] ⊢ e₁ ≡ e₂ : t := WHRedS.defeq hE hΓ hr₁ h
  have he₂ : ∃ t, E[Γ] ⊢ e₂ : t := have ⟨_, h⟩ := he; ⟨_, (h₁ h).right⟩
  let .ok ⟨e₃, h₂⟩ := whnfStep hE hΓ e₂ he₂
    | return ⟨e₂, h₁⟩
  let ⟨e₄, hr₂⟩ ← whnfCore E e₃
  have h₃ {t} (h : E[Γ] ⊢ e₂ : t) : E[Γ] ⊢ e₂ ≡ e₄ : t :=
    (h₂ h).trans (WHRedS.defeq hE hΓ hr₂ (h₂ h).right)
  if e₂.decEq? e₄ matches .ok _ then return ⟨e₂, h₁⟩
  let ⟨e₅, h₄⟩ ← whnf hE hΓ e₄ (have ⟨_, h⟩ := he₂; ⟨_, (h₃ h).right⟩)
  pure ⟨e₅, fun h => (h₁ h).trans ((h₃ (h₁ h).right).trans (h₄ (h₃ (h₁ h).right).right))⟩

partial def whnfStep (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) :
    (e₁ : Expr ζ ℓ n) → (∃ t, E[Γ] ⊢ e₁ : t) →
    Except Failure {e₂ : Expr ζ ℓ n //
      ∀ {t}, E[Γ] ⊢ e₁ : t → E[Γ] ⊢ e₁ ≡ e₂ : t}
  | .app f₁ a => fun he => do
    let ⟨f₂, hr⟩ ← whnf hE hΓ f₁
      (have ⟨_, h⟩ := he; have ⟨_, _, hf, _⟩ := h.app_inv; ⟨_, hf⟩)
    if f₁.decEq? f₂ matches .ok _ then throw (.reject .notDefEq)
    pure ⟨.app f₂ a, fun h => (Frame.app a).plug_defeq hE hΓ hr h⟩
  | .recr η s ls l ps ms mins is maj₁ => fun he =>
    kLikeStep hE hΓ (.recr η s ls l ps ms mins is maj₁) he <|> do
      have hmaj : E[Γ] ⊢ maj₁ : .ind η s ls ps is :=
        have ⟨_, h⟩ := he
        (Defeq.recr_typed hE hΓ h).2.2.2.2.2
      let ⟨maj₂, hm⟩ ← whnf hE hΓ maj₁ ⟨_, hmaj⟩
      let ⟨maj₃, hη⟩ ←
        (do
          if (E.get η).block.level{ls} = .zero then throw (.reject .notDefEq)
          etaStruct hE hΓ η s ls ps is maj₂ (hm hmaj).right) <|>
        pure ⟨maj₂, (hm hmaj).right⟩
      if maj₁.decEq? maj₃ matches .ok _ then throw (.reject .notDefEq)
      have hmajor := (hm hmaj).trans hη
      pure ⟨.recr η s ls l ps ms mins is maj₃,
        fun h => (Frame.recr η s ls l ps ms mins is).plug_defeq hE hΓ (hmajor.retype hE hΓ) h⟩
  | .quotLift η l₁ l₂ α r β f h a₁ => fun he => do
    let ⟨a₂, hr⟩ ← whnf hE hΓ a₁
      (have ⟨_, hq⟩ := he
       have ⟨_, _, _, _, _, _, _, _, _, _, _, ha, _⟩ := hq.quotLift_prem
       ⟨_, ha.right⟩)
    if a₁.decEq? a₂ matches .ok _ then throw (.reject .notDefEq)
    pure ⟨.quotLift η l₁ l₂ α r β f h a₂,
      fun hq => (Frame.quotLift η l₁ l₂ α r β f h).plug_defeq hE hΓ hr hq⟩
  | .quotInd η l α r β f a₁ => fun he => do
    let ⟨a₂, hr⟩ ← whnf hE hΓ a₁
      (have ⟨_, hq⟩ := he
       have ⟨_, _, _, _, _, _, _, _, _, ha, _, _⟩ := hq.quotInd_prem
       ⟨_, ha.right⟩)
    if a₁.decEq? a₂ matches .ok _ then throw (.reject .notDefEq)
    pure ⟨.quotInd η l α r β f a₂,
      fun hq => (Frame.quotInd η l α r β f).plug_defeq hE hΓ hr hq⟩
  | _ => fun _ => throw (.reject .notDefEq)

partial def isDefEqStruct (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) (t e₂ : Expr ζ ℓ n) (he₂ : E[Γ] ⊢ e₂ : t) :
    (e₁ : Expr ζ ℓ n) → E[Γ] ⊢ e₁ : t →
    Except Failure (PLift (E[Γ] ⊢ e₁ ≡ e₂ : t))
  | .ctor η s c ls ps fds recFds => fun he₁ => do
    have hT := UniqTyFrom.ctor he₁
    let ⟨e₃, hη⟩ ← etaStruct hE hΓ η s ls ps _ e₂ (hT.symm.conv he₂)
    let ⟨hc⟩ ← isDefEqCore hE hΓ t (.ctor η s c ls ps fds recFds) e₃ he₁ (hT.conv hη.right)
    pure ⟨hc.trans (hT.conv hη).symm⟩
  | _ => fun _ => throw (.reject .notDefEq)

partial def isDefEqEta (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) (t e₂ : Expr ζ ℓ n) (he₂ : E[Γ] ⊢ e₂ : t) :
    (e₁ : Expr ζ ℓ n) → E[Γ] ⊢ e₁ : t →
    Except Failure (PLift (E[Γ] ⊢ e₁ ≡ e₂ : t))
  | .lam t₂ b => fun he₁ => do
    if e₂ matches .lam .. then throw (.reject .notDefEq)
    let ⟨_, hfn⟩ ← inferTyped hE hΓ e₂ ⟨_, he₂⟩
    let ⟨t₃, t₃', hpi⟩ ← ensureForall hE hΓ hfn
    have heta : E[Γ] ⊢ .lam t₃ (.app e₂.wk (.var (Fin.last n))) ≡ e₂ : .forallE t₃ t₃' := by
      have ⟨_, htype⟩ := hpi.regular
      have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := htype.forallE_inv
      exact Defeq.eta ht ht' (by simpa [Expr.wk] using ht.wk t₃)
        (by simpa [Expr.wk] using hpi.wk t₃) hpi
    have hT := Defeq.uniqTy hE hΓ he₂ hpi
    let ⟨hlam⟩ ← isDefEq hE hΓ (.forallE t₃ t₃') (.lam t₂ b)
      (.lam t₃ (.app e₂.wk (.var (Fin.last n)))) (hT.conv he₁) heta.left
    pure ⟨hT.symm.conv (hlam.trans heta)⟩
  | _ => fun _ => throw (.reject .notDefEq)

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
  have hfields : IsEmpty (Fin (ι.ctors s c).nfields) := by
    rw [hf]
    infer_instance
  pure ⟨have ⟨_, hind⟩ := ht.right
    ht.symm.conv (unit_like_eta hs hfields hE hΓ (Defeq.ind_typed hE hind).1
      (ht.conv he₁) (ht.conv he₂))⟩

partial def kLikeStep (hE : EnvWF E) {n : Nat} {Γ : Ctx ζ ℓ 0 n}
    (hΓ : E[Γ] ⊢ ok) :
    (e₁ : Expr ζ ℓ n) → (∃ t, E[Γ] ⊢ e₁ : t) →
    Except Failure {e₂ : Expr ζ ℓ n //
      ∀ {t}, E[Γ] ⊢ e₁ : t → E[Γ] ⊢ e₁ ≡ e₂ : t}
  | .recr (ι := ι) η s ls l ps ms mins is maj => fun he => do
    unless ι.nsorts = 1 do throw (.reject .notDefEq)
    let ⟨hp⟩ ← guardProofOr ((E.get η).block.level = .zero) (.reject .notDefEq)
    let ⟨hc⟩ ← guardProofOr (ι.nctors s = 1) (.reject .notDefEq)
    let c : Fin (ι.nctors s) := ⟨0, by omega⟩
    let ⟨hf⟩ ← guardProofOr ((ι.ctors s c).nfields = 0) (.reject .notDefEq)
    let ⟨hr⟩ ← guardProofOr ((ι.ctors s c).nrecFields = 0) (.reject .notDefEq)
    let fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n := fun f => by omega
    let recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n := fun f => by omega
    have hrecr := have ⟨_, h⟩ := he; Defeq.recr_typed hE hΓ h
    have ⟨_, hps, _, _, his, hmaj⟩ := hrecr
    have hfields : IsEmpty (Fin (ι.ctors s c).nfields) := by
      rw [hf]
      infer_instance
    have hrecFields : IsEmpty (Fin (ι.ctors s c).nrecFields) := by
      rw [hr]
      infer_instance
    have hctor : E[Γ] ⊢ .ctor η s c ls ps fds recFds :
        .ind η s ls ps fun i => ((E.get η).block.ctors s c).targetIndex ls ps fds i :=
      Defeq.nullaryCtor (hE.entryWF η).block hfields hrecFields hps
    let ⟨hidx⟩ ← checkTypeEq hE hΓ
      (.ind η s ls ps fun i => ((E.get η).block.ctors s c).targetIndex ls ps fds i)
      (.ind η s ls ps is) hctor.regular ⟨_, .indDF hps his⟩
    have hprop : E[Γ] ⊢ .ind η s ls ps is : .prop := by
      have hind := Defeq.indDF hps his
      rwa [hp] at hind
    pure ⟨_, fun h => WHRed.klike_defeq hE hΓ hprop hmaj (hidx.conv hctor) h⟩
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
    let ⟨tb, hb⟩ ← inferTyped hE (hΓ.snoc ht₂) b
      (have ⟨_, hb, _⟩ := Defeq.lam_inv he hΓ; ⟨_, hb⟩)
    let ⟨hbEq⟩ ← isDefEqTyped hE (hΓ.snoc ht₂) tb b b₁ hb
      (have ⟨_, hb₁, _⟩ := Defeq.lam_inv he₁ hΓ; ⟨_, Defeq.snocConvTy hdom.symm hb₁⟩)
    pure ⟨by
      have ⟨_, hdom_sort⟩ := hdom.sort_uniq hE hΓ
      have ⟨_, htb⟩ := hb.regular
      exact Defeq.retype hE hΓ
        (.lamDF hdom_sort htb (hdom_sort.snocConv htb) hbEq (hdom_sort.snocConv hbEq)) he⟩
  | .const (kind := kind) (nlevels := nlevels) η ls,
      .const (kind := kind₁) (nlevels := nlevels₁) η₁ ls₁ => fun he _ => do
    let ⟨rfl⟩ ← guardProofOr (kind = kind₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (nlevels = nlevels₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    pure ⟨he⟩
  | .ind η s ls ps is, .ind η₁ s₁ ls₁ ps₁ is₁ => fun he he₁ => do
    let ⟨rfl, rfl⟩ ← η.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s = s₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    have ⟨hpsl, hisl⟩ := Defeq.ind_typed hE he
    have ⟨hpsr, hisr⟩ := Defeq.ind_typed hE he₁
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      isDefEqTyped hE hΓ ((E.get η).block.paramType ls ps p) (ps p) (ps₁ p)
        (hpsl p) ⟨_, hpsr p⟩
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      isDefEqTyped hE hΓ ((E.get η).block.indexType ls s ps is i) (is i) (is₁ i)
        (hisl i) ⟨_, hisr i⟩
    pure ⟨Defeq.retype hE hΓ (.indDF hps his) he⟩
  | .ctor η s c ls ps fds recFds, .ctor η₁ s₁ c₁ ls₁ ps₁ fds₁ recFds₁ => fun he he₁ => do
    let ⟨rfl, rfl⟩ ← η.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s = s₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (c = c₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    have ⟨hpsl, hfdsl, hrecFdsl⟩ := Defeq.ctor_typed hE he
    have ⟨hpsr, hfdsr, hrecFdsr⟩ := Defeq.ctor_typed hE he₁
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      isDefEqTyped hE hΓ ((E.get η).block.paramType ls ps p) (ps p) (ps₁ p)
        (hpsl p) ⟨_, hpsr p⟩
    let ⟨hfds⟩ ← Fin.sequenceM fun f =>
      isDefEqTyped hE hΓ
        (((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f)
        (fds f) (fds₁ f) (hfdsl f) ⟨_, hfdsr f⟩
    let ⟨hrecFds⟩ ← Fin.sequenceM fun f =>
      isDefEqTyped hE hΓ
        (((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f)
        (recFds f) (recFds₁ f) (hrecFdsl f) ⟨_, hrecFdsr f⟩
    pure ⟨by
      have hi := (hE.entryWF η).block
      exact Defeq.retype hE hΓ
        (.ctorDF hps hfds hrecFds
          (fun f => (hi.ctors s c).ordinaryFieldExpr_congr hi.params f hps (fun g _ => hfds g))
          (fun f => ((hi.ctors s c).recursiveFieldExpr_congr hi.params rfl f hps hfds).choose_spec)
          ((hE.entryWF η).ctorType s c hps hfds)) he⟩
  | .recr η s ls l ps ms mins is maj, .recr η₁ s₁ ls₁ l₁ ps₁ ms₁ mins₁ is₁ maj₁ => fun he he₁ => do
    let ⟨rfl, rfl⟩ ← η.indDecEq? η₁
    let ⟨rfl⟩ ← guardProofOr (s = s₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l = l₁) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (ls = ls₁) (.reject .notDefEq)
    have ⟨hrec, hpsl, hmsl, hminsl, hisl, hmajl⟩ := Defeq.recr_typed hE hΓ he
    have ⟨_, hpsr, hmsr, hminsr, hisr, hmajr⟩ := Defeq.recr_typed hE hΓ he₁
    let ⟨hps⟩ ← Fin.sequenceM fun p =>
      isDefEqTyped hE hΓ ((E.get η).block.paramType ls ps p) (ps p) (ps₁ p)
        (hpsl p) ⟨_, hpsr p⟩
    let ⟨hms⟩ ← Fin.sequenceM fun t =>
      isDefEqTyped hE hΓ ((E.get η).block.motiveType η ls ps l t) (ms t) (ms₁ t)
        (hmsl t) ⟨_, hmsr t⟩
    let ⟨hmins⟩ ← Fin.sequenceM fun t => Fin.sequenceM fun c =>
      isDefEqTyped hE hΓ ((E.get η).block.caseFnType η ls ps ms t c)
        (mins t c) (mins₁ t c) (hminsl t c) ⟨_, hminsr t c⟩
    let ⟨his⟩ ← Fin.sequenceM fun i =>
      isDefEqTyped hE hΓ ((E.get η).block.indexType ls s ps is i) (is i) (is₁ i)
        (hisl i) ⟨_, hisr i⟩
    let ⟨hmaj⟩ ← isDefEqTyped hE hΓ (.ind η s ls ps is) maj maj₁ hmajl ⟨_, hmajr⟩
    pure ⟨Defeq.retype hE hΓ
      (.recrDF hrec hps hms hmins his hmaj
        ((hE.entryWF η).block.motiveResult_congr hΓ hps hms his hmaj)) he⟩
  | .quot η l₁ α r, .quot η₁ l₂ α₁ r₁ => fun he he₁ => do
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    have ⟨hαl, hrl⟩ := Defeq.quot_formation_inv he
    have ⟨hαr, hrr⟩ := Defeq.quot_formation_inv he₁
    let ⟨hα⟩ ← isDefEqTyped hE hΓ (.sort l₁) α α₁ hαl ⟨_, hαr⟩
    let ⟨hr⟩ ← isDefEqTyped hE hΓ (Quot.relType α) r r₁ hrl ⟨_, hrr⟩
    pure ⟨Defeq.retype hE hΓ (.quotDF hα hr) he⟩
  | .quotMk η l₁ α r a, .quotMk η₁ l₂ α₁ r₁ a₁ => fun he he₁ => do
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    have ⟨hαl, hrl, hal⟩ := Defeq.quotMk_typed he
    have ⟨hαr, hrr, har⟩ := Defeq.quotMk_typed he₁
    let ⟨hα⟩ ← isDefEqTyped hE hΓ (.sort l₁) α α₁ hαl ⟨_, hαr⟩
    let ⟨hr⟩ ← isDefEqTyped hE hΓ (Quot.relType α) r r₁ hrl ⟨_, hrr⟩
    let ⟨ha⟩ ← isDefEqTyped hE hΓ α a a₁ hal ⟨_, har⟩
    pure ⟨Defeq.retype hE hΓ (.quotMkDF hα hr ha) he⟩
  | .quotLift η l₁ l₂ α r β f h a, .quotLift η₁ l₁' l₂' α₁ r₁ β₁ f₁ h₁ a₁ => fun he he₁ => do
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₁') (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (l₂ = l₂') (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    have ⟨hαl, hrl, hβl, hfl, hhl, hal⟩ := Defeq.quotLift_typed he
    have ⟨hαr, hrr, hβr, hfr, hhr, har⟩ := Defeq.quotLift_typed he₁
    let ⟨hα⟩ ← isDefEqTyped hE hΓ (.sort l₁) α α₁ hαl ⟨_, hαr⟩
    let ⟨hr⟩ ← isDefEqTyped hE hΓ (Quot.relType α) r r₁ hrl ⟨_, hrr⟩
    let ⟨hβ⟩ ← isDefEqTyped hE hΓ (.sort l₂) β β₁ hβl ⟨_, hβr⟩
    let ⟨hf⟩ ← isDefEqTyped hE hΓ (.forallE α β.wk) f f₁ hfl ⟨_, hfr⟩
    let ⟨hh⟩ ← checkTyped hE hΓ h (Quot.compatType (E.get η).eqHead l₂ α r β f) hhl
      (Quot.compatType_isType (hE.eqBlock η) hαl hrl hβl hfl)
    let ⟨hcompat⟩ ← isDefEqTyped hE hΓ (Quot.compatType (E.get η).eqHead l₂ α r β f) h h₁
      hh hhr
    let ⟨ha⟩ ← isDefEqTyped hE hΓ (.quot η l₁ α r) a a₁ hal ⟨_, har⟩
    pure ⟨Defeq.retype hE hΓ (.quotLiftDF hα hr hβ hf hcompat ha) he⟩
  | .quotInd η l₁ α r β f a, .quotInd η₁ l₂ α₁ r₁ β₁ f₁ a₁ => fun he he₁ => do
    let ⟨rfl⟩ ← guardProofOr (l₁ = l₂) (.reject .notDefEq)
    let ⟨rfl⟩ ← guardProofOr (η = η₁) (.reject .notDefEq)
    have ⟨hαl, hrl, hβl, hfl, hal⟩ := Defeq.quotInd_typed he
    have ⟨hαr, hrr, hβr, hfr, har⟩ := Defeq.quotInd_typed he₁
    let ⟨hα⟩ ← isDefEqTyped hE hΓ (.sort l₁) α α₁ hαl ⟨_, hαr⟩
    let ⟨hr⟩ ← isDefEqTyped hE hΓ (Quot.relType α) r r₁ hrl ⟨_, hrr⟩
    let ⟨hβ⟩ ← isDefEqTyped hE hΓ (Quot.motiveType η l₁ α r) β β₁ hβl ⟨_, hβr⟩
    let ⟨hfm⟩ ← checkTyped hE hΓ f (Quot.minorType η l₁ α r β) hfl
      (Quot.minorType_isType hαl hrl hβl)
    let ⟨hf⟩ ← isDefEqTyped hE hΓ (Quot.minorType η l₁ α r β) f f₁ hfm hfr
    let ⟨ha⟩ ← isDefEqTyped hE hΓ (.quot η l₁ α r) a a₁ hal ⟨_, har⟩
    pure ⟨Defeq.retype hE hΓ
      (.quotIndDF hα hr hβ hf ha
        (.appDF (.quotDF hα.left hr.left) .sortDF hβ ha .sortDF)) he⟩
  | .app f a, .app f₁ a₁ => fun he he₁ => do
    let ⟨_, hfn⟩ ← inferTyped hE hΓ f
      (have ⟨_, _, hf, _⟩ := he.app_inv; ⟨_, hf⟩)
    let ⟨t₂, t₂', hpi⟩ ← ensureForall hE hΓ hfn
    let ⟨hfeq⟩ ← isDefEqTyped hE hΓ (.forallE t₂ t₂') f f₁ hpi
      (have ⟨_, _, hf, _⟩ := he₁.app_inv; ⟨_, hf⟩)
    have ha : E[Γ] ⊢ a : t₂ :=
      have ⟨_, _, hf, ha, _⟩ := he.app_inv
      have ⟨hdom, _⟩ := TypeEq.forallE_inj hE hΓ (Defeq.uniqTy hE hΓ hf hpi)
      hdom.conv ha
    let ⟨haeq⟩ ← isDefEqTyped hE hΓ t₂ a a₁ ha
      (have ⟨_, _, _, ha, _⟩ := he₁.app_inv; ⟨_, ha⟩)
    pure ⟨by
      have ⟨_, hty⟩ := hpi.regular
      have ⟨⟨_, ht⟩, ⟨_, ht'⟩⟩ := hty.forallE_inv
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
  let ⟨hvalue⟩ ← checkAgainst hE .nil e t ⟨l, ht⟩
  pure ⟨.def ⟨l, ht⟩ hvalue⟩

def checkOpaque (hE : EnvWF E) (t e : Expr ζ ℓ 0) :
    Except Failure (PLift (EntryWF E (.opaque t))) := do
  let ⟨l, ht⟩ ← checkIsType hE .nil t
  let ⟨hvalue⟩ ← checkAgainst hE .nil e t ⟨l, ht⟩
  pure ⟨.opaque hvalue ⟨l, ht⟩⟩

end Metalean.Checker.Slow
