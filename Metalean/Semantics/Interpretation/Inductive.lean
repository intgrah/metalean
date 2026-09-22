/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Inductive
public import Metalean.Typing.Telescope
public import Metalean.Semantics.Domain.Constructors
public import Metalean.Semantics.Interpretation.Family.Application
public import Metalean.Semantics.Interpretation.Family.Basic
public import Metalean.Semantics.Interpretation.Family.Substitution
public import Metalean.Semantics.Syntax.Rank
import Mathlib.Order.Filter.Finite

@[expose] public section

namespace Metalean

open CategoryTheory Presheaf

namespace CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}
  {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}

structure IndTyping (Γ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ Γ.as.len)
    (is : Fin (ι.nindices s) → Expr ζ ℓ Γ.as.len) : Prop where
  param (p : Fin ι.nparams) : E[Γ.as.ctx] ⊢ ps p : (E.get η).block.paramType ls ps p
  index (i : Fin (ι.nindices s)) : E[Γ.as.ctx] ⊢ is i : (E.get η).block.indexType ls s ps is i

noncomputable def IndTyping.code {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len} {is : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len}
    (h : IndTyping Γ₁ η s ls ps is) : IndCode Γ₁ :=
  ⟨η, s, fun p => ls p, fun p => Tm.label Γ₁.as (h.param p), fun i => Tm.label Γ₁.as (h.index i)⟩

namespace IndTyping

variable {ls : Fin ι.nlevels → Level ℓ} {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len}

theorem ofTyping (hB : InductiveWF E (E.get η).block) {t : Expr ζ ℓ Γ₁.as.len}
    (h : E[Γ₁.as.ctx] ⊢ .ind η s ls ps₁ is₁ : t) : IndTyping Γ₁ η s ls ps₁ is₁ :=
  have ⟨_, _, hps, his, _⟩ := Defeq.ind_inv h
  ⟨fun p => Inductive.paramType_conv hB p hps, fun i => Inductive.indexType_conv hB i hps his⟩

theorem left (hps : ∀ p, E[Γ₁.as.ctx] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p)
    (his : ∀ i, E[Γ₁.as.ctx] ⊢ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i) :
    IndTyping Γ₁ η s ls ps₁ is₁ :=
  ⟨fun p => (hps p).left, fun i => (his i).left⟩

theorem right (hB : InductiveWF E (E.get η).block)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p)
    (his : ∀ i, E[Γ₁.as.ctx] ⊢ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i) :
    IndTyping Γ₁ η s ls ps₂ is₂ :=
  ⟨fun p => Inductive.paramType_conv hB p hps, fun i => Inductive.indexType_conv hB i hps his⟩

theorem subst (h : IndTyping Γ₁ η s ls ps₁ is₁) (σ : Γ₂.as ⟶ Γ₁.as) :
    IndTyping Γ₂ η s ls (fun p => (ps₁ p).subst σ.subst) fun i => (is₁ i).subst σ.subst where
  param p := by simpa using (h.param p).substitution σ.typed
  index i := by simpa using (h.index i).substitution σ.typed

theorem code_map (h : IndTyping Γ₁ η s ls ps₁ is₁) (σ : Γ₂.as ⟶ Γ₁.as) :
    h.code.map ((Tm E ℓ).map (RawCtx.toCtx.map σ).op) = (h.subst σ).code := by
  simp only [code, IndCode.map]
  congr 1
  · funext p
    exact congr(Tm.label _ (t := $(by simp)) _)
  · funext i
    exact congr(Tm.label _ (t := $(by simp)) _)

theorem code_rel (h : IndTyping Γ₁ η s ls ps₁ is₁) :
    h.code.rel = Level.rel ((E.get η).block.level.inst ls) :=
  rfl

theorem code_congr (hB : InductiveWF E (E.get η).block)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p)
    (his : ∀ i, E[Γ₁.as.ctx] ⊢ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i)
    (h₁ : IndTyping Γ₁ η s ls ps₁ is₁) (h₂ : IndTyping Γ₁ η s ls ps₂ is₂) : h₁.code = h₂.code := by
  simp only [code]
  congr 1
  · funext p
    exact Tm.label_eq (Inductive.paramType_congr hB p hps) (hps p)
  · funext i
    exact Tm.label_eq (Inductive.indexType_congr hB i hps his) (his i)

end IndTyping

structure CtorTyping (Γ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ Γ.as.len)
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ.as.len)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ Γ.as.len) : Prop where
  ordinary (f : Fin (ι.ctors s c).nfields) :
    E[Γ.as.ctx] ⊢ fds f : ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f
  recursive (f : Fin (ι.ctors s c).nrecFields) :
    E[Γ.as.ctx] ⊢ recFds f : ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f

noncomputable def CtorTyping.names {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ}
    {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len} {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ₁.as.len}
    {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ Γ₁.as.len}
    (h : CtorTyping Γ₁ η s c ls ps fds recFds) :
    Fin (CtorHead.mk η s c).arity → Tm_ Γ₁ :=
  Fin.append (fun f => Tm.label Γ₁.as (h.ordinary f)) fun f => Tm.label Γ₁.as (h.recursive f)

namespace CtorTyping

variable {c : Fin (ι.nctors s)} {ls₁ ls₂ : Fin ι.nlevels → Level ℓ}
  {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}
  {fds₁ fds₂ : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ₁.as.len}
  {recFds₁ recFds₂ : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ Γ₁.as.len}
  {fieldLevels : Fin (ι.ctors s c).nfields → Level ℓ}
  {recFieldLevels : Fin (ι.ctors s c).nrecFields → Level ℓ}

theorem left
    (hfields : ∀ f, E[Γ₁.as.ctx] ⊢ fds₁ f ≡ fds₂ f :
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls₁ ps₁ fds₁ f)
    (hrecFields : ∀ f, E[Γ₁.as.ctx] ⊢ recFds₁ f ≡ recFds₂ f :
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls₁ ps₁ fds₁ f) :
    CtorTyping Γ₁ η s c ls₁ ps₁ fds₁ recFds₁ :=
  ⟨fun f => (hfields f).left, fun f => (hrecFields f).left⟩

theorem right
    (hfields : ∀ f, E[Γ₁.as.ctx] ⊢ fds₁ f ≡ fds₂ f :
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls₁ ps₁ fds₁ f)
    (hrecFields : ∀ f, E[Γ₁.as.ctx] ⊢ recFds₁ f ≡ recFds₂ f :
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls₁ ps₁ fds₁ f)
    (hfieldTypes : ∀ f, E[Γ₁.as.ctx] ⊢
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls₁ ps₁ fds₁ f ≡
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls₂ ps₂ fds₂ f : .sort (fieldLevels f))
    (hrecFieldTypes : ∀ f, E[Γ₁.as.ctx] ⊢
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls₁ ps₁ fds₁ f ≡
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls₂ ps₂ fds₂ f : .sort (recFieldLevels f)) :
    CtorTyping Γ₁ η s c ls₂ ps₂ fds₂ recFds₂ :=
  ⟨fun f => (TypeEq.ofDefEq (hfieldTypes f)).conv (hfields f).right,
    fun f => (TypeEq.ofDefEq (hrecFieldTypes f)).conv (hrecFields f).right⟩

theorem subst (h : CtorTyping Γ₁ η s c ls₁ ps₁ fds₁ recFds₁) (σ : Γ₂.as ⟶ Γ₁.as) :
    CtorTyping Γ₂ η s c ls₁ (fun p => (ps₁ p).subst σ.subst) (fun f => (fds₁ f).subst σ.subst)
      fun f => (recFds₁ f).subst σ.subst where
  ordinary f := by simpa using (h.ordinary f).substitution σ.typed
  recursive f := by simpa using (h.recursive f).substitution σ.typed

theorem names_map (h : CtorTyping Γ₁ η s c ls₁ ps₁ fds₁ recFds₁) (σ : Γ₂.as ⟶ Γ₁.as) :
    (fun i => (Tm E ℓ).map (RawCtx.toCtx.map σ).op (h.names i)) = (h.subst σ).names := by
  funext i
  cases i using Fin.addCases with
  | left f =>
    simp only [names, Fin.append_left, Tm.map_label]
    exact congr(Tm.label _ (t := $(by simp)) _)
  | right f =>
    simp only [names, Fin.append_right, Tm.map_label]
    exact congr(Tm.label _ (t := $(by simp)) _)

theorem names_congr
    (hfields : ∀ f, E[Γ₁.as.ctx] ⊢ fds₁ f ≡ fds₂ f :
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls₁ ps₁ fds₁ f)
    (hrecFields : ∀ f, E[Γ₁.as.ctx] ⊢ recFds₁ f ≡ recFds₂ f :
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls₁ ps₁ fds₁ f)
    (hfieldTypes : ∀ f, E[Γ₁.as.ctx] ⊢
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls₁ ps₁ fds₁ f ≡
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls₂ ps₂ fds₂ f : .sort (fieldLevels f))
    (hrecFieldTypes : ∀ f, E[Γ₁.as.ctx] ⊢
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls₁ ps₁ fds₁ f ≡
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls₂ ps₂ fds₂ f : .sort (recFieldLevels f))
    (h : CtorTyping Γ₁ η s c ls₁ ps₁ fds₁ recFds₁) (h₁ : CtorTyping Γ₁ η s c ls₂ ps₂ fds₂ recFds₂) :
    h.names = h₁.names := by
  funext i
  cases i using Fin.addCases with
  | left f =>
    simpa [names, Fin.append_left] using Tm.label_eq (.ofDefEq (hfieldTypes f)) (hfields f)
  | right f =>
    simpa [names, Fin.append_right] using Tm.label_eq (.ofDefEq (hrecFieldTypes f)) (hrecFields f)

end CtorTyping

namespace RawFamily

noncomputable def ind (code : IndCode Γ₁) (Ts : Fin code.toIndHead.nctors → RawFamily Γ₁) :
    RawFamily Γ₁ where
  app X σ₁ := Preord.ofHom {
    toFun ρ := RawValue.ind (code.map ((Tm E ℓ).map σ₁.unop.op))
      fun c => (Ts c).app X σ₁ ρ
    monotone' _ _ h := RawValue.ind_mono (code.map ((Tm E ℓ).map σ₁.unop.op))
      fun c => ((Ts c).app X σ₁).hom.monotone h }
  naturality σ₂ σ₁ := Preord.ext fun ρ => by
    refine Eq.trans ?_ (RawValue.pullback_ind (code.map ((Tm E ℓ).map σ₁.unop.op))
      (fun c => (Ts c).app _ σ₁ ρ) σ₂.unop).symm
    refine RawValue.ind_congr (IndCode.map_comp_hom σ₁.unop σ₂.unop code) fun c c' hcc => ?_
    rw [Fin.ext hcc]
    exact ((Ts c').app_pullback σ₁ σ₂.unop ρ).symm

@[simp] theorem ind_value (code : IndCode Γ₁) (Ts : Fin code.toIndHead.nctors → RawFamily Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (ind code Ts).app _ σ.op ρ =
      RawValue.ind (code.map ((Tm E ℓ).map σ.op)) fun c => (Ts c).app _ σ.op ρ :=
  rfl

theorem ind_isFinitary (code : IndCode Γ₁) {Ts : Fin code.toIndHead.nctors → RawFamily Γ₁}
    (hTs : ∀ c, (Ts c).IsFinitary) : (ind code Ts).IsFinitary := by
  intro Γ₂ σ i ρ
  refine ΩLower.IsFinitary.of_eventually fun I y hy => ?_
  have ⟨ts, hts, hy⟩ := hy
  exact (Filter.eventually_all.2 fun c => IsFinitary.eventually (hTs c) σ i ρ I (hts c)).mono
    fun J hJ => ⟨ts, hJ, hy⟩

noncomputable def ctor (head : CtorHead ζ) (names : Fin head.arity → Tm_ Γ₁)
    (Fs : Fin head.arity → RawFamily Γ₁) : RawFamily Γ₁ where
  app X σ₁ := Preord.ofHom {
    toFun ρ := RawValue.ctor head (fun i => (Tm E ℓ).map σ₁.unop.op (names i))
      fun i => (Fs i).app X σ₁ ρ
    monotone' _ _ h := RawValue.ctor_mono _ _ fun i => ((Fs i).app X σ₁).hom.monotone h }
  naturality σ₂ σ₁ := Preord.ext fun ρ => by
    change RawValue.ctor _ _ _ = (RawValue.ctor _ _ _).pullback σ₂.unop
    rw [RawValue.pullback_ctor]
    congr 1
    · funext i
      simp
    · funext i
      exact ((Fs i).app_pullback σ₁ σ₂.unop ρ).symm

@[simp] theorem ctor_value (head : CtorHead ζ) (names : Fin head.arity → Tm_ Γ₁)
    (Fs : Fin head.arity → RawFamily Γ₁) (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (ctor head names Fs).app _ σ.op ρ =
      RawValue.ctor head (fun i => (Tm E ℓ).map σ.op (names i)) fun i =>
        (Fs i).app _ σ.op ρ :=
  rfl

theorem IsFinitary.ctor (head : CtorHead ζ) (names : Fin head.arity → Tm_ Γ₁)
    {Fs : Fin head.arity → RawFamily Γ₁} (hFs : ∀ i, (Fs i).IsFinitary) :
    (ctor head names Fs).IsFinitary := by
  intro Γ₂ σ i ρ
  refine ΩLower.IsFinitary.of_eventually fun I y hy => ?_
  have ⟨xs, hxs, hy⟩ := hy
  exact (Filter.eventually_all.2 fun j => IsFinitary.eventually (hFs j) σ i ρ I (hxs j)).mono
    fun J hJ => ⟨xs, hJ, hy⟩

end RawFamily

end CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {ι : IndSig}

theorem Expr.measure_ind_ctorTypeFn {n : Nat} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) :
    Prod.Lex (· < ·) (· < ·) (((E.get η).block.ctorTypeFn s c).instL fun p => ls p).measure
      (Expr.ind η s ls ps is).measure := by
  refine .left _ _ (lt_of_le_of_lt ?_ ((E.get_block_headRank_lt η).trans_le (le_max_left _ _)))
  simp only [Expr.headRank_instL, Inductive.ctorTypeFn, Ctx.headRank_lam, Ctx.headRank_pi,
    Expr.headRank, Nat.max_zero]
  exact max_le (le_max_left _ _)
    ((Ctor.headRank_ordinaryTeleAux_le _ _ _).trans (Inductive.headRank_ctors_le _ s c))

namespace CoherentShape

open CategoryTheory Presheaf

noncomputable def RawFamily.closedApps {Γ : CtxCat E ℓ} {k : Nat} (F : RawFamily (CtxCat.nil E ℓ))
    (names : Fin k → Tm_ Γ) (args : Fin k → RawFamily Γ) : RawFamily Γ :=
  (F.substitute (CtxCat.toNil Γ) (ValuationMap.ofFin Fin.elim0)).apps args fun i => {names i}

theorem RawFamily.IsFinitary.closedApps {Γ : CtxCat E ℓ} {k : Nat} {F : RawFamily (CtxCat.nil E ℓ)}
    (hF : F.IsFinitary) (names : Fin k → Tm_ Γ)
    {args : Fin k → RawFamily Γ} (ha : ∀ i, (args i).IsFinitary) :
    (RawFamily.closedApps F names args).IsFinitary :=
  RawFamily.IsFinitary.apps
    (RawFamily.IsFinitary.substitute hF _ fun i => i.elim0) ha _

theorem RawFamily.closedApps_value {Γ₁ : CtxCat E ℓ} {k : Nat} (F : RawFamily (CtxCat.nil E ℓ))
    (names : Fin k → Tm_ Γ₁) (args : Fin k → RawFamily Γ₁)
    {Γ₂ : CtxCat E ℓ} (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (RawFamily.closedApps F names args).app _ σ.op ρ =
      rawApps (F.app _ (σ ≫ CtxCat.toNil Γ₁).op fun _ => ⊥)
        (fun i => (Tm E ℓ).map σ.op (names i)) fun i => (args i).app _ σ.op ρ :=
  RawFamily.apps_named_value _ args names σ ρ

theorem RawFamily.closedApps_mono {Γ : CtxCat E ℓ} {k : Nat} {F₁ F₂ : RawFamily (CtxCat.nil E ℓ)}
    (hF : F₁ ≤ F₂) (names : Fin k → Tm_ Γ) (args : Fin k → RawFamily Γ) :
    RawFamily.closedApps F₁ names args ≤ RawFamily.closedApps F₂ names args := by
  intro X σ ρ
  induction X using Opposite.rec with | op Γ₂ =>
  change (RawFamily.closedApps F₁ names args).app _ σ.unop.op ρ ≤
    (RawFamily.closedApps F₂ names args).app _ σ.unop.op ρ
  rw [RawFamily.closedApps_value, RawFamily.closedApps_value]
  exact rawApps_mono (hF _ _ _) _ fun _ {_} _ _ hz => hz

theorem RawFamily.closedApps_iSup_le {Γ : CtxCat E ℓ} {k : Nat} (F : Nat → RawFamily (CtxCat.nil E ℓ))
    (names : Fin k → Tm_ Γ) (args : Fin k → RawFamily Γ) :
    RawFamily.closedApps (⨆ n, F n) names args ≤ ⨆ n, RawFamily.closedApps (F n) names args := by
  intro X σ ρ
  induction X using Opposite.rec with | op Γ₂ =>
  change (RawFamily.closedApps (⨆ n, F n) names args).app _ σ.unop.op ρ ≤
    (⨆ n, RawFamily.closedApps (F n) names args).app _ σ.unop.op ρ
  simp only [RawFamily.iSup_app, RawFamily.closedApps_value]
  exact rawApps_iSup_le_const _ _

end CoherentShape

end Metalean
