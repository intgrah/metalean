/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Inductive
public import Metalean.Syntax.Inductive.Recursor.Substitution
public import Metalean.Semantics.Interpretation.Inductive
public import Metalean.Semantics.Interpretation.Recursor.Telescope

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory Presheaf IndSig TypeTheory TypeTheory.NaturalModel

variable {Γ₁ Γ₂ : CtxCat E ℓ} {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
  {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len} {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
  {mins₁ mins₂ : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}
  {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len} {maj₁ maj₂ : Expr ζ ℓ Γ₁.as.len}
  {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ₁.as.len}
  {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ Γ₁.as.len}

structure IndData (Γ₁ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len) : Prop where
  block : (E.get η).block.WFStrong E
  param (p : Fin ι.nparams) : E[Γ₁.as.ctx] ⊢ₛ ps p : (E.get η).block.paramType ls ps p

structure RecData (Γ₁ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ)
    (l : Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len)
    (ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len) : Prop
    extends IndData Γ₁ η ls ps where
  allowed : (E.get η).block.RecAllowed l
  motive (s₁ : Fin ι.nsorts) : E[Γ₁.as.ctx] ⊢ₛ ms s₁ : (E.get η).block.motiveType η ls ps l s₁
  case (s₁ : Fin ι.nsorts) (c : Fin (ι.nctors s₁)) :
    E[Γ₁.as.ctx] ⊢ₛ mins s₁ c : (E.get η).block.caseFnType η ls ps ms s₁ c

structure RecTyping (Γ₁ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len)
    (ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len)
    (is : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len) (maj : Expr ζ ℓ Γ₁.as.len) : Prop
    extends RecData Γ₁ η ls l ps ms mins where
  index (i : Fin (ι.nindices s)) : E[Γ₁.as.ctx] ⊢ₛ is i : (E.get η).block.indexType ls s ps is i
  major : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is

structure RecDecl (E : Env ζ) (η : Head ζ (.inductive ι)) (l : Level ℓ) : Prop where
  block : (E.get η).block.WFStrong E
  allowed : (E.get η).block.RecAllowed l

abbrev CtxCat.recr (hd : RecDecl E η l) (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts) :
    CtxCat E ℓ :=
  CtxCat.extendTele (CtxCat.nil E ℓ) ((E.get η).block.recrTele η s ls l) hd.block.recrTele

namespace RecData

theorem subst (h : RecData Γ₁ η ls l ps₁ ms₁ mins₁) (σ : Γ₂.as ⟶ Γ₁.as) :
    RecData Γ₂ η ls l (fun p => (ps₁ p).subst σ.subst) (fun s₁ => (ms₁ s₁).subst σ.subst)
      fun s₁ c₁ => (mins₁ s₁ c₁).subst σ.subst where
  block := h.block
  allowed := h.allowed
  param p := by simpa using (h.param p).substitution σ.typed
  motive s₁ := by simpa using (h.motive s₁).substitution σ.typed
  case s₁ c₁ := by simpa using (h.case s₁ c₁).substitution σ.typed

end RecData

namespace RecTyping

theorem left (hB : (E.get η).block.WFStrong E) (hallowed : (E.get η).block.RecAllowed l)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p)
    (hms : ∀ s₁, E[Γ₁.as.ctx] ⊢ₛ ms₁ s₁ ≡ ms₂ s₁ : (E.get η).block.motiveType η ls ps₁ l s₁)
    (hmins : ∀ s₁ c₁, E[Γ₁.as.ctx] ⊢ₛ mins₁ s₁ c₁ ≡ mins₂ s₁ c₁ :
      (E.get η).block.caseFnType η ls ps₁ ms₁ s₁ c₁)
    (his : ∀ i, E[Γ₁.as.ctx] ⊢ₛ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁) :
    RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁ is₁ maj₁ where
  block := hB
  allowed := hallowed
  param p := (hps p).left
  motive s₁ := (hms s₁).left
  case s₁ c₁ := (hmins s₁ c₁).left
  index i := (his i).left
  major := hmaj.left

theorem right (hB : (E.get η).block.WFStrong E) (hallowed : (E.get η).block.RecAllowed l)
    (hΓ : E[Γ₁.as.ctx] ⊢ₛ ok)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p)
    (hms : ∀ s₁, E[Γ₁.as.ctx] ⊢ₛ ms₁ s₁ ≡ ms₂ s₁ : (E.get η).block.motiveType η ls ps₁ l s₁)
    (hmins : ∀ s₁ c₁, E[Γ₁.as.ctx] ⊢ₛ mins₁ s₁ c₁ ≡ mins₂ s₁ c₁ :
      (E.get η).block.caseFnType η ls ps₁ ms₁ s₁ c₁)
    (his : ∀ i, E[Γ₁.as.ctx] ⊢ₛ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i)
    (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁) :
    RecTyping Γ₁ η s ls l ps₂ ms₂ mins₂ is₂ maj₂ where
  block := hB
  allowed := hallowed
  param := (Inductive.paramType_conv hB · hps)
  motive s₁ := (Inductive.motiveType_congr hB hΓ hps).convStrong (hms s₁).right
  case s₁ c₁ := Inductive.caseFnType_conv hB hΓ hps hms (hmins s₁ c₁)
  index := (Inductive.indexType_conv hB · hps his)
  major := (IsTypeEq.ofDefEq (DefeqStrong.indDF hps his)).convStrong hmaj.right

theorem iota (hB : (E.get η).block.WFStrong E) (hallowed : (E.get η).block.RecAllowed l)
    (hΓ : E[Γ₁.as.ctx] ⊢ₛ ok)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ₛ ps₁ p : (E.get η).block.paramType ls ps₁ p)
    (hms : ∀ s₁, E[Γ₁.as.ctx] ⊢ₛ ms₁ s₁ : (E.get η).block.motiveType η ls ps₁ l s₁)
    (hmins : ∀ s₁ c₁, E[Γ₁.as.ctx] ⊢ₛ mins₁ s₁ c₁ : (E.get η).block.caseFnType η ls ps₁ ms₁ s₁ c₁)
    (hfds : ∀ f, E[Γ₁.as.ctx] ⊢ₛ fds f :
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds f)
    (hrecFds : ∀ f, E[Γ₁.as.ctx] ⊢ₛ recFds f :
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds f) :
    RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁
      (fun i => ((E.get η).block.ctors s c).targetIndex ls ps₁ fds i)
      (.ctor η s c ls ps₁ fds recFds) where
  block := hB
  allowed := hallowed
  param := hps
  motive := hms
  case := hmins
  index := ((hB.ctors s c).targetIndex · (Ctor.targetSubstWFStrong hps hfds))
  major :=
    DefeqStrong.ctorDF hps hfds hrecFds
      ((hB.ctors s c).ordinaryFieldExprStrong · hps hfds)
      (fun f => ((hB.ctors s c).recursiveFieldExprStrong rfl f hΓ hps hfds).choose_spec)
      (.indDF hps ((hB.ctors s c).targetIndex · (Ctor.targetSubstWFStrong hps hfds)))

theorem subst (h : RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁ is₁ maj₁) (σ : Γ₂.as ⟶ Γ₁.as) :
    RecTyping Γ₂ η s ls l (fun p => (ps₁ p).subst σ.subst) (fun s₁ => (ms₁ s₁).subst σ.subst)
      (fun s₁ c₁ => (mins₁ s₁ c₁).subst σ.subst) (fun i => (is₁ i).subst σ.subst)
      (maj₁.subst σ.subst) where
  __ := h.toRecData.subst σ
  index i := by simpa using (h.index i).substitution σ.typed
  major := by simpa [Expr.subst] using h.major.substitution σ.typed

theorem toRecDecl (h : RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁ is₁ maj₁) : RecDecl E η l :=
  ⟨h.block, h.allowed⟩

theorem recrSubstWF (h : RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁ is₁ maj₁) :
    E[Γ₁.as.ctx] ⊢ₛ Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁ ⊣
      (CtxCat.recr h.toRecDecl ls s).as.ctx := by
  change E[Γ₁.as.ctx] ⊢ₛ _ ⊣ #t[] ++ _
  rw [Tele.nil_append]
  exact Inductive.forall_recrSubst
    h.param h.motive h.case h.index h.major

def recrHom (h : RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁ is₁ maj₁) :
    Γ₁.as ⟶ (CtxCat.recr h.toRecDecl ls s).as :=
  ⟨Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁, h.recrSubstWF⟩

theorem generic (hd : RecDecl E η l) (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts) :
    RecTyping (CtxCat.recr hd ls s) η s ls l (fun p => .var (RecrBinder.param p).resolve)
      (fun t => .var (RecrBinder.motive t).resolve) (fun t c => .var (RecrBinder.case t c).resolve)
      (fun i => .var (RecrBinder.index i).resolve) (.var RecrBinder.major.resolve) := by
  have hvar (v : Fin (ι.recrEnd s)) : E[(CtxCat.recr hd ls s).as.ctx] ⊢ₛ .var v :
      (Ctx.get v ((E.get η).block.recrTele η s ls l)).subst
        (Inductive.recrSubst (fun p => .var (RecrBinder.param p).resolve)
          (fun t => .var (RecrBinder.motive t).resolve)
          (fun t c => .var (RecrBinder.case t c).resolve)
          (fun i => .var (RecrBinder.index i).resolve) (.var RecrBinder.major.resolve)) := by
    rw [Inductive.recrSubst_vars, Expr.subst_id]
    exact (congrArg (fun Δ => E[(CtxCat.recr hd ls s).as.ctx] ⊢ₛ .var v : Ctx.get v Δ)
      (Tele.nil_append _)).mp ((CtxCat.recr hd ls s).as.wf.var v)
  exact {
    block := hd.block
    allowed := hd.allowed
    param p := by
      have hp := hvar (((p.castAdd ι.nsorts).castAdd (Fin.sum ι.nctors)).castAdd (ι.nindices s)).castSucc
      rwa [Inductive.recrTele_get_param_subst] at hp
    motive t := by
      have hp := hvar (((Fin.natAdd ι.nparams t).castAdd (Fin.sum ι.nctors)).castAdd
        (ι.nindices s)).castSucc
      rwa [Inductive.recrTele_get_motive_subst] at hp
    case t c := by
      have hp := hvar ((Fin.natAdd (ι.nparams + ι.nsorts)
        (Fin.encodeSigma ι.nctors ⟨t, c⟩)).castAdd (ι.nindices s)).castSucc
      rwa [Inductive.recrTele_get_case_subst] at hp
    index i := by
      have hp := hvar (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors) i).castSucc
      rwa [Inductive.recrTele_get_index_subst] at hp
    major := by
      have hp := hvar (Fin.last _)
      rwa [Inductive.recrTele_get_major_subst] at hp }

theorem recrBody_typed (hd : RecDecl E η l) (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts) :
    E[(CtxCat.recr hd ls s).as.ctx] ⊢ₛ
      .recr η s ls l (fun p => .var (RecrBinder.param p).resolve)
        (fun t => .var (RecrBinder.motive t).resolve) (fun t c => .var (RecrBinder.case t c).resolve)
        (fun i => .var (RecrBinder.index i).resolve) (.var RecrBinder.major.resolve) :
      ι.recrBody s :=
  have h := generic hd ls s
  .recrDF h.allowed h.param h.motive h.case h.index h.major
    (Inductive.WFStrong.motiveResult_congr h.block (CtxCat.recr hd ls s).as.wf h.param h.motive
      h.index h.major)

end RecTyping

structure CtorInstance (Γ₁ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len) where
  fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ₁.as.len
  recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ Γ₁.as.len
  typed : CtorTyping Γ₁ η s c ls ps fds recFds

namespace CtorInstance

noncomputable def names (inst : CtorInstance Γ₁ η s c ls ps₁) :
    Fin (CtorHead.mk η s c).arity → Tm_ Γ₁ :=
  inst.typed.names

def ih (inst : CtorInstance Γ₁ η s c ls ps₁) (l : Level ℓ) (ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len)
    (f : Fin (ι.ctors s c).nrecFields) : Expr ζ ℓ Γ₁.as.len :=
  (E.get η).block.iotaIHs η ls l ps₁ ms mins s c inst.fds inst.recFds f

theorem ih_typed (h : RecData Γ₁ η ls l ps₁ ms₁ mins₁)
    (inst : CtorInstance Γ₁ η s c ls ps₁) (f : Fin (ι.ctors s c).nrecFields) :
    E[Γ₁.as.ctx] ⊢ₛ inst.ih l ms₁ mins₁ f :
      ((E.get η).block.ctors s c).ihTypeWith ls ms₁ ps₁ inst.fds inst.recFds f :=
  Ctor.WFStrong.iotaIH (h.block.ctors s c) h.block h.allowed f Γ₁.as.wf h.param h.motive
    h.case inst.typed.ordinary inst.typed.recursive

noncomputable def ihName (h : RecData Γ₁ η ls l ps₁ ms₁ mins₁)
    (inst : CtorInstance Γ₁ η s c ls ps₁) (f : Fin (ι.ctors s c).nrecFields) :
    Tm_ Γ₁ :=
  Tm.label Γ₁.as (inst.ih_typed h f)

end CtorInstance

end Metalean.CoherentShape
