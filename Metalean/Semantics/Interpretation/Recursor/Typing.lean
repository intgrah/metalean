/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Inductive
public import Metalean.Syntax.Inductive.Recursor.Substitution
public import Metalean.Semantics.Interpretation.Inductive
public import Metalean.Semantics.Interpretation.Recursor.Telescope

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory Presheaf IndSig

variable {Γ₁ Γ₂ : CtxCat E ℓ} {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
  {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len} {ms₁ ms₂ : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
  {mins₁ mins₂ : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}
  {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len} {maj₁ maj₂ : Expr ζ ℓ Γ₁.as.len}
  {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ₁.as.len}
  {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ Γ₁.as.len}

structure IndData (Γ₁ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len) : Prop where
  block : InductiveWF E (E.get η).block
  param (p : Fin ι.nparams) : E[Γ₁.as.ctx] ⊢ ps p : (E.get η).block.paramType ls ps p

structure RecDecl (E : Env ζ) (η : Head ζ (.inductive ι)) (l : Level ℓ) : Prop where
  block : InductiveWF E (E.get η).block
  allowed : (E.get η).block.RecAllowed l

structure RecData (Γ₁ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ)
    (l : Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len)
    (ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len) : Prop
    extends IndData Γ₁ η ls ps, RecDecl E η l where
  motive (s₁ : Fin ι.nsorts) : E[Γ₁.as.ctx] ⊢ ms s₁ : (E.get η).block.motiveType η ls ps l s₁
  case (s₁ : Fin ι.nsorts) (c : Fin (ι.nctors s₁)) :
    E[Γ₁.as.ctx] ⊢ mins s₁ c : (E.get η).block.caseFnType η ls ps ms s₁ c

structure RecTyping (Γ₁ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len)
    (ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len)
    (is : Fin (ι.nindices s) → Expr ζ ℓ Γ₁.as.len) (maj : Expr ζ ℓ Γ₁.as.len) : Prop
    extends RecData Γ₁ η ls l ps ms mins where
  index (i : Fin (ι.nindices s)) : E[Γ₁.as.ctx] ⊢ is i : (E.get η).block.indexType ls s ps is i
  major : E[Γ₁.as.ctx] ⊢ maj : .ind η s ls ps is

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

theorem left (hB : InductiveWF E (E.get η).block) (hallowed : (E.get η).block.RecAllowed l)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p)
    (hms : ∀ s₁, E[Γ₁.as.ctx] ⊢ ms₁ s₁ ≡ ms₂ s₁ : (E.get η).block.motiveType η ls ps₁ l s₁)
    (hmins : ∀ s₁ c₁, E[Γ₁.as.ctx] ⊢ mins₁ s₁ c₁ ≡ mins₂ s₁ c₁ :
      (E.get η).block.caseFnType η ls ps₁ ms₁ s₁ c₁)
    (his : ∀ i, E[Γ₁.as.ctx] ⊢ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i)
    (hmaj : E[Γ₁.as.ctx] ⊢ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁) :
    RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁ is₁ maj₁ where
  block := hB
  allowed := hallowed
  param p := (hps p).left
  motive s₁ := (hms s₁).left
  case s₁ c₁ := (hmins s₁ c₁).left
  index i := (his i).left
  major := hmaj.left

theorem right (hB : InductiveWF E (E.get η).block) (hallowed : (E.get η).block.RecAllowed l)
    (hΓ : E[Γ₁.as.ctx] ⊢ ok)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ ps₁ p ≡ ps₂ p : (E.get η).block.paramType ls ps₁ p)
    (hms : ∀ s₁, E[Γ₁.as.ctx] ⊢ ms₁ s₁ ≡ ms₂ s₁ : (E.get η).block.motiveType η ls ps₁ l s₁)
    (hmins : ∀ s₁ c₁, E[Γ₁.as.ctx] ⊢ mins₁ s₁ c₁ ≡ mins₂ s₁ c₁ :
      (E.get η).block.caseFnType η ls ps₁ ms₁ s₁ c₁)
    (his : ∀ i, E[Γ₁.as.ctx] ⊢ is₁ i ≡ is₂ i : (E.get η).block.indexType ls s ps₁ is₁ i)
    (hmaj : E[Γ₁.as.ctx] ⊢ maj₁ ≡ maj₂ : .ind η s ls ps₁ is₁) :
    RecTyping Γ₁ η s ls l ps₂ ms₂ mins₂ is₂ maj₂ where
  block := hB
  allowed := hallowed
  param := (Inductive.paramType_conv hB · hps)
  motive s₁ := (Inductive.motiveType_congr hB hΓ hps).conv (hms s₁).right
  case s₁ c₁ := Inductive.caseFnType_conv hB hΓ hps hms (hmins s₁ c₁)
  index := (Inductive.indexType_conv hB · hps his)
  major := (TypeEq.ofDefEq (Defeq.indDF hps his)).conv hmaj.right

theorem iota (hB : InductiveWF E (E.get η).block) (hallowed : (E.get η).block.RecAllowed l)
    (hΓ : E[Γ₁.as.ctx] ⊢ ok)
    (hps : ∀ p, E[Γ₁.as.ctx] ⊢ ps₁ p : (E.get η).block.paramType ls ps₁ p)
    (hms : ∀ s₁, E[Γ₁.as.ctx] ⊢ ms₁ s₁ : (E.get η).block.motiveType η ls ps₁ l s₁)
    (hmins : ∀ s₁ c₁, E[Γ₁.as.ctx] ⊢ mins₁ s₁ c₁ : (E.get η).block.caseFnType η ls ps₁ ms₁ s₁ c₁)
    (hfds : ∀ f, E[Γ₁.as.ctx] ⊢ fds f :
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps₁ fds f)
    (hrecFds : ∀ f, E[Γ₁.as.ctx] ⊢ recFds f :
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps₁ fds f) :
    RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁
      (fun i => ((E.get η).block.ctors s c).targetIndex ls ps₁ fds i)
      (.ctor η s c ls ps₁ fds recFds) where
  block := hB
  allowed := hallowed
  param := hps
  motive := hms
  case := hmins
  index := ((hB.ctors s c).targetIndex · (Ctor.forall_ordinarySubst le_rfl hps hfds))
  major :=
    Defeq.ctorDF hps hfds hrecFds
      ((hB.ctors s c).ordinaryFieldExpr · hps hfds)
      (fun f => ((hB.ctors s c).recursiveFieldExpr rfl f hΓ hps hfds).choose_spec)
      (.indDF hps ((hB.ctors s c).targetIndex · (Ctor.forall_ordinarySubst le_rfl hps hfds)))

theorem subst (h : RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁ is₁ maj₁) (σ : Γ₂.as ⟶ Γ₁.as) :
    RecTyping Γ₂ η s ls l (fun p => (ps₁ p).subst σ.subst) (fun s₁ => (ms₁ s₁).subst σ.subst)
      (fun s₁ c₁ => (mins₁ s₁ c₁).subst σ.subst) (fun i => (is₁ i).subst σ.subst)
      (maj₁.subst σ.subst) where
  __ := h.toRecData.subst σ
  index i := by simpa using (h.index i).substitution σ.typed
  major := by simpa [Expr.subst] using h.major.substitution σ.typed

def recrHom (h : RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁ is₁ maj₁) :
    Γ₁.as ⟶ (CtxCat.recr h.toRecDecl ls s).as :=
  ⟨Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁, by
    simpa [CtxCat.recr, CtxCat.extendTele, CtxCat.nil] using
      Inductive.forall_recrSubst h.param h.motive h.case h.index h.major⟩

theorem generic (hd : RecDecl E η l) (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts) :
    RecTyping (CtxCat.recr hd ls s) η s ls l (fun p => .var (RecrBinder.param p).resolve)
      (fun t => .var (RecrBinder.motive t).resolve) (fun t c => .var (RecrBinder.case t c).resolve)
      (fun i => .var (RecrBinder.index i).resolve) (.var RecrBinder.major.resolve) := by
  have ht b := (E.get η).block.recrTele_get_subst (s := s) η ls l
    (fun p => .var (RecrBinder.param p).resolve) (fun t => .var (RecrBinder.motive t).resolve)
    (fun t c => .var (RecrBinder.case t c).resolve) (fun i => .var (RecrBinder.index i).resolve)
    (.var RecrBinder.major.resolve) b
  rw [Inductive.recrSubst_vars] at ht
  simp only [Expr.subst_id] at ht
  have hvar (b : RecrBinder ι s) : E[(CtxCat.recr hd ls s).as.ctx] ⊢ .var b.resolve :
      (E.get η).block.recrBinderType η ls l (fun p => .var (RecrBinder.param p).resolve)
        (fun t => .var (RecrBinder.motive t).resolve) (fun i => .var (RecrBinder.index i).resolve) b := by
    rw [← ht b]
    simpa [CtxCat.recr, CtxCat.extendTele, CtxCat.nil] using (CtxCat.recr hd ls s).as.wf.var b.resolve
  exact {
    block := hd.block
    allowed := hd.allowed
    param p := hvar (.param p)
    motive t := hvar (.motive t)
    case t c := hvar (.case t c)
    index i := hvar (.index i)
    major := hvar .major }

theorem typed (h : RecTyping Γ₁ η s ls l ps₁ ms₁ mins₁ is₁ maj₁) :
    E[Γ₁.as.ctx] ⊢ .recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁ : Inductive.motiveResult (ms₁ s) is₁ maj₁ :=
  .recrDF h.allowed h.param h.motive h.case h.index h.major
    (InductiveWF.motiveResult_congr h.block Γ₁.as.wf h.param h.motive h.index h.major)

end RecTyping

structure CtorInstance (Γ₁ : CtxCat E ℓ) (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len) where
  fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ Γ₁.as.len
  recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ Γ₁.as.len
  typed : CtorTyping Γ₁ η s c ls ps fds recFds

namespace CtorInstance

def ih (inst : CtorInstance Γ₁ η s c ls ps₁) (l : Level ℓ) (ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len)
    (f : Fin (ι.ctors s c).nrecFields) : Expr ζ ℓ Γ₁.as.len :=
  (E.get η).block.iotaIHs η ls l ps₁ ms mins s c inst.fds inst.recFds f

theorem ih_typed (h : RecData Γ₁ η ls l ps₁ ms₁ mins₁)
    (inst : CtorInstance Γ₁ η s c ls ps₁) (f : Fin (ι.ctors s c).nrecFields) :
    E[Γ₁.as.ctx] ⊢ inst.ih l ms₁ mins₁ f :
      ((E.get η).block.ctors s c).ihTypeWith ls ms₁ ps₁ inst.fds inst.recFds f :=
  ((h.block.ctors s c).recursive f).iotaIH h.block rfl h.allowed (by simp) Γ₁.as.wf
    h.param h.motive h.case (Ctor.forall_ordinarySubst le_rfl h.param inst.typed.ordinary)
    (inst.typed.recursive f)

noncomputable def ihName (h : RecData Γ₁ η ls l ps₁ ms₁ mins₁)
    (inst : CtorInstance Γ₁ η s c ls ps₁) (f : Fin (ι.ctors s c).nrecFields) :
    Tm_ Γ₁ :=
  Tm.label Γ₁.as (inst.ih_typed h f)

end CtorInstance

end Metalean.CoherentShape
