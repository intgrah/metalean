/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.InstLevel
public import Metalean.Semantics.Interpretation.Recursor.Typing
public import Metalean.TypeTheory.Syntactic.Telescope
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

theorem InductiveWF.ordinaryClosedWF {ι : IndSig} {I : Inductive ζ ι} (hB : InductiveWF E I)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ) (count : Nat)
    (hcount : count ≤ (ι.ctors s c).nfields) :
    E[(I.params ++ (I.ctors s c).ordinaryTeleAux count hcount){ls}] ⊢ ok := by
  have htele : TeleWF E I.LevelOK ((#t[] : Ctx ζ ι.nlevels 0 0) ++ I.params)
      ((I.ctors s c).ordinaryTeleAux count hcount) := by
    simpa using (hB.ctors s c).ordinaryTeleAux count hcount
  simpa using
    ((hB.params.append (htele.mono fun _ => trivial)).instLevel (Q := fun _ => True) ls
      fun _ => trivial).appendCtxWF .nil

theorem Inductive.paramType_var {k : Nat} {ι : IndSig} {I : Inductive ζ ι}
    {ls : Fin ι.nlevels → Level ℓ} {Δ : Ctx ζ ι.nlevels ι.nparams (ι.nparams + k)}
    (p : Fin ι.nparams) :
    E[(I.params ++ Δ){ls}] ⊢ ok →
    E[(I.params ++ Δ){ls}] ⊢ .var (p.castAdd k) :
      I.paramType ls (fun q => .var (q.castAdd k)) p := by
  intro hΓ
  have hv := SubstWF.id hΓ (p.castAdd k)
  have hrestrict : (fun w : Var p.val =>
      Subst.id (w.castLE (show p.val ≤ ι.nparams + k by omega))) =
      fun w : Var p.val =>
        (Expr.var ((w.castLE (show p.val ≤ ι.nparams by omega)).castAdd k) :
          Expr ζ ℓ (ι.nparams + k)) :=
    funext fun _ => congrArg Expr.var (Fin.ext rfl)
  rw [Ctx.get_subst _ _ (p.castAdd k) p.val (by omega) rfl, hrestrict] at hv
  simpa [Inductive.paramType, Subst.id] using hv

theorem SubstWF.wkN {n m k : Nat} {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m}
    {Δ : Ctx ζ ℓ m (m + k)} {σ : Subst ζ ℓ n m} :
    E[Γ₂] ⊢ σ ⊣ Γ₁ →
    E[Γ₂ ++ Δ] ⊢ (fun v => (σ v).wkN k) ⊣ Γ₁ := by
  intro hσ v
  have heq : ((Γ₁.get v).subst σ).wkN k = (Γ₁.get v).subst fun w => (σ w).wkN k := by
    simp only [Expr.wkN_eq_rename, Expr.subst_rename]
    rfl
  have hv : E[Γ₂ ++ Δ] ⊢ (σ v).wkN k : ((Γ₁.get v).subst σ).wkN k := (hσ v).wkN
  rwa [heq] at hv

namespace CoherentShape

open CategoryTheory Presheaf

variable {Γ₁ Γ₂ : CtxCat E ℓ} {ι : IndSig} {η : Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Level ℓ}
  {l : Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len}


section

variable (E : Env ζ) (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ)
  (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields)

abbrev recursiveSourceTele :
    Ctx ζ ℓ (ι.nparams + (ι.ctors s c).nfields)
      (ι.nparams + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields) :=
  ((E.get η).block.ctors s c).recursiveFieldTele η ls
    (fun p => ((Subst.id : Subst ζ ℓ ι.nparams ι.nparams) p).wkN (ι.ctors s c).nfields)
    (Expr.boundVars ι.nparams (ι.ctors s c).nfields 0)

theorem recursiveSourceTele_subst {n : Nat} (ps : Fin ι.nparams → Expr ζ ℓ n) :
    Ctx.substN (Subst.liftN ps (ι.ctors s c).nfields) (ι.ctors s c).nrecFields
        (recursiveSourceTele E η ls s c) =
      ((E.get η).block.ctors s c).recursiveFieldTele η ls
        (fun p => (ps p).wkN (ι.ctors s c).nfields)
        (Expr.boundVars n (ι.ctors s c).nfields 0) := by
  rw [Ctor.recursiveFieldTeleAux_subst]
  erw [Expr.boundVars_subst ps (ι.ctors s c).nfields 0]
  simp [Subst.id, Expr.subst]

end

variable (h : IndData Γ₁ η ls ps) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
  (f : Fin (ι.ctors s c).nrecFields)

abbrev CtxCat.ctorSource : CtxCat E ℓ :=
  ⟨((E.get η).block.params ++ ((E.get η).block.ctors s c).ordinaryTele){ls},
    h.block.ordinaryClosedWF s c ls _ le_rfl⟩

theorem recursiveSourceTele_wf :
    TeleWF E (fun _ => True) (CtxCat.ctorSource h s c).as.ctx (recursiveSourceTele E η ls s c) := by
  let := Subst.category ζ ℓ
  have hparams := h.block.paramClosedWF ls
  have hfield := (h.block.ctors s c).fieldTele rfl hparams
    (ps := (Subst.id : Subst ζ ℓ ι.nparams ι.nparams))
    (fun p => Inductive.paramType_var (k := 0) (Δ := #t[]) p hparams)
  have hsplit := (TeleWF.of_append hfield).2
  have hctx : (E.get η).block.params{ls} ++
      ((E.get η).block.ctors s c).ordinaryFieldTele η ls (Subst.id : Subst ζ ℓ ι.nparams ι.nparams) =
      ((E.get η).block.params ++ ((E.get η).block.ctors s c).ordinaryTele){ls} :=
    (congrArg ((E.get η).block.params{ls} ++ ·)
      ((Ctx.substFunctor _).map_id_apply _ _)).trans
    (Ctx.instL_append _ _ _).symm
  rwa [hctx] at hsplit

theorem sourceTelescope_wf :
    TeleWF E (fun _ => True) (CtxCat.ctorSource h s c).as.ctx (((E.get η).block.ctors s c).recursive f).tele{ls} :=
  ((h.block.ctors s c).recursive f).tele.instLevel ls fun _ => trivial

abbrev CtxCat.sourceFieldTarget : CtxCat E ℓ :=
  CtxCat.extendTele (CtxCat.ctorSource h s c) (((E.get η).block.ctors s c).recursive f).tele{ls}
    (sourceTelescope_wf h s c f)

theorem sourceIndexTyping (i : Fin (ι.nindices ((ι.ctors s c).recursiveTarget f))) :
    E[(CtxCat.sourceFieldTarget h s c f).as.ctx] ⊢ (((E.get η).block.ctors s c).recursive f).indices{ls} i :
      (E.get η).block.indexType ls ((ι.ctors s c).recursiveTarget f)
        (fun p => ((Expr.var (p.castAdd (ι.ctors s c).nfields))).wkN ((ι.ctors s c).recursiveArity f))
        (((E.get η).block.ctors s c).recursive f).indices{ls} i := by
  have hi := ((h.block.ctors s c).recursive f).instantiatedIndices
    (fun _ => rfl) i (SubstWF.id (CtxCat.ctorSource h s c).as.wf)
  simp only [RecField.instantiatedTelescope_id, RecField.instantiatedIndices_id] at hi
  exact hi

abbrev CtxCat.ctorFields : CtxCat E ℓ :=
  CtxCat.extendTele Γ₁ (((E.get η).block.ctors s c).fieldTele η ls ps)
    ((h.block.ctors s c).fieldTele rfl Γ₁.as.wf h.param)

def CtxCat.ctorFieldsProjection : (CtxCat.ctorFields h s c).as ⟶ Γ₁.as :=
  RawCtx.Hom.teleProjection ((h.block.ctors s c).fieldTele rfl Γ₁.as.wf h.param)

def CtxCat.ctorFieldsHom : (CtxCat.ctorFields h s c).as ⟶ (CtxCat.ctorSource h s c).as where
  subst := Fin.append ((ι.ctors s c).fieldParams ps) (ι.ctors s c).fieldOrdinary
  typed := (h.block.ctors s c).fieldTargetSubst h.param

abbrev fieldTelescope :
    Ctx ζ ℓ (CtxCat.ctorFields h s c).as.len
      ((CtxCat.ctorFields h s c).as.len + (ι.ctors s c).recursiveArity f) :=
  (((E.get η).block.ctors s c).recursive f).instantiatedTelescope ls
    (Fin.append ((ι.ctors s c).fieldParams ps) (ι.ctors s c).fieldOrdinary)

theorem fieldTelescope_wf :
    TeleWF E (fun _ => True) (CtxCat.ctorFields h s c).as.ctx (fieldTelescope h s c f) :=
  (sourceTelescope_wf h s c f).substitution (CtxCat.ctorFieldsHom h s c).typed

abbrev CtxCat.ctorFieldTarget : CtxCat E ℓ :=
  CtxCat.extendTele (CtxCat.ctorFields h s c) (fieldTelescope h s c f) (fieldTelescope_wf h s c f)

def fieldIndices :
    Fin (ι.nindices ((ι.ctors s c).recursiveTarget f)) →
      Expr ζ ℓ (CtxCat.ctorFieldTarget h s c f).as.len :=
  (((E.get η).block.ctors s c).recursive f).instantiatedIndices ls
    (Fin.append ((ι.ctors s c).fieldParams ps) (ι.ctors s c).fieldOrdinary)

def appliedMajor : Expr ζ ℓ (CtxCat.ctorFieldTarget h s c f).as.len :=
  ((ι.ctors s c).fieldRecursive f).applyBound ((ι.ctors s c).recursiveArity f)

theorem appliedMajor_typed :
    E[(CtxCat.ctorFieldTarget h s c f).as.ctx] ⊢ appliedMajor h s c f :
      .ind η ((ι.ctors s c).recursiveTarget f) ls
        (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
        (fieldIndices h s c f) := by
  have hfield := (h.block.ctors s c).fieldRecursive f Γ₁.as.wf h.param
  rw [RecField.instantiatedType] at hfield
  have ⟨_, hpi⟩ := hfield.regular
  have ⟨_, _, hind⟩ := Ctx.pi_isType_inv _ (CtxCat.ctorFields h s c).as.wf hpi
  exact Ctx.pi_applyBound (CtxCat.ctorFieldTarget h s c f).as.wf hind hfield

theorem indexTyping (i : Fin (ι.nindices ((ι.ctors s c).recursiveTarget f))) :
    E[(CtxCat.ctorFieldTarget h s c f).as.ctx] ⊢ fieldIndices h s c f i :
      (E.get η).block.indexType ls ((ι.ctors s c).recursiveTarget f)
        (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
        (fieldIndices h s c f) i :=
  ((h.block.ctors s c).recursive f).instantiatedIndices (fun p => Fin.append_left _ _ p) i
    ((h.block.ctors s c).fieldTargetSubst h.param)

def CtxCat.ctorFieldTargetHom : (CtxCat.ctorFieldTarget h s c f).as ⟶ Γ₁.as where
  subst v := ((CtxCat.ctorFieldsProjection h s c).subst v).wkN ((ι.ctors s c).recursiveArity f)
  typed := SubstWF.wkN (CtxCat.ctorFieldsProjection h s c).typed

theorem CtxCat.ctorFieldsHom_subst :
    (CtxCat.ctorFieldsHom h s c).subst =
      fun v => (Subst.liftN ps (ι.ctors s c).nfields v).wkN (ι.ctors s c).nrecFields := by
  funext v
  cases v using Fin.addCases with
  | left p => simp [CtxCat.ctorFieldsHom, CtorSig.fieldParams]
  | right f => simp [CtxCat.ctorFieldsHom, CtorSig.fieldOrdinary]

theorem CtxCat.ctorFieldTargetHom_param (e : Expr ζ ℓ Γ₁.as.len) :
    e.subst (CtxCat.ctorFieldTargetHom h s c f).subst =
      ((e.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields).wkN
        ((ι.ctors s c).recursiveArity f) := by
  simp only [CtxCat.ctorFieldTargetHom, CtxCat.ctorFieldsProjection,
    RawCtx.Hom.teleProjection, Expr.var_wkN]
  simp [Expr.wkN_eq_rename]
  rfl

theorem ctorFieldTargetHom_params :
    (fun p => (ps p).subst (CtxCat.ctorFieldTargetHom h s c f).subst) =
      fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f) :=
  funext fun p => CtxCat.ctorFieldTargetHom_param h s c f (ps p)

def CtorInstance.generic :
    CtorInstance (CtxCat.ctorFields h s c) η s c ls ((ι.ctors s c).fieldParams ps) where
  fds := (ι.ctors s c).fieldOrdinary
  recFds := (ι.ctors s c).fieldRecursive
  typed.ordinary := ((h.block.ctors s c).fieldOrdinary · h.param)
  typed.recursive := ((h.block.ctors s c).fieldRecursive · Γ₁.as.wf h.param)

theorem CtorInstance.generic_ih_eq_lam (ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len) :
    (generic h s c).ih l
      (fun s₁ => ((ms s₁).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
      (fun s₁ c₁ => ((mins s₁ c₁).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) f =
      (fieldTelescope h s c f).lam
        (.recr η ((ι.ctors s c).recursiveTarget f) ls l
          (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
          (fun s₁ => (ms s₁).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
          (fun s₁ c₁ => (mins s₁ c₁).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
          (fieldIndices h s c f) (appliedMajor h s c f)) := by
  simp only [CtxCat.ctorFieldTargetHom_param]
  cases ((E.get η).block.ctors s c).recursive f
  rfl

theorem CtorInstance.generic_ihType_eq_pi (ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len) :
    ((E.get η).block.ctors s c).ihTypeWith ls
      (fun s₁ => ((ms s₁).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
      ((ι.ctors s c).fieldParams ps) (ι.ctors s c).fieldOrdinary (ι.ctors s c).fieldRecursive f =
      (fieldTelescope h s c f).pi
        (Inductive.motiveResult
          ((ms ((ι.ctors s c).recursiveTarget f)).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
          (fieldIndices h s c f) (appliedMajor h s c f)) := by
  simp only [Ctor.ihTypeWith, CtxCat.ctorFieldTargetHom_param, fieldTelescope, fieldIndices]
  cases ((E.get η).block.ctors s c).recursive f
  rfl

end CoherentShape

namespace CoherentShape

variable {Γ₁ Γ₂ : CtxCat E ℓ} {ι : IndSig} {η : Head ζ (.inductive ι)} {ls : Fin ι.nlevels → Level ℓ}
  {l : Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len} {ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}
  (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
  (f : Fin (ι.ctors s c).nrecFields)

theorem RecData.fields :
    RecData (CtxCat.ctorFields h.toIndData s c) η ls l ((ι.ctors s c).fieldParams ps)
      (fun s₁ => ((ms s₁).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
      fun s₁ c₁ => ((mins s₁ c₁).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields where
  block := h.block
  allowed := h.allowed
  param := (CtorWF.fieldParams _ · h.param)
  motive := (CtorWF.fieldMotive _ · h.motive)
  case := (CtorWF.fieldCase _ · · h.case)

theorem RecData.ihTyping :
    RecTyping (CtxCat.ctorFieldTarget h.toIndData s c f) η ((ι.ctors s c).recursiveTarget f) ls l
      (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
      (fun s₁ => (ms s₁).subst (CtxCat.ctorFieldTargetHom h.toIndData s c f).subst)
      (fun s₁ c₁ => (mins s₁ c₁).subst (CtxCat.ctorFieldTargetHom h.toIndData s c f).subst)
      (fieldIndices h.toIndData s c f) (appliedMajor h.toIndData s c f) := by
  have h' := h.subst (CtxCat.ctorFieldTargetHom h.toIndData s c f)
  rw [ctorFieldTargetHom_params] at h'
  exact ⟨h', indexTyping h.toIndData s c f, appliedMajor_typed h.toIndData s c f⟩

end CoherentShape

end Metalean
