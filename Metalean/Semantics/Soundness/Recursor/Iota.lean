/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Soundness.Recursor.Typing
public import Metalean.Semantics.Soundness.Telescope.Section
import Metalean.Semantics.Interpretation.Computation
import Metalean.Semantics.Soundness.Constructor.Fields
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean

open CategoryTheory Presheaf CoherentShape CodeAssignment IndSig

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {Γ₁ Γ₂ Γ₃ : CtxCat E₂ ℓ}
  {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len} {ms : Fin ι.nsorts → Expr ζ₂ ℓ Γ₁.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ ℓ Γ₁.as.len}
  {ps₂ : Fin ι.nparams → Expr ζ₂ ℓ Γ₂.as.len} {ms₂ : Fin ι.nsorts → Expr ζ₂ ℓ Γ₂.as.len}
  {mins₂ : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ ℓ Γ₂.as.len}
  (inst : CtorInstance Γ₂ η s c ls ps₂)

theorem CoherentShape.CtorInstance.fields_admissible (h : IndData Γ₁ η ls ps) (σ₁ : Γ₂.as ⟶ Γ₁.as)
    (hps : ∀ p, (ps p).subst σ₁.subst = ps₂ p)
    (pfield : RawTeleProperties E₂ Γ₁.as.ctx (((E₂.get η).block.ctors s c).fieldTele η ls ps))
    (pf : ∀ f, RawTyped Γ₂ (inst.fds f) (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps₂ inst.fds f))
    (prf : ∀ f, RawTyped Γ₂ (inst.recFds f)
      (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps₂ inst.fds f))
    (σ₂ : Γ₃ ⟶ Γ₂) (ρ₁ ρ₂ : RawValuation Γ₃) (hsub : SemanticSubstitution σ₁ σ₂ ρ₁ ρ₂)
    (hsource : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁) ρ₁) (hρ : SourceAdmissible σ₂ ρ₂) :
    SemanticSubstitution (inst.fieldsHom h σ₁ hps) σ₂
        (ρ₁.pushFin fun i => (rawInterpret (piLimit E₂ ℓ) Γ₂ (Fin.append inst.fds inst.recFds i)).app _ σ₂.op ρ₂)
        ρ₂ ∧
      SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map (inst.fieldsHom h σ₁ hps))
        (ρ₁.pushFin fun i => (rawInterpret (piLimit E₂ ℓ) Γ₂ (Fin.append inst.fds inst.recFds i)).app _ σ₂.op ρ₂) := by
  have hΔ := (h.block.ctors s c).fieldTele rfl Γ₁.as.wf h.param
  have hproj : inst.fieldsHom h σ₁ hps ≫ RawCtx.Hom.teleProjection hΔ = σ₁ :=
    RawCtx.Hom.ext (funext fun v => inst.fieldsSubst_base h σ₁ v)
  have hvar (i : Fin (CtorHead.mk η s c).arity) :
      inst.fieldsSubst σ₁ (fieldVar h s c i) = Fin.append inst.fds inst.recFds i := by
    cases i using Fin.addCases with
    | left f => exact (inst.fieldsSubst_ordinary h σ₁ f).trans (Fin.append_left _ _ f).symm
    | right f => exact (inst.fieldsSubst_recursive h σ₁ f).trans (Fin.append_right _ _ f).symm
  have ⟨hs, ha⟩ := pfield.extend_admissible (k := (CtorHead.mk η s c).arity) _
    (by simp only [CtorHead.arity, CtorHead.sig]; omega) hΔ (inst.fieldsHom h σ₁ hps)
    (fun i => by
      change RawInterpretationProperties Γ₂ (inst.fieldsSubst σ₁ (fieldVar h s c i))
      rw [hvar]
      cases i using Fin.addCases with
      | left f => rw [Fin.append_left]; exact (pf f).term
      | right f => rw [Fin.append_right]; exact (prf f).term)
    (fun i => by
      change HasFixedness Γ₂ (inst.fieldsSubst σ₁ (fieldVar h s c i))
        ((Ctx.get (fieldVar h s c i) (CtxCat.ctorFields h s c).as.ctx).subst (inst.fieldsSubst σ₁))
      cases i using Fin.addCases with
      | left f =>
        rw [inst.fieldsSubst_ordinary h σ₁ f, CtxCat.ctorFields_get_ordinary,
          inst.ordinaryFieldExpr_fieldsSubst σ₁ hps]
        exact (pf f).fixed
      | right f =>
        rw [inst.fieldsSubst_recursive h σ₁ f, CtxCat.ctorFields_get_recursive,
          inst.recursiveFieldExpr_fieldsSubst σ₁ hps]
        exact (prf f).fixed)
    σ₂ ρ₁ ρ₂ (by rwa [hproj]) (by rwa [hproj]) hρ
  have hv : (fun i : Fin (CtorHead.mk η s c).arity => (rawInterpret (piLimit E₂ ℓ) Γ₂
      (inst.fieldsSubst σ₁ (fieldVar h s c i))).app _ σ₂.op ρ₂) =
      fun i => (rawInterpret (piLimit E₂ ℓ) Γ₂ (Fin.append inst.fds inst.recFds i)).app _ σ₂.op ρ₂ :=
    funext fun i => by rw [hvar]
  rw [← hv]
  exact ⟨hs, ha⟩

variable (σ₁ : Γ₂.as ⟶ Γ₁.as) (hps : ∀ p, (ps p).subst σ₁.subst = ps₂ p)
  (hidx : ∀ i, E₂[Γ₂.as.ctx] ⊢ₛ ((E₂.get η).block.ctors s c).targetIndex ls ps₂ inst.fds i :
    (E₂.get η).block.indexType ls s ps₂ (((E₂.get η).block.ctors s c).targetIndex ls ps₂ inst.fds) i)

include hps in
theorem CoherentShape.CtorInstance.recovery_index_name (h : IndData Γ₁ η ls ps)
    (f : Fin (ι.ctors s c).nfields) (i : Fin (ι.nindices s))
    (hi : ((E₂.get η).block.ctors s c).recoveryIndex f = some i) :
    inst.names (Fin.castAdd (ι.ctors s c).nrecFields f) = Tm.label Γ₂.as (hidx i) := by
  have ht := (h.block.ctors s c).targetIndex i
    (Ctor.targetSubstWFStrong (fun p => Ctor.WFStrong.fieldParams _ p h.param)
      (CtorInstance.generic h s c).typed.ordinary)
  have he : ((E₂.get η).block.ctors s c).targetIndex ls ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary i =
      .var (fieldVar h s c (Fin.castAdd (ι.ctors s c).nrecFields f)) := by
    rw [Ctor.targetIndex_recovery hi]
    simp [CtorSig.fieldOrdinary, fieldVar, Fin.natAdd]
  have hmap : Tm.label Γ₂.as (ht.substitution (inst.fieldsHom h σ₁ hps).typed) =
      inst.names (Fin.castAdd (ι.ctors s c).nrecFields f) :=
    (Tm.map_label ht (inst.fieldsHom h σ₁ hps)).symm.trans
      ((congrArg ((Tm E₂ ℓ).map (RawCtx.toCtx.map (inst.fieldsHom h σ₁ hps)).op)
        (Tm.label_eq_var ht he)).trans (inst.map_fieldsHom_fieldVar h σ₁ hps _))
  rw [← hmap]
  have hterm (j : Fin (ι.nindices s)) :
      (((E₂.get η).block.ctors s c).targetIndex ls ((ι.ctors s c).fieldParams ps)
        (CtorInstance.generic h s c).fds j).subst (inst.fieldsSubst σ₁) =
      ((E₂.get η).block.ctors s c).targetIndex ls ps₂ inst.fds j := by
    simp [CtorInstance.generic, CtorInstance.fieldsSubst, Expr.boundVars, Expr.subst, hps]
  have htype : ((E₂.get η).block.indexType ls s ((ι.ctors s c).fieldParams ps)
      (fun j => ((E₂.get η).block.ctors s c).targetIndex ls ((ι.ctors s c).fieldParams ps)
        (CtorInstance.generic h s c).fds j) i).subst (inst.fieldsSubst σ₁) =
      (E₂.get η).block.indexType ls s ps₂ (((E₂.get η).block.ctors s c).targetIndex ls ps₂ inst.fds) i := by
    simp only [Inductive.indexType_subst, hterm]
    simp [CtorSig.fieldParams, CtorInstance.fieldsSubst, hps]
  refine Tm.label_eq_iff.mpr ⟨?_, ?_⟩
  · rw [CtorInstance.fieldsHom_subst, htype]
    exact IsTypeStrong.isTypeEq (hidx i).regular
  · rw [CtorInstance.fieldsHom_subst, htype, hterm]
    exact hidx i

include hps in
theorem CoherentShape.CtorInstance.recoveryNames (h : RecData Γ₁ η ls l ps ms mins) (hrel : l.rel = true)
    (herased : (E₂.get η).block.level.inst ls = .zero) :
    RecoveryNames η s c ls (fun i => Tm.label Γ₂.as (hidx i)) inst.names := by
  intro f hf
  have ⟨i, hi⟩ := Ctor.recoveryIndex_exists (h.recovery_eligible hrel herased s c).2 ls f hf
  exact ⟨i, hi, inst.recovery_index_name σ₁ hps hidx h.toIndData f i hi⟩

include hps in
theorem proofConstructor_instance (h : RecData Γ₁ η ls l ps ms mins) (hrel : l.rel = true)
    (herased : (E₂.get η).block.level.inst ls = .zero) (σ₂ : Γ₃ ⟶ Γ₂)
    (indices : Fin (ι.nindices s) → RawValue Γ₃) :
    proofConstructor h s (σ₂ ≫ RawCtx.toCtx.map σ₁)
        (fun i => (Tm E₂ ℓ).map σ₂.op (Tm.label Γ₂.as (hidx i))) indices =
      RawValue.ctor ⟨η, s, c⟩ (fun f => (Tm E₂ ℓ).map σ₂.op (inst.names f))
        (recoveredField η s c ls indices) := by
  have hn := inst.recoveryNames σ₁ hps hidx h hrel herased
  have hsingle := (h.recovery_eligible hrel herased s c).1
  ext Γ₄ σ₃ y
  have hnames := hn.map (σ₃ ≫ σ₂)
  let sect := ((inst.section h σ₁ hps).pullback (σ₃ ≫ σ₂)).congr
    (Category.assoc σ₃ σ₂ (RawCtx.toCtx.map σ₁))
  have hsect : sect.names = fun f => (Tm E₂ ℓ).map (σ₃ ≫ σ₂).op (inst.names f) := by
    simp [sect]
  have hrhs :
      (RawValue.ctor ⟨η, s, c⟩ (fun f => (Tm E₂ ℓ).map σ₂.op (inst.names f))
        (recoveredField η s c ls indices)).mem σ₃ y ↔
      (RawValue.ctor ⟨η, s, c⟩ (fun f => (Tm E₂ ℓ).map (σ₃ ≫ σ₂).op (inst.names f))
        (recoveredField η s c ls fun i => (indices i).pullback σ₃)).mem (𝟙 Γ₄) y := by
    rw [← ΩLower.presheaf_map_mem_id, RawValue.pullback_ctor]
    simp [pullback_recoveredField]
  rw [hrhs]
  constructor
  · rintro (hy | ⟨c', sect', hn', hy⟩)
    · exact ΩLower.lower _ _ hy (ΩLower.bottom _ _)
    · have hc : c' = c := Fin.ext (by have := c'.isLt; have := c.isLt; omega)
      subst c'
      have hn' : RecoveryNames η s c ls
          (fun i => (Tm E₂ ℓ).map (σ₃ ≫ σ₂).op (Tm.label Γ₂.as (hidx i))) sect'.names := by
        simpa using hn'
      have he := CtorSection.names_eq_recovery h herased sect' sect hn' (by rwa [hsect])
      rwa [he, hsect] at hy
  · intro hy
    refine Or.inr ⟨c, sect, ?_, ?_⟩
    · rw [hsect]
      simpa using hnames
    · rwa [hsect]

variable (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁) (hblock : (E₂.get η).block = I.map pre.sigs)

include hsound hB hblock

theorem RawSound.genericIHProperties (h : RecData Γ₁ η ls l ps ms mins) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ t, RawTyped Γ₁ (ms t) ((E₂.get η).block.motiveType η ls ps l t))
    (pmins : ∀ t c, RawTyped Γ₁ (mins t c) ((E₂.get η).block.caseFnType η ls ps ms t c))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields) :
    RawInterpretationProperties (CtxCat.ctorFields h.toIndData s c)
        ((CtorInstance.generic h.toIndData s c).ih l
          (fun t => ((ms t).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
          (fun t c₁ => ((mins t c₁).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) f) ∧
      HasFixedness (CtxCat.ctorFields h.toIndData s c)
        ((CtorInstance.generic h.toIndData s c).ih l
          (fun t => ((ms t).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
          (fun t c₁ => ((mins t c₁).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) f)
        (((E₂.get η).block.ctors s c).ihType ls ps ms f) := by
  let g := CtxCat.ctorFieldTargetHom h.toIndData s c f
  have h' := h.ihTyping s c f
  have pargs := hsound.fieldTargetArgProperties hB hblock s c h.toIndData hR pps pms pmins f
  have fargs := Inductive.forall_recrSubst
    (motive := fun _ e _ t => HasFixedness (CtxCat.ctorFieldTarget h.toIndData s c f) e t)
    (ps₂ := fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
    (ms₂ := fun t => (ms t).subst g.subst) (mins₂ := fun t c₁ => (mins t c₁).subst g.subst)
    (is₂ := fieldIndices h.toIndData s c f) (maj₂ := appliedMajor h.toIndData s c f)
    (fun p => by
      have ⟨_, _, hf⟩ := (pps p).ctorFieldTarget_properties h.toIndData s c f
      rwa [Inductive.paramType_subst, ctorFieldTargetHom_params, CtxCat.ctorFieldTargetHom_param] at hf)
    (fun t => by
      have ⟨_, _, hf⟩ := (pms t).ctorFieldTarget_properties h.toIndData s c f
      rwa [Inductive.motiveType_subst, ctorFieldTargetHom_params] at hf)
    (fun t c₁ => by
      have ⟨_, _, hf⟩ := (pmins t c₁).ctorFieldTarget_properties h.toIndData s c f
      rwa [Inductive.caseFnType_subst, ctorFieldTargetHom_params] at hf)
    (fun i => (hsound.fieldIndexProperties hB hblock s c h.toIndData f pps i).2)
    (hsound.appliedMajorProperties hB hblock s c h.toIndData hR pps f).2
  have pe : RawInterpretationProperties (CtxCat.ctorFieldTarget h.toIndData s c f)
      (.recr η ((ι.ctors s c).recursiveTarget f) ls l
        (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
        (fun t => (ms t).subst g.subst) (fun t c₁ => (mins t c₁).subst g.subst)
        (fieldIndices h.toIndData s c f) (appliedMajor h.toIndData s c f)) :=
    ⟨hsound.recr_ideal hB hblock h' fun v => (pargs v).ideal, HasSubstitution.recr h' fun v => (pargs v).subst⟩
  have fe : HasFixedness _ _ _ := hsound.recr_fixed hB hblock h' pargs fargs
  have pΔ := hsound.fieldTelescopeProperties hB hblock s c h.toIndData f pps
  have pmr := hsound.recursiveMotiveResult hB hblock s c h.toIndData hR pps pms f
  have he : E₂[(CtxCat.ctorFieldTarget h.toIndData s c f).as.ctx] ⊢ₛ
      .recr η ((ι.ctors s c).recursiveTarget f) ls l
        (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
        (fun t => (ms t).subst g.subst) (fun t c₁ => (mins t c₁).subst g.subst)
        (fieldIndices h.toIndData s c f) (appliedMajor h.toIndData s c f) :
      Inductive.motiveResult ((ms ((ι.ctors s c).recursiveTarget f)).subst g.subst)
        (fieldIndices h.toIndData s c f) (appliedMajor h.toIndData s c f) :=
    .recrDF h'.allowed h'.param h'.motive h'.case h'.index h'.major
      (Inductive.WFStrong.motiveResult_congr h'.block (CtxCat.ctorFieldTarget h.toIndData s c f).as.wf
        h'.param h'.motive h'.index h'.major)
  rw [CtorInstance.generic_ih_eq_lam h.toIndData s c f ms mins, Ctor.ihType,
    CtorInstance.generic_ihType_eq_pi h.toIndData s c f ms]
  exact ⟨RawInterpretationProperties.ctxLam _ rfl (fieldTelescopeStrong h.toIndData s c f) pΔ _ pe,
    HasFixedness.ctxLam _ rfl (fieldTelescopeStrong h.toIndData s c f) pΔ _ _ pmr.syntactic.left he
      pmr.left.ideal pe.ideal fe⟩

theorem RawSound.ihProperties (h : RecData Γ₁ η ls l ps ms mins) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ t, RawTyped Γ₁ (ms t) ((E₂.get η).block.motiveType η ls ps l t))
    (pmins : ∀ t c, RawTyped Γ₁ (mins t c) ((E₂.get η).block.caseFnType η ls ps ms t c))
    (σ₁ : Γ₂.as ⟶ Γ₁.as) (hps : ∀ p, (ps p).subst σ₁.subst = ps₂ p)
    (hms : ∀ t, (ms t).subst σ₁.subst = ms₂ t) (hmins : ∀ t c, (mins t c).subst σ₁.subst = mins₂ t c)
    (pσ₁ : ∀ v, HasSubstitution Γ₂ (σ₁.subst v))
    (hσ₁ : ∀ ⦃Γ₃ : CtxCat E₂ ℓ⦄ (σ₃ : Γ₃ ⟶ Γ₂) (ρ₂ : RawValuation Γ₃), SourceAdmissible σ₃ ρ₂ →
      ∃ ρ₁, SemanticSubstitution σ₁ σ₃ ρ₁ ρ₂ ∧ SourceAdmissible (σ₃ ≫ RawCtx.toCtx.map σ₁) ρ₁)
    (pf : ∀ f, RawTyped Γ₂ (inst.fds f) (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps₂ inst.fds f))
    (prf : ∀ f, RawTyped Γ₂ (inst.recFds f)
      (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps₂ inst.fds f))
    (f : Fin (ι.ctors s c).nrecFields) :
    RawInterpretationProperties Γ₂ (inst.ih l ms₂ mins₂ f) ∧
      HasFixedness Γ₂ (inst.ih l ms₂ mins₂ f)
        (((E₂.get η).block.ctors s c).ihTypeWith ls ms₂ ps₂ inst.fds inst.recFds f) := by
  have ⟨pe, fe⟩ := hsound.genericIHProperties hB hblock h hR pps pms pmins s c f
  have pt := hsound.ihTypeProperties hB hblock s c h.toIndData hR pps pms f
  have pfield := (hsound.fieldTeleProperties hB hblock s c h.toIndData pps).1
  let σ₂ := inst.fieldsHom h.toIndData σ₁ hps
  have pσ₂ (v : Var (CtxCat.ctorFields h.toIndData s c).as.len) : HasSubstitution Γ₂ (σ₂.subst v) := by
    cases v using Fin.addCases with
    | left v =>
      cases v using Fin.addCases with
      | left v =>
        change HasSubstitution Γ₂ (inst.fieldsSubst σ₁ (baseVar h.toIndData s c v))
        rw [inst.fieldsSubst_base h.toIndData σ₁ v]
        exact pσ₁ v
      | right f =>
        change HasSubstitution Γ₂ (inst.fieldsSubst σ₁ (fieldVar h.toIndData s c (Fin.castAdd _ f)))
        rw [inst.fieldsSubst_ordinary h.toIndData σ₁ f]
        exact (pf f).term.subst
    | right f =>
      change HasSubstitution Γ₂ (inst.fieldsSubst σ₁ (Fin.natAdd _ f))
      rw [← fieldVar_natAdd h.toIndData s c f, inst.fieldsSubst_recursive h.toIndData σ₁ f]
      exact (prf f).term.subst
  have hσ₂ ⦃Γ₃ : CtxCat E₂ ℓ⦄ (σ₃ : Γ₃ ⟶ Γ₂) (ρ₂ : RawValuation Γ₃) (hρ : SourceAdmissible σ₃ ρ₂) :
      ∃ ρs, SemanticSubstitution σ₂ σ₃ ρs ρ₂ ∧ SourceAdmissible (σ₃ ≫ RawCtx.toCtx.map σ₂) ρs :=
    have ⟨ρ₁, hs, ha⟩ := hσ₁ σ₃ ρ₂ hρ
    ⟨_, inst.fields_admissible h.toIndData σ₁ hps pfield pf prf σ₃ ρ₁ ρ₂ hs ha hρ⟩
  have hih := (CtorInstance.generic h.toIndData s c).ih_typed (h.fields s c) f
  rw [← inst.ih_fieldsSubst h σ₁ hps hms hmins f, ← inst.ihType_fieldsSubst h σ₁ hps hms f]
  have hhom : SemanticHom σ₂ := ⟨pσ₂, hσ₂⟩
  exact ⟨hhom.props pe, hhom.fixed hih pt.subst pe.subst fe⟩

theorem RawSound.recursiveField_prop (h : IndData Γ₁ η ls ps) (fds : Fin (ι.ctors s c).nfields → Expr ζ₂ ℓ Γ₁.as.len)
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pf : ∀ f, RawJudgment Γ₁ (fds f) (fds f) (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f))
    (herased : (E₂.get η).block.level.inst ls = .zero) (f : Fin (ι.ctors s c).nrecFields) :
    E₂[Γ₁.as.ctx] ⊢ₛ ((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f : .prop ∧
      HasFixedness Γ₁ (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f) .prop := by
  let σ : Γ₁.as ⟶ (CtxCat.ctorSource h s c).as :=
    ⟨Fin.append ps fds, fun v => (ctorSourceJudgment pps pf v).syntactic.left⟩
  have pΔ := (hsound.ctorSourceProperties hB hblock s c).substitution
    (Src := CtxCat.ctorSource h s c) (sourceTelescope E₂ η ls s c f) (sourceTelescopeStrong h s c f)
    (hsound.recursiveArgumentProperties hB hblock s c h f) σ (fun v => (ctorSourceJudgment pps pf v).left)
    fun v => @(ctorSourceJudgment pps pf v).fixed
  have hσ : E₂[Γ₁.as.ctx] ⊢ₛ Fin.append ps fds ⊣
      Ctx.instL ls ((E₂.get η).block.params ++ ((E₂.get η).block.ctors s c).ordinaryTele) := σ.typed
  have hΔ := ((h.block.ctors s c).recursive f).instantiatedTelescope (P := fun _ => True) (ls := ls)
    (fun _ => trivial) (by simpa only using hσ)
  let T := CtxCat.extendTele Γ₁ _ hΔ
  have hI : IndTyping T η ((ι.ctors s c).recursiveTarget f) ls
      (fun p => (ps p).wkN ((ι.ctors s c).recursiveArity f))
      ((((E₂.get η).block.ctors s c).recursive f).instantiatedIndices ls (Fin.append ps fds)) :=
    ⟨fun p => by
      have hp : E₂[T.as.ctx] ⊢ₛ (ps p).wkN ((ι.ctors s c).recursiveArity f) :
          ((E₂.get η).block.paramType ls ps p).wkN ((ι.ctors s c).recursiveArity f) :=
        (pps p).syntactic.left.wkN
      simp only [Inductive.paramType_wkN] at hp
      exact hp,
    fun i => ((h.block.ctors s c).recursive f).instantiatedIndices (fun p => Fin.append_left _ _ p) i
      (by simpa only using hσ)⟩
  have hb : E₂[T.as.ctx] ⊢ₛ .ind η ((ι.ctors s c).recursiveTarget f) ls
      (fun p => (ps p).wkN ((ι.ctors s c).recursiveArity f))
      ((((E₂.get η).block.ctors s c).recursive f).instantiatedIndices ls (Fin.append ps fds)) :
      .sort ((E₂.get η).block.level.inst ls) := .indDF hI.param hI.index
  have pb : HasFixedness _ _ _ := HasFixedness.ind hI h.block
  rw [herased] at hb pb
  exact ⟨Ctx.pi_propStrong _ T.as.wf hb, HasFixedness.pi_prop _ hΔ pΔ _ hb pb⟩

theorem recoveredField_eq_instance (h : RecData Γ₁ η ls l ps ms mins) (hrel : l.rel = true)
    (herased : (E₂.get η).block.level.inst ls = .zero) (inst : CtorInstance Γ₁ η s c ls ps)
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pf : ∀ f, RawJudgment Γ₁ (inst.fds f) (inst.fds f)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps inst.fds f))
    (prf : ∀ f, RawJudgment Γ₁ (inst.recFds f) (inst.recFds f)
      (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps inst.fds f))
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    recoveredField η s c ls (fun i =>
        (rawInterpret (piLimit E₂ ℓ) Γ₁ (((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)).app _ σ.op ρ) =
      fun f => (rawInterpret (piLimit E₂ ℓ) Γ₁ (Fin.append inst.fds inst.recFds f)).app _ σ.op ρ := by
  have hctx (k : Nat) (hk : k ≤ (ι.ctors s c).nfields) := h.block.ordinaryClosedWF s c ls k hk
  funext f
  cases f using Fin.addCases with
  | left f =>
    simp only [recoveredField, Fin.append_left]
    split
    · rename_i hf
      have ⟨i, hi⟩ := Ctor.recoveryIndex_exists (h.recovery_eligible hrel herased s c).2 ls f hf
      rw [hi]
      exact congrArg (fun e => (rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ.op ρ)
        (Ctor.targetIndex_recovery hi ls ps inst.fds)
    · rename_i hf
      have hadm := (hsound.ctorSourceProperties hB hblock s c).admissible (hctx _ le_rfl)
        ⟨Fin.append ps inst.fds, Ctor.targetSubstWFStrong h.param inst.typed.ordinary⟩ σ ρ hρ
        (ctorSourceJudgment pps pf)
      have hvalues : (fun v => (rawInterpret (piLimit E₂ ℓ) Γ₁ ((Fin.append ps inst.fds) v)).app _ σ.op ρ) =
          Fin.append (fun p => (rawInterpret (piLimit E₂ ℓ) Γ₁ (ps p)).app _ σ.op ρ)
            fun f => (rawInterpret (piLimit E₂ ℓ) Γ₁ (inst.fds f)).app _ σ.op ρ := by
        funext v
        cases v using Fin.addCases <;> simp
      change SourceAdmissible _ (RawValuation.pushFin (fun _ => ⊥)
        fun v => (rawInterpret (piLimit E₂ ℓ) Γ₁ ((Fin.append ps inst.fds) v)).app _ σ.op ρ) at hadm
      rw [hvalues, RawValuation.pushFin_append] at hadm
      have hp := hsound.blockOrdinaryTypeJudgment η hB hblock s c ls f
      exact (ordinaryField_eq_bot_of_admissible hctx h.param inst.typed.ordinary f (hp (hctx _ _))
        (Bool.eq_false_iff.mpr hf) σ _ _ hadm).symm
  | right f =>
    simp only [recoveredField, Fin.append_right]
    have ⟨ht, hp⟩ := hsound.recursiveField_prop hB hblock h.toIndData inst.fds pps pf herased f
    have hsort := hp ht σ ρ hρ
    rw [rawInterpret_sort] at hsort
    exact (((prf f).fixed (prf f).syntactic.left σ ρ hρ).symm.trans
      (piLimit_rawExtend_prop _ hsort _ _)).symm

omit hsound hB hblock in
theorem CoherentShape.CtorInstance.caseSubstWF (h : RecData Γ₁ η ls l ps ms mins)
    (inst : CtorInstance Γ₁ η s c ls ps) :
    E₂[Γ₁.as.ctx] ⊢ₛ (ι.ctors s c).caseSubst inst.fds inst.recFds (inst.ih l ms mins) ⊣
      Γ₁.as.ctx ++ (E₂.get η).block.caseTele η ls ps ms s c := by
  have hΔ := (h.block.ctors s c).ihTele h.block Γ₁.as.wf h.param h.motive
  have hxs (f : Fin (ι.ctors s c).nrecFields) : E₂[Γ₁.as.ctx] ⊢ₛ inst.ih l ms mins f :
      ((((E₂.get η).block.ctors s c).ihTele ls ps ms).entry (by omega) (by omega)).subst
        (Fin.append (inst.fieldsSubst (𝟙 Γ₁.as)) fun previous =>
          inst.ih l ms mins (previous.castLE f.isLt.le)) := by
    rw [Ctor.ihTele, Ctor.ihTeleAux, Ctx.entry_ofTypes, Expr.wkN_subst_append]
    change E₂[Γ₁.as.ctx] ⊢ₛ inst.ih l ms mins f :
      (((E₂.get η).block.ctors s c).ihTypeWith ls
        (fun t => ((ms t).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
        ((ι.ctors s c).fieldParams ps) (CtorInstance.generic h.toIndData s c).fds
        (CtorInstance.generic h.toIndData s c).recFds f).subst (inst.fieldsSubst (𝟙 Γ₁.as))
    rw [inst.ihType_fieldsSubst h (𝟙 Γ₁.as) (fun p => Expr.subst_id _) (fun t => Expr.subst_id _)]
    exact inst.ih_typed h f
  have hσ := WFTeleStrong.extendFamily hΔ (inst.fieldsSubstWF h.toIndData (𝟙 Γ₁.as) fun p => Expr.subst_id _) hxs
  simpa [Inductive.caseTele, Tele.append_assoc, CtorSig.caseSubst, CtorInstance.fieldsSubst,
    RawCtx.Hom.id_subst] using hσ

theorem rawInterpret_iotaRhs (h : RecData Γ₁ η ls l ps ms mins) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ t, RawTyped Γ₁ (ms t) ((E₂.get η).block.motiveType η ls ps l t))
    (pmins : ∀ t c, RawTyped Γ₁ (mins t c) ((E₂.get η).block.caseFnType η ls ps ms t c))
    (inst : CtorInstance Γ₁ η s c ls ps)
    (pf : ∀ f, RawTyped Γ₁ (inst.fds f) (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps inst.fds f))
    (prf : ∀ f, RawTyped Γ₁ (inst.recFds f)
      (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps inst.fds f))
    (pih : ∀ f, RawInterpretationProperties Γ₁ (inst.ih l ms mins f) ∧
      HasFixedness Γ₁ (inst.ih l ms mins f)
        (((E₂.get η).block.ctors s c).ihTypeWith ls ms ps inst.fds inst.recFds f))
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ₁
      ((E₂.get η).block.iotaRhs η ls l ps ms mins s c inst.fds inst.recFds)).app _ σ₁.op ρ =
      rawApps ((rawInterpret (piLimit E₂ ℓ) Γ₁ (mins s c)).app _ σ₁.op ρ)
        (Fin.append (fun i => (Tm E₂ ℓ).map σ₁.op (inst.names i))
          (fun f => (Tm E₂ ℓ).map σ₁.op (inst.ihName h f)))
        (Fin.append
          (fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁ (Fin.append inst.fds inst.recFds i)).app _ σ₁.op ρ)
          (fun f => (rawInterpret (piLimit E₂ ℓ) Γ₁ (inst.ih l ms mins f)).app _ σ₁.op ρ)) := by
  have hps : ∀ p, (ps p).subst (RawCtx.Hom.subst (𝟙 Γ₁.as)) = ps p := fun p => Expr.subst_id _
  let O := ((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps
  let R := ((E₂.get η).block.ctors s c).recursiveFieldTele η ls
    (fun p => (ps p).wkN (ι.ctors s c).nfields)
    (Expr.boundVars Γ₁.as.len (ι.ctors s c).nfields 0)
  let H := ((E₂.get η).block.ctors s c).ihTele ls ps ms
  let t' := (E₂.get η).block.caseType η ls ps ms s c
  have pcase := hsound.caseTeleSplit hB hblock h.toIndData hR pps pms s c
  let T := CtxCat.extendTele Γ₁ O pcase.ordinaryWF
  let U := CtxCat.extendTele T R pcase.recursiveWF
  let V := CtxCat.extendTele U H pcase.ihWF
  have ht : E₂[Γ₁.as.ctx] ⊢ₛ (ι.ctors s c).caseSubst inst.fds inst.recFds (inst.ih l ms mins) ⊣ V.as.ctx := by
    have hh := inst.caseSubstWF h
    simp only [Inductive.caseTele, Ctor.fieldTele, ← Tele.append_assoc] at hh
    exact hh
  let σ₂ : Γ₁.as ⟶ V.as := ⟨_, ht⟩
  let σ₃ : Γ₁.as ⟶ U.as := σ₂ ≫ RawCtx.Hom.teleProjection pcase.ihWF
  let σ₄ : Γ₁.as ⟶ T.as := σ₃ ≫ RawCtx.Hom.teleProjection pcase.recursiveWF
  have hover : σ₄ ≫ RawCtx.Hom.teleProjection pcase.ordinaryWF = 𝟙 Γ₁.as := by
    apply RawCtx.Hom.ext
    funext v
    change (ι.ctors s c).caseSubst inst.fds inst.recFds (inst.ih l ms mins)
      (((v.castAdd (ι.ctors s c).nfields).castAdd (ι.ctors s c).nrecFields).castAdd
        (ι.ctors s c).nrecFields) = .var v
    simp [CtorSig.caseSubst, Subst.id]
  have hordinary (f : Fin (ι.ctors s c).nfields) : σ₄.subst (Fin.natAdd Γ₁.as.len f) = inst.fds f :=
    CtorSig.caseSubst_ordinary _ _ _ _ f
  have hrecursive (f : Fin (ι.ctors s c).nrecFields) :
      σ₃.subst (Fin.natAdd T.as.len f) = inst.recFds f :=
    CtorSig.caseSubst_recursive _ _ _ _ f
  have hih (f : Fin (ι.ctors s c).nrecFields) :
      σ₂.subst (Fin.natAdd U.as.len f) = inst.ih l ms mins f :=
    Fin.append_right _ _ _
  have htih (f : Fin (ι.ctors s c).nrecFields) :
      (V.as.ctx.get (Fin.natAdd U.as.len f)).subst σ₂.subst =
        ((E₂.get η).block.ctors s c).ihTypeWith ls ms ps inst.fds inst.recFds f := by
    erw [Ctx.get_subst _ _ _ (U.as.len + f.val)
      (by change U.as.len + f.val < U.as.len + (ι.ctors s c).nrecFields; omega) rfl,
      Ctx.entry_append_right U.as.ctx H (by omega) (by omega) (by
      change (Γ₁.as.len + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields) + f.val <
        (Γ₁.as.len + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields) + (ι.ctors s c).nrecFields
      omega)]
    dsimp only [H, Ctor.ihTele]
    erw [Ctor.ihTeleAux, Ctx.entry_ofTypes, Expr.wkN_eq_rename, Expr.rename_subst]
    rw [← inst.ihType_fieldsSubst h (𝟙 Γ₁.as) hps (fun t => Expr.subst_id _)]
    congr 1
    funext v
    change σ₂.subst ((v.castAdd f.val).castLE _) = (inst.fieldsSubst (𝟙 Γ₁.as)) v
    have hv : (v.castAdd f.val).castLE (show U.as.len + f.val ≤ V.as.len by
        change U.as.len + f.val ≤ U.as.len + (ι.ctors s c).nrecFields; omega) =
        v.castAdd (ι.ctors s c).nrecFields := Fin.ext rfl
    erw [hv]
    exact Fin.append_left _ _ _
  have fih (f : Fin (ι.ctors s c).nrecFields) :
      HasFixedness Γ₁ (σ₂.subst (Fin.natAdd U.as.len f))
        ((V.as.ctx.get (Fin.natAdd U.as.len f)).subst σ₂.subst) := by
    rw [hih, htih]
    exact (pih f).2
  let xs := fun f => (rawInterpret (piLimit E₂ ℓ) Γ₁ (inst.fds f)).app _ σ₁.op ρ
  let ys := fun f => (rawInterpret (piLimit E₂ ℓ) Γ₁ (inst.recFds f)).app _ σ₁.op ρ
  let zs := fun f => (rawInterpret (piLimit E₂ ℓ) Γ₁ (inst.ih l ms mins f)).app _ σ₁.op ρ
  let ρO := ρ.pushFin xs
  let ρR := ρO.pushFin ys
  have hv : (fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁
      (Fin.append inst.fds inst.recFds i)).app _ σ₁.op ρ) = Fin.append xs ys := by
    funext i
    cases i using Fin.addCases <;> simp [xs, ys]
  have hρR : ρR = ρ.pushFin (fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁
      (Fin.append inst.fds inst.recFds i)).app _ σ₁.op ρ) := by
    rw [hv, show ρR = (ρ.pushFin xs).pushFin ys from rfl, ← RawValuation.pushFin_append]
  have hfieldsSubst : σ₃.subst = inst.fieldsSubst (𝟙 Γ₁.as) := by
    funext v
    exact Fin.append_left _ _ _
  have hg : σ₃ = ⟨inst.fieldsSubst (𝟙 Γ₁.as), by rw [← hfieldsSubst]; exact σ₃.typed⟩ :=
    RawCtx.Hom.ext hfieldsSubst
  have hfields : SemanticSubstitution σ₃ σ₁ ρR ρ ∧
      SourceAdmissible (σ₁ ≫ RawCtx.toCtx.map σ₃) ρR := by
    rw [hρR]
    have q (wf : E₂[Γ₁.as.ctx ++ (O ++ R)] ⊢ₛ ok)
        (typed : E₂[Γ₁.as.ctx] ⊢ₛ inst.fieldsSubst (𝟙 Γ₁.as) ⊣ Γ₁.as.ctx ++ (O ++ R)) :
        let g : Γ₁.as ⟶ (⟨Γ₁.as.ctx ++ (O ++ R), wf⟩ : CtxCat E₂ ℓ).as := ⟨_, typed⟩
        SemanticSubstitution g σ₁ (ρ.pushFin fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁
          (Fin.append inst.fds inst.recFds i)).app _ σ₁.op ρ) ρ ∧
        SourceAdmissible (σ₁ ≫ RawCtx.toCtx.map g) (ρ.pushFin fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁
          (Fin.append inst.fds inst.recFds i)).app _ σ₁.op ρ) :=
      inst.fields_admissible h.toIndData (𝟙 Γ₁.as) hps
        (hsound.fieldTeleProperties hB hblock s c h.toIndData pps).1 pf prf σ₁ ρ ρ
        (SemanticSubstitution.id σ₁ ρ)
        (by rw [RawCtx.toCtx.map_id]; change SourceAdmissible (σ₁ ≫ 𝟙 Γ₁) ρ; rw [Category.comp_id]; exact hρ) hρ
    rw [← Tele.append_assoc] at q
    rw [hg]
    exact q U.as.wf _
  have hfull := RawTeleProperties.extend_admissible H rfl pcase.ihWF pcase.ih σ₂
    (fun f => by change RawInterpretationProperties Γ₁ (σ₂.subst (Fin.natAdd U.as.len f)); rw [hih]; exact (pih f).1)
    fih σ₁ ρR ρ hfields.1 hfields.2 hρ
  have hOrd : SourceAdmissible (σ₁ ≫ RawCtx.toCtx.map σ₄) ρO := by
    have hp := SourceAdmissible.tailTele pcase.recursiveWF hfields.2
    simp only [T, Nat.add_sub_cancel_left] at hp
    have hv : ρR.tailN (ι.ctors s c).nrecFields = ρO := RawValuation.tailN_pushFin _ _
    erw [Category.assoc, ← RawCtx.toCtx.map_comp, hv] at hp
    exact hp
  let BH := Ctx.pi t' H
  let BR := Ctx.pi BH R
  have hm : E₂[Γ₁.as.ctx] ⊢ₛ mins s c : Ctx.pi BR O := by
    have he := h.case s c
    simp only [Inductive.caseFnType, Inductive.caseTele, Ctor.fieldTele,
      Ctx.pi, Tele.foldr_append] at he
    exact he
  have hm' : E₂[Γ₁.as.ctx] ⊢ₛ mins s c : (Ctx.pi BR O).subst (RawCtx.Hom.subst (𝟙 Γ₁.as)) :=
    congr(E₂[Γ₁.as.ctx] ⊢ₛ mins s c :
      $(RawCtx.expr.map_id_apply (Opposite.op Γ₁.as) (Ctx.pi BR O))).mpr hm
  have hmf : HasFixedness Γ₁ (mins s c) (Ctx.pi BR O) := by
    have hf : HasFixedness Γ₁ (mins s c) ((E₂.get η).block.caseFnType η ls ps ms s c) := (pmins s c).fixed
    simp only [Inductive.caseFnType, Inductive.caseTele, Ctor.fieldTele,
      Ctx.pi, Tele.foldr_append] at hf
    exact hf
  have hfix' := HasFixedness.id_rawExtend
    (Ctx.pi_isTypeStrong T.as.wf pcase.recursivePi_sort.choose_spec).choose_spec hm hm' hmf σ₁ ρ hρ
  have ha := RawCtx.Hom.applyTele_typed pcase.ordinaryWF σ₄ hover pcase.recursivePi_sort.choose_spec hm'
  have qa := rawInterpret_applyTele_source O pcase.ordinaryWF pcase.ordinary BR pcase.recursivePi_sort.choose_spec pcase.recursivePi.ideal
    (𝟙 Γ₁.as) (mins s c) hm' σ₄ hover ha σ₁ ρ ρ ((pmins s c).term.ideal σ₁ ρ hρ)
    hfix' (by simpa only [hordinary] using hOrd)
  simp only [hordinary] at ha qa
  have hab : E₂[Γ₁.as.ctx] ⊢ₛ ((mins s c).apps inst.fds).apps inst.recFds : BH.subst σ₃.subst := by
    simpa only [hrecursive] using
      RawCtx.Hom.applyTele_typed pcase.recursiveWF σ₃ rfl pcase.ihPi_sort.choose_spec ha
  have qb := rawInterpret_applyTele_source R pcase.recursiveWF pcase.recursive BH pcase.ihPi_sort.choose_spec pcase.ihPi.ideal σ₄
    ((mins s c).apps inst.fds) ha σ₃ rfl
    (by simpa only [hrecursive] using hab) σ₁ ρO ρ
    qa.2.1
    qa.2.2
    (by simpa only [hrecursive] using hfields.2)
  simp only [hrecursive] at qb
  have hc := RawCtx.Hom.applyTele_typed pcase.ihWF σ₂ rfl pcase.sort hab
  have qc := rawInterpret_applyTele_source H pcase.ihWF pcase.ih t' pcase.sort (pcase.type _).ideal σ₃
    (((mins s c).apps inst.fds).apps inst.recFds) hab σ₂ rfl hc σ₁ ρR ρ
    qb.2.1
    qb.2.2
    (by
      have q := hfull.2
      change SourceAdmissible _ (ρR.pushFin fun i =>
        (rawInterpret (piLimit E₂ ℓ) Γ₁ (σ₂.subst (Fin.natAdd U.as.len i))).app _ σ₁.op ρ) at q
      simpa only using q)
  simp only [hih] at qc
  have hnfield (i : Fin (CtorHead.mk η s c).arity) :
      Tm.label Γ₁.as (σ₃.typed (fieldVar h.toIndData s c i)) = inst.names i := by
    have q (wf : E₂[Γ₁.as.ctx ++ (O ++ R)] ⊢ₛ ok)
        (typed : E₂[Γ₁.as.ctx] ⊢ₛ inst.fieldsSubst (𝟙 Γ₁.as) ⊣ Γ₁.as.ctx ++ (O ++ R)) :
        Tm.label Γ₁.as (typed (fieldVar h.toIndData s c i)) = inst.names i := by
      have hh := inst.map_fieldsHom_fieldVar h.toIndData (𝟙 Γ₁.as) hps i
      rwa [Tm.map_varLabel] at hh
    rw [← Tele.append_assoc] at q
    rw [hg]
    exact q U.as.wf _
  have hnO (f : Fin (ι.ctors s c).nfields) :
      Tm.label Γ₁.as (σ₄.typed (Fin.natAdd Γ₁.as.len f)) =
        Tm.label Γ₁.as (inst.typed.ordinary f) := by
    change (Tm E₂ ℓ).map (RawCtx.toCtx.map
      (σ₃ ≫ RawCtx.Hom.teleProjection pcase.recursiveWF)).op (Tm.varLabel T _) = _
    rw [RawCtx.toCtx.map_comp, op_comp, Functor.map_comp_apply, Tm.map_teleProjection_varLabel]
    have hh := hnfield (f.castAdd _)
    simp only [CtorInstance.names, CtorTyping.names, Fin.append_left] at hh
    exact hh
  have hnR (f : Fin (ι.ctors s c).nrecFields) :
      Tm.label Γ₁.as (σ₃.typed (Fin.natAdd T.as.len f)) =
        Tm.label Γ₁.as (inst.typed.recursive f) := by
    have hh := hnfield (Fin.natAdd (ι.ctors s c).nfields f)
    erw [fieldVar_natAdd] at hh
    simp only [CtorInstance.names, CtorTyping.names, Fin.append_right] at hh
    exact hh
  have hnH (f : Fin (ι.ctors s c).nrecFields) :
      Tm.label Γ₁.as (σ₂.typed (Fin.natAdd U.as.len f)) = inst.ihName h f := by
    apply Tm.label_eq
    · erw [htih]
      exact IsTypeStrong.isTypeEq (inst.ih_typed h f).regular
    · erw [htih, hih]
      exact inst.ih_typed h f
  change (rawInterpret (piLimit E₂ ℓ) Γ₁ (((mins s c).apps inst.fds).apps inst.recFds |>.apps
    (inst.ih l ms mins))).app _ σ₁.op ρ = _
  rw [qc.1, qb.1, qa.1]
  simp only [hordinary] at hnO
  simp only [hrecursive] at hnR
  simp only [hih] at hnH
  have hn : (fun i => (Tm E₂ ℓ).map σ₁.op (inst.names i)) =
      Fin.append (fun f => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (inst.typed.ordinary f)))
        (fun f => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (inst.typed.recursive f))) := by
    funext i
    cases i using Fin.addCases <;> simp [CtorInstance.names, CtorTyping.names]
  rw [hn, hv, rawApps_append, rawApps_append]
  refine congrArg₂ (fun F ns => rawApps F ns zs) ?_ ?_
  · refine congrArg₂ (fun F ns => rawApps F ns ys) ?_ ?_
    · apply congrArg (fun ns => rawApps ((rawInterpret (piLimit E₂ ℓ) Γ₁ (mins s c)).app _ σ₁.op ρ) ns xs)
      funext f
      exact congrArg ((Tm E₂ ℓ).map σ₁.op) (hnO f)
    · funext f
      exact congrArg ((Tm E₂ ℓ).map σ₁.op) (hnR f)
  · funext f
    exact congrArg ((Tm E₂ ℓ).map σ₁.op) (hnH f)

theorem RawSound.iota (h : RecData Γ₁ η ls l ps ms mins)
    (hrel : l.rel = true) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx) (inst : CtorInstance Γ₁ η s c ls ps)
    (pps : ∀ p, RawJudgment Γ₁ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawJudgment Γ₁ (ms s) (ms s) ((E₂.get η).block.motiveType η ls ps l s))
    (pmins : ∀ s c, RawJudgment Γ₁ (mins s c) (mins s c) ((E₂.get η).block.caseFnType η ls ps ms s c))
    (pf : ∀ f, RawJudgment Γ₁ (inst.fds f) (inst.fds f)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps inst.fds f))
    (prf : ∀ f, RawJudgment Γ₁ (inst.recFds f) (inst.recFds f)
      (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps inst.fds f))
    (heq : E₂[Γ₁.as.ctx] ⊢ₛ .recr η s ls l ps ms mins
        (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)
        (.ctor η s c ls ps inst.fds inst.recFds) ≡
      (E₂.get η).block.iotaRhs η ls l ps ms mins s c inst.fds inst.recFds :
      (E₂.get η).block.iotaType η ls ps ms s c inst.fds inst.recFds)
    (prhs : RawJudgment Γ₁
      ((E₂.get η).block.iotaRhs η ls l ps ms mins s c inst.fds inst.recFds)
      ((E₂.get η).block.iotaRhs η ls l ps ms mins s c inst.fds inst.recFds)
      ((E₂.get η).block.iotaType η ls ps ms s c inst.fds inst.recFds)) :
    HasEquality Γ₁
      (.recr η s ls l ps ms mins
        (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)
        (.ctor η s c ls ps inst.fds inst.recFds))
      ((E₂.get η).block.iotaRhs η ls l ps ms mins s c inst.fds inst.recFds) := by
  intro Γ₂ σ₁ ρ₁ hρ
  have hr := RecTyping.iota h.block h.allowed Γ₁.as.wf h.param h.motive h.case
    inst.typed.ordinary inst.typed.recursive
  have pfn (d : Fin (ι.nctors s)) := hsound.blockCtorTypeFnProperties η hB hblock s d ls
  have pis := hsound.instanceIndexProperties hB hblock s c h.toIndData pps pf
  have hind : IndTyping Γ₁ η s ls ps
      fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i :=
    ⟨h.param, hr.index⟩
  have pindTerm : RawInterpretationProperties Γ₁
      (.ind η s ls ps fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i) :=
    ⟨HasIdeality.ind hind h.block (fun d => (pfn d).ideal) fun p => (pps p).left.ideal,
      HasSubstitution.ind hind h.block fun p => (pps p).left.subst⟩
  have pind : RawJudgment Γ₁
      (.ind η s ls ps fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)
      (.ind η s ls ps fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)
      (.sort ((E₂.get η).block.level.inst ls)) :=
    ⟨.indDF h.param hr.index, RawInterpretationProperties.sort Γ₁ _, pindTerm, pindTerm,
      HasEquality.refl _ _, HasFixedness.ind hind h.block⟩
  have pmaj := RawJudgment.ctorDF hsound hB hblock h.block pps pf prf
    (fun f => (h.block.ctors s c).ordinaryFieldExprStrong f h.param inst.typed.ordinary)
    (fun f => ((h.block.ctors s c).recursiveFieldExprStrong rfl f Γ₁.as.wf h.param
      inst.typed.ordinary).choose_spec)
    pind
  have pargs := Inductive.forall_recrSubst_image (motive := fun e => RawInterpretationProperties Γ₁ e)
    (fun p => (pps p).left) (fun t => (pms t).left) (fun t c => (pmins t c).left) (fun i => (pis i).1)
    pmaj.left
  have fargs := Inductive.forall_recrSubst (motive := fun _ e _ t => HasFixedness Γ₁ e t)
    (ps₂ := ps) (ms₂ := ms) (mins₂ := mins)
    (is₂ := fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)
    (maj₂ := .ctor η s c ls ps inst.fds inst.recFds)
    (fun p => @(pps p).fixed) (fun t => @(pms t).fixed) (fun t c => @(pmins t c).fixed)
    (fun i => (pis i).2) @pmaj.fixed
  let hd := hr.toRecDecl
  let gen := RecTyping.generic hd ls s
  let σ' := σ₁ ≫ RawCtx.toCtx.map hr.recrHom
  let ρ' := RawValuation.pushFin (fun _ => ⊥) fun v =>
    (rawInterpret (piLimit E₂ ℓ) Γ₁ (Inductive.recrSubst ps ms mins
      (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)
      (.ctor η s c ls ps inst.fds inst.recFds) v)).app _ σ₁.op ρ₁
  let xs := fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁ (Fin.append inst.fds inst.recFds i)).app _ σ₁.op ρ₁
  have hps (p : Fin ι.nparams) : (Expr.var (RecrBinder.param (s := s) p).resolve).subst hr.recrHom.subst = ps p := by
    simp [RecTyping.recrHom, Expr.subst]
  have hms (t : Fin ι.nsorts) : (Expr.var (RecrBinder.motive (s := s) t).resolve).subst hr.recrHom.subst = ms t := by
    simp [RecTyping.recrHom, Expr.subst]
  have hmins (t : Fin ι.nsorts) (c₁ : Fin (ι.nctors t)) :
      (Expr.var (RecrBinder.case (s := s) t c₁).resolve).subst hr.recrHom.subst = mins t c₁ := by
    simp [RecTyping.recrHom, Expr.subst]
  have ppsG := hsound.genericParam hB hblock hd ls s
  have pmsG := hsound.genericMotive hB hblock hd ls s
  have pminsG := hsound.genericCase hB hblock hd ls s
  have hRG := RawTeleProperties.append .nil (hsound.recrTeleProperties hB hblock hd ls s)
  have pfieldG := (hsound.fieldTeleProperties hB hblock s c gen.toIndData ppsG).1
  have pf' := fun f => (pf f).toRawTyped
  have prf' := fun f => (prf f).toRawTyped
  have hadmRecr := hsound.recrHom_admissible hB hblock hr pargs fargs σ₁ ρ₁ hρ
  have hsubRecr := SemanticSubstitution.ofHom (CtxCat.recr hd ls s).as.wf hr.recrHom σ₁ ρ₁
    (fun v => (pargs v).subst) hρ
  have ⟨hsubF, hadmF⟩ := inst.fields_admissible gen.toIndData hr.recrHom hps pfieldG pf' prf' σ₁ ρ' ρ₁
    hsubRecr hadmRecr hρ
  have hxs (i : Fin (CtorHead.mk η s c).arity) : (xs i).IsDirected := by
    cases i using Fin.addCases with
    | left f =>
      simp only [xs, Fin.append_left]
      exact (pf f).left.ideal σ₁ ρ₁ hρ
    | right f =>
      simp only [xs, Fin.append_right]
      exact (prf f).left.ideal σ₁ ρ₁ hρ
  have pih := hsound.ihProperties inst hB hblock gen.toRecData hRG ppsG pmsG pminsG hr.recrHom hps hms hmins
    (fun v => (pargs v).subst)
    (fun _ σ₂ ρ₂ hρ₂ => ⟨_, SemanticSubstitution.ofHom (CtxCat.recr hd ls s).as.wf hr.recrHom σ₂ ρ₂
      (fun v => (pargs v).subst) hρ₂, hsound.recrHom_admissible hB hblock hr pargs fargs σ₂ ρ₂ hρ₂⟩) pf' prf'
  have hcase (f : Fin (ι.ctors s c).nrecFields) :
      rawApps ((recursorHyp (piLimit E₂ ℓ) (fun Γ₁ e _ => rawInterpret (piLimit E₂ ℓ) Γ₁ e) hd ls
          (recursor (piLimit E₂ ℓ) hd ls) s c f).app _ σ'.op ρ')
        (fun i => (Tm E₂ ℓ).map σ₁.op (inst.names i)) xs =
      (rawInterpret (piLimit E₂ ℓ) Γ₁ (inst.ih l ms mins f)).app _ σ₁.op ρ₁ := by
    have hproj : inst.fieldsHom gen.toIndData hr.recrHom hps ≫
        RawCtx.Hom.teleProjection ((gen.block.ctors s c).fieldTele rfl (CtxCat.recr hd ls s).as.wf gen.param) =
          hr.recrHom :=
      RawCtx.Hom.ext (funext fun v => inst.fieldsSubst_base gen.toIndData hr.recrHom v)
    have ⟨pe, _⟩ := hsound.genericIHProperties hB hblock gen.toRecData hRG ppsG pmsG pminsG s c f
    rw [recursorHyp_eq (piLimit E₂ ℓ) hd hrel ls s c f]
    refine (RawFamily.ctxLam_openBeta _ (k := (CtorHead.mk η s c).arity)
      (by simp only [CtorHead.arity, CtorHead.sig]; omega) _ pfieldG _ _ (rawInterpret_isFinitary _ _ _)
      pe.ideal (σ₁ ≫ RawCtx.toCtx.map (inst.fieldsHom gen.toIndData hr.recrHom hps)) σ'
      (by rw [Category.assoc, ← RawCtx.toCtx.map_comp, hproj]) _
      (fun i => by
        rw [op_comp, Functor.map_comp_apply]
        exact congrArg _ (inst.map_fieldsHom_fieldVar gen.toIndData hr.recrHom hps i))
      ρ' xs hadmF).trans ?_
    rw [← pe.subst (inst.fieldsHom gen.toIndData hr.recrHom hps) σ₁ _ ρ₁ hsubF hadmF]
    exact congrArg (fun e => (rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ₁.op ρ₁)
      (inst.ih_fieldsSubst gen.toRecData hr.recrHom hps hms hmins f)
  have hname (hstruct : (E₂.get η).block.IsStructure s c) :
      ((inst.section gen.toRecData hr.recrHom hps).pullback σ₁).ProjectsFrom hstruct
        ((Tm E₂ ℓ).map σ'.op
          (Tm.varLabel (CtxCat.recr hd ls s) (RecrBinder.major (s := s)).resolve)) := by
    have hA := gen.toIndData.indTyped s c hstruct
    have hi : (fun i => (Expr.var (RecrBinder.index (s := s) i).resolve :
        Expr ζ₂ ℓ (CtxCat.recr hd ls s).as.len)) = hstruct.indices :=
      funext hstruct.no_indices.elim
    have hvar : E₂[(CtxCat.recr hd ls s).as.ctx] ⊢ₛ .var (RecrBinder.major (s := s)).resolve :
        .ind η s ls (fun p => .var (RecrBinder.param p).resolve) hstruct.indices := by
      have hm := gen.major
      rwa [hi] at hm
    rw [← Tm.label_eq_var hvar rfl]
    refine ⟨(Raw.ContextSection.ofTerm hA hvar).pullbackId σ', ?_⟩
    have hrec : inst.recFds = hstruct.recursive := funext hstruct.no_recursive.elim
    have hmaj : E₂[Γ₁.as.ctx] ⊢ₛ .ctor η s c ls ps inst.fds hstruct.recursive :
        .ind η s ls ps hstruct.indices := by
      have hm := hr.major
      rwa [hrec, show (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i) = hstruct.indices from
        funext hstruct.no_indices.elim] at hm
    change σ₁ ≫ RawCtx.toCtx.map (inst.fieldsHom gen.toIndData hr.recrHom hps) =
      (σ' ≫ RawCtx.toCtx.map (RawCtx.Hom.one ⟨_, hA⟩ hvar)) ≫
        RawCtx.toCtx.map (projHom gen.toIndData s c hstruct)
    rw [Category.assoc, Category.assoc]
    congr 1
    set τ := hr.recrHom ≫ RawCtx.Hom.one ⟨_, hA⟩ hvar ≫ projHom gen.toIndData s c hstruct with hτ
    refine ((RawCtx.toCtx_map_eq_iff _ _).mpr fun v => ?_).symm
    cases v using Fin.addCases with
    | left v =>
      cases v using Fin.addCases with
      | left v =>
        have hb : τ.subst (baseVar gen.toIndData s c v) =
            (inst.fieldsHom gen.toIndData hr.recrHom hps).subst (baseVar gen.toIndData s c v) := by
          change ((projSubst gen.toIndData s c hstruct (baseVar gen.toIndData s c v)).subst
            (Subst.id.extend _)).subst hr.recrHom.subst = inst.fieldsSubst hr.recrHom (baseVar gen.toIndData s c v)
          rw [projSubst_base, inst.fieldsSubst_base gen.toIndData hr.recrHom v]
          simp [Expr.subst, Subst.id]
        change E₂[Γ₁.as.ctx] ⊢ₛ τ.subst (baseVar gen.toIndData s c v) ≡
          (inst.fieldsHom gen.toIndData hr.recrHom hps).subst (baseVar gen.toIndData s c v) :
          (Ctx.get (baseVar gen.toIndData s c v)
            (CtxCat.ctorFields gen.toIndData s c).as.ctx).subst τ.subst
        rw [← hb]
        exact τ.typed _
      | right f =>
        have hstep := hstruct.projTerm_ctorStrong h.block f inst.fds Γ₁.as.wf h.param hmaj inst.typed.ordinary
        have hord : τ.subst (fieldVar gen.toIndData s c (Fin.castAdd (ι.ctors s c).nrecFields f)) =
            hstruct.projTerm η ls ps f (.ctor η s c ls ps inst.fds hstruct.recursive) := by
          change ((RawCtx.Hom.one ⟨_, hA⟩ hvar ≫ projHom gen.toIndData s c hstruct).subst
            (fieldVar gen.toIndData s c (Fin.castAdd (ι.ctors s c).nrecFields f))).subst hr.recrHom.subst = _
          rw [projHom_one_ordinary gen.toIndData s c hstruct hvar f]
          simp [RecTyping.recrHom, Expr.subst, hrec]
        have hget : (Ctx.get (fieldVar gen.toIndData s c (Fin.castAdd (ι.ctors s c).nrecFields f))
            (CtxCat.ctorFields gen.toIndData s c).as.ctx).subst τ.subst =
            hstruct.projType η ls ps f (.ctor η s c ls ps inst.fds hstruct.recursive) := by
          change Expr.subst (Subst.comp (RawCtx.Hom.one ⟨_, hA⟩ hvar ≫
              projHom gen.toIndData s c hstruct).subst hr.recrHom.subst) _ = _
          rw [← Expr.subst_subst, projHom_one_get_ordinary gen.toIndData s c hstruct hvar f]
          simp [RecTyping.recrHom, Expr.subst, hrec]
        change E₂[Γ₁.as.ctx] ⊢ₛ
          τ.subst (fieldVar gen.toIndData s c (Fin.castAdd (ι.ctors s c).nrecFields f)) ≡
          inst.fieldsSubst hr.recrHom (fieldVar gen.toIndData s c (Fin.castAdd (ι.ctors s c).nrecFields f)) :
          (Ctx.get (fieldVar gen.toIndData s c (Fin.castAdd (ι.ctors s c).nrecFields f))
            (CtxCat.ctorFields gen.toIndData s c).as.ctx).subst τ.subst
        rw [hord, hget, inst.fieldsSubst_ordinary gen.toIndData hr.recrHom f]
        exact hstep
    | right f => exact hstruct.no_recursive.elim f
  have hX : (recoverMajor gen.toRecData s (𝟙 (CtxCat.recr hd ls s))
      (fun i => Tm.varLabel (CtxCat.recr hd ls s) (RecrBinder.index i).resolve)
      (fun i => RawFamily.lookup (Var.db (RecrBinder.index i).resolve))
      (RawFamily.lookup (Var.db (RecrBinder.major (s := s)).resolve))).app _ σ'.op ρ' =
      RawValue.ctor ⟨η, s, c⟩ ((inst.section gen.toRecData hr.recrHom hps).pullback σ₁).names xs := by
    rw [CtorSection.names_pullback, CtorInstance.names_section]
    by_cases hcar : Level.rel ((E₂.get η).block.level.inst ls) = true
    · simp only [recoverMajor, hcar]
      change ρ' (Var.db (RecrBinder.major (s := s)).resolve) = _
      simp only [ρ', RawValuation.pushFin_variable, Inductive.recrSubst_resolve_major]
      rw [rawInterpret_ctor_typed _ inst.typed hcar]
      rfl
    · have hz : (E₂.get η).block.level.inst ls = .zero := by simpa using hcar
      have hnames : (fun i => (Tm E₂ ℓ).map σ'.op
          (Tm.varLabel (CtxCat.recr hd ls s) (RecrBinder.index (s := s) i).resolve)) =
          fun i => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (hr.index i)) := by
        funext i
        rw [op_comp, Functor.map_comp_apply,
          ← Tm.label_eq_var (hsound.genericIndex hB hblock hd ls s i).typed rfl, Tm.map_label]
        refine congrArg _ (Tm.label_eq_iff.mpr ⟨?_, ?_⟩)
        · simp only [Inductive.indexType_subst, Expr.subst, RecTyping.recrHom, Inductive.recrSubst_resolve_param,
            Inductive.recrSubst_resolve_index]
          exact IsTypeStrong.isTypeEq (hr.index i).regular
        · simp only [Inductive.indexType_subst, Expr.subst, RecTyping.recrHom, Inductive.recrSubst_resolve_param,
            Inductive.recrSubst_resolve_index]
          exact hr.index i
      have hvals : (fun i => ρ' (Var.db (RecrBinder.index (s := s) i).resolve)) =
          fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁ (((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)).app _ σ₁.op ρ₁ := by
        funext i
        simp [ρ']
      simp only [recoverMajor, hcar]
      change proofConstructor gen.toRecData s (σ' ≫ 𝟙 _)
        (fun i => (Tm E₂ ℓ).map σ'.op (Tm.varLabel _ (RecrBinder.index (s := s) i).resolve))
        (fun i => ρ' (Var.db (RecrBinder.index (s := s) i).resolve)) = _
      rw [Category.comp_id]
      refine (congrArg₂ (proofConstructor gen.toRecData s σ') hnames hvals).trans ?_
      rw [proofConstructor_instance inst hr.recrHom hps hr.index gen.toRecData hrel hz σ₁,
        recoveredField_eq_instance hsound hB hblock h hrel hz inst pps pf prf σ₁ ρ₁ hρ]
  have hpayload : (recursorPayload (piLimit E₂ ℓ) (fun Γ₁ e _ => rawInterpret (piLimit E₂ ℓ) Γ₁ e) hd ls
      (recursor (piLimit E₂ ℓ) hd ls) s).app _ σ'.op ρ' =
      (rawInterpret (piLimit E₂ ℓ) Γ₁ ((E₂.get η).block.iotaRhs η ls l ps ms mins s c inst.fds inst.recFds)).app _
        σ₁.op ρ₁ := by
    unfold recursorPayload
    rw [RawActionFamily.apply_app, rawRecCaseFamily_value, hX,
      rawRecCase_ctor gen.toRecData _ _ σ' ρ' _ xs hxs _ hname,
      rawInterpret_iotaRhs hsound hB hblock h hR (fun p => (pps p).toRawTyped) (fun t => (pms t).toRawTyped)
        (fun t c => (pmins t c).toRawTyped) inst pf' prf' pih σ₁ ρ₁ hρ]
    simp only [CtorSection.names_pullback, CtorInstance.names_section, CtorSection.ihName_pullback,
      inst.ihName_section gen.toRecData hr.recrHom hps hms hmins h, caseArgs]
    congr 1
    · change ρ' (Var.db (RecrBinder.case (s := s) s c).resolve) = _
      simp [ρ', RawValuation.pushFin_variable, Inductive.recrSubst_resolve_case]
    · congr 1
      funext f
      exact hcase f
  have hn : Tm.label (t := Inductive.motiveResult (ms s)
      (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)
      (.ctor η s c ls ps inst.fds inst.recFds)) Γ₁.as heq.left = Tm.label Γ₁.as prhs.syntactic.left :=
    Tm.label_eq (IsTypeStrong.isTypeEq heq.left.regular) heq
  rw [hsound.recr_value hB hblock hr pargs fargs hrel heq.left σ₁ ρ₁ hρ, hpayload, hn]
  exact prhs.fixed prhs.syntactic.left σ₁ ρ₁ hρ

end Metalean
