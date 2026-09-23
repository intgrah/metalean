/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Soundness.Recursor.Typing
public import Metalean.Semantics.Soundness.Telescope.Basic
import Metalean.Semantics.Interpretation.Computation
import Metalean.Syntax.Substitution

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
  (hidx : ∀ i, E₂[Γ₂.as.ctx] ⊢ ((E₂.get η).block.ctors s c).targetIndex ls ps₂ inst.fds i :
    (E₂.get η).block.indexType ls s ps₂ (((E₂.get η).block.ctors s c).targetIndex ls ps₂ inst.fds) i)

include hps in
theorem CoherentShape.CtorInstance.recovery_index_name (h : IndData Γ₁ η ls ps)
    (f : Fin (ι.ctors s c).nfields) (i : Fin (ι.nindices s))
    (hi : ((E₂.get η).block.ctors s c).recoveryIndex f = some i) :
    inst.typed.names (Fin.castAdd (ι.ctors s c).nrecFields f) = Tm.label Γ₂.as (hidx i) := by
  have ht := (h.block.ctors s c).targetIndex i
    (Ctor.forall_ordinarySubst le_rfl (fun p => CtorWF.fieldParams _ p h.param)
      (CtorInstance.generic h s c).typed.ordinary)
  have he : ((E₂.get η).block.ctors s c).targetIndex ls ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary i =
      .var (fieldVar h s c (Fin.castAdd (ι.ctors s c).nrecFields f)) := by
    rw [Ctor.targetIndex_recovery hi]
    simp [CtorSig.fieldOrdinary, fieldVar, Fin.natAdd]
  have hmap : Tm.label Γ₂.as (ht.substitution (inst.fieldsHom h σ₁ hps).typed) =
      inst.typed.names (Fin.castAdd (ι.ctors s c).nrecFields f) :=
    (Tm.map_label ht (inst.fieldsHom h σ₁ hps)).symm.trans
      ((congrArg ((Tm E₂ ℓ).map (RawCtx.toCtx.map (inst.fieldsHom h σ₁ hps)).op)
        (Tm.label_eq_var ht he)).trans (inst.map_fieldsHom_fieldVar h σ₁ hps _))
  rw [← hmap]
  congr 1 <;> simp [CtorInstance.fieldsHom, CtorInstance.generic, CtorInstance.fieldsSubst,
    Expr.boundVars, Expr.subst, hps, CtorSig.fieldParams]

include hps in
theorem proofConstructor_instance (h : RecData Γ₁ η ls l ps ms mins) (hrel : l.rel = true)
    (herased : (E₂.get η).block.level{ls} = .zero) (σ₂ : Γ₃ ⟶ Γ₂)
    (indices : Fin (ι.nindices s) → RawValue Γ₃) :
    proofConstructor h s (σ₂ ≫ RawCtx.toCtx.map σ₁)
        (fun i => (Tm E₂ ℓ).map σ₂.op (Tm.label Γ₂.as (hidx i))) indices =
      RawValue.ctor ⟨η, s, c⟩ (fun f => (Tm E₂ ℓ).map σ₂.op (inst.typed.names f))
        (recoveredField η s c ls indices) := by
  have hn : RecoveryNames η s c ls (fun i => Tm.label Γ₂.as (hidx i)) inst.typed.names := by
    intro f hf
    have ⟨i, hi⟩ := Ctor.recoveryIndex_exists (h.recovery_eligible hrel herased s c).2 ls f hf
    exact ⟨i, hi, inst.recovery_index_name σ₁ hps hidx h.toIndData f i hi⟩
  have hsingle := (h.recovery_eligible hrel herased s c).1
  ext Γ₄ σ₃ y
  have hnames := hn.map (σ₃ ≫ σ₂)
  let sect := ((inst.section h σ₁ hps).pullback (σ₃ ≫ σ₂)).congr
    (Category.assoc σ₃ σ₂ (RawCtx.toCtx.map σ₁))
  have hsect : sect.names = fun f => (Tm E₂ ℓ).map (σ₃ ≫ σ₂).op (inst.typed.names f) := by
    simp [sect]
  have hrhs :
      (RawValue.ctor ⟨η, s, c⟩ (fun f => (Tm E₂ ℓ).map σ₂.op (inst.typed.names f))
        (recoveredField η s c ls indices)).mem σ₃ y ↔
      (RawValue.ctor ⟨η, s, c⟩ (fun f => (Tm E₂ ℓ).map (σ₃ ≫ σ₂).op (inst.typed.names f))
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
      obtain rfl := CtorSection.eq_of_recovery h herased sect' sect hn' (by rwa [hsect])
      rwa [hsect] at hy
  · intro hy
    refine Or.inr ⟨c, sect, ?_, ?_⟩
    · rw [hsect]
      simpa using hnames
    · rwa [hsect]

variable (hsound : RawSound E₂ ℓ pre) (hB : InductiveWF E₁ I) (hblock : (E₂.get η).block = I.map pre.sigs)

include hsound hB hblock

theorem RawSound.genericIHProperties (h : RecData Γ₁ η ls l ps ms mins) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ t, RawTyped Γ₁ (ms t) ((E₂.get η).block.motiveType η ls ps l t))
    (pmins : ∀ t c, RawTyped Γ₁ (mins t c) ((E₂.get η).block.caseFnType η ls ps ms t c))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields) :
    RawTyped (CtxCat.ctorFields h.toIndData s c)
      ((CtorInstance.generic h.toIndData s c).ih l
        (fun t => ((ms t).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
        (fun t c₁ => ((mins t c₁).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) f)
      (((E₂.get η).block.ctors s c).ihType ls ps ms f) := by
  have h' := h.ihTyping s c f
  have pargs := hsound.fieldTargetArgProperties hB hblock s c h.toIndData hR pps pms pmins f
  have pe := RawInterpretationProperties.mk
    (hsound.recr_ideal hB hblock h' fun v => (pargs v).term.ideal)
    (HasSubstitution.recr h' fun v => (pargs v).term.subst)
  have fe := hsound.recr_fixed hB hblock h' (fun v => (pargs v).term) fun v => (pargs v).fixed
  have pΔ := hsound.fieldTelescopeProperties hB hblock s c h.toIndData f pps
  have pmr := hsound.recursiveMotiveResult hB hblock s c h.toIndData hR pps pms f
  rw [CtorInstance.generic_ih_eq_lam h.toIndData s c f ms mins,
    Ctor.ihType, CtorInstance.generic_ihType_eq_pi h.toIndData s c f ms]
  exact RawTyped.ctxLam _ (fieldTelescope_wf h.toIndData s c f) pΔ ⟨h'.typed, pmr.term, pe, fe⟩

theorem RawSound.recursiveField_prop (h : IndData Γ₁ η ls ps) (fds : Fin (ι.ctors s c).nfields → Expr ζ₂ ℓ Γ₁.as.len)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pf : ∀ f, RawTyped Γ₁ (fds f) (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f))
    (herased : (E₂.get η).block.level{ls} = .zero) (f : Fin (ι.ctors s c).nrecFields) :
    E₂[Γ₁.as.ctx] ⊢ ((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f : .prop ∧
      HasFixedness Γ₁ (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f) .prop := by
  have pσ := Ctor.forall_ordinarySubst (motive := fun e _ t => RawTyped Γ₁ e t)
    (ps₂ := ps) (fds₂ := fds) le_rfl pps pf
  let σ : Γ₁.as ⟶ (CtxCat.ctorSource h s c).as := ⟨_, fun v => (pσ v).typed⟩
  have pΔ := (SemanticHom.ofImages (CtxCat.ctorSource h s c).as.wf
    (hsound.ordinaryPrefixProperties η hB hblock s c ls _ le_rfl) σ
    (fun v => (pσ v).term) (fun v => (pσ v).fixed)).tele (sourceTelescope_wf h s c f)
      (hsound.recursiveArgumentProperties hB hblock s c h f)
  have hσ : E₂[Γ₁.as.ctx] ⊢ Fin.append ps fds ⊣
      ((E₂.get η).block.params ++ ((E₂.get η).block.ctors s c).ordinaryTele){ls} := σ.typed
  have hΔ := (((h.block.ctors s c).recursive f).tele.instLevel (Q := fun _ => True) ls
    fun _ => trivial).substitution hσ
  let T := CtxCat.extendTele Γ₁ _ hΔ
  have hI : IndTyping T η ((ι.ctors s c).recursiveTarget f) ls
      (fun p => (ps p).wkN ((ι.ctors s c).recursiveArity f))
      ((((E₂.get η).block.ctors s c).recursive f).instantiatedIndices ls (Fin.append ps fds)) :=
    ⟨fun p => by
      have hp : E₂[T.as.ctx] ⊢ (ps p).wkN ((ι.ctors s c).recursiveArity f) :
          ((E₂.get η).block.paramType ls ps p).wkN ((ι.ctors s c).recursiveArity f) :=
        (pps p).typed.wkN
      simp only [Inductive.paramType_wkN] at hp
      exact hp,
    fun i => ((h.block.ctors s c).recursive f).instantiatedIndices (fun p => Fin.append_left _ _ p) i
      (by simpa only using hσ)⟩
  have hb : E₂[T.as.ctx] ⊢ .ind η ((ι.ctors s c).recursiveTarget f) ls
      (fun p => (ps p).wkN ((ι.ctors s c).recursiveArity f))
      ((((E₂.get η).block.ctors s c).recursive f).instantiatedIndices ls (Fin.append ps fds)) :
      .sort (E₂.get η).block.level{ls} := .indDF hI.param hI.index
  have pb : HasFixedness _ _ _ := HasFixedness.ind hI h.block
  rw [herased] at hb pb
  exact ⟨Ctx.pi_prop _ T.as.wf hb, HasFixedness.pi_prop _ hΔ pΔ _ hb pb⟩

theorem recoveredField_eq_instance (h : RecData Γ₁ η ls l ps ms mins) (hrel : l.rel = true)
    (herased : (E₂.get η).block.level{ls} = .zero) (inst : CtorInstance Γ₁ η s c ls ps)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pf : ∀ f, RawTyped Γ₁ (inst.fds f)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps inst.fds f))
    (prf : ∀ f, RawTyped Γ₁ (inst.recFds f)
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
      have pσ := Ctor.forall_ordinarySubst (motive := fun e _ t => RawTyped Γ₁ e t)
        (ps₂ := ps) (fds₂ := fun g => inst.fds (g.castLE f.isLt.le)) f.isLt.le pps fun g => pf (g.castLE f.isLt.le)
      let τ : Γ₁.as ⟶ (⟨_, hctx f.val f.isLt.le⟩ : CtxCat E₂ ℓ).as :=
        ⟨_, fun v => (pσ v).typed⟩
      have hp := (SemanticHom.ofImages (hctx _ _) (hsound.ordinaryPrefixProperties η hB hblock s c ls _ _)
        τ (fun v => (pσ v).term) (fun v => (pσ v).fixed)).typed
        (hsound.ordinaryTypeJudgment η hB hblock s c ls f (hctx _ _)).toRawTyped
      have hz : (((E₂.get η).block.ctors s c).ordinary f).level{ls} = .zero := by simpa using hf
      rw [Expr.subst_sort, hz] at hp
      have hsrt := hp.fixed hp.typed σ ρ hρ
      rw [rawInterpret_sort] at hsrt
      exact (((pf f).fixed (pf f).typed σ ρ hρ).symm.trans
        (piLimit_rawExtend_prop _ hsrt _ _)).symm
  | right f =>
    simp only [recoveredField, Fin.append_right]
    have ⟨ht, hp⟩ := hsound.recursiveField_prop hB hblock h.toIndData inst.fds pps pf herased f
    have hsort := hp ht σ ρ hρ
    rw [rawInterpret_sort] at hsort
    exact (((prf f).fixed (prf f).typed σ ρ hρ).symm.trans
      (piLimit_rawExtend_prop _ hsort _ _)).symm

theorem rawInterpret_iotaRhs (h : RecData Γ₁ η ls l ps ms mins) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ t, RawTyped Γ₁ (ms t) ((E₂.get η).block.motiveType η ls ps l t))
    (pmins : ∀ t c, RawTyped Γ₁ (mins t c) ((E₂.get η).block.caseFnType η ls ps ms t c))
    (inst : CtorInstance Γ₁ η s c ls ps)
    (pf : ∀ f, RawTyped Γ₁ (inst.fds f) (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps inst.fds f))
    (prf : ∀ f, RawTyped Γ₁ (inst.recFds f)
      (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps inst.fds f))
    (pih : ∀ f, RawTyped Γ₁ (inst.ih l ms mins f)
        (((E₂.get η).block.ctors s c).ihTypeWith ls ms ps inst.fds inst.recFds f))
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ₁
      ((E₂.get η).block.iotaRhs η ls l ps ms mins s c inst.fds inst.recFds)).app _ σ₁.op ρ =
      rawApps ((rawInterpret (piLimit E₂ ℓ) Γ₁ (mins s c)).app _ σ₁.op ρ)
        (Fin.append (fun i => (Tm E₂ ℓ).map σ₁.op (inst.typed.names i))
          (fun f => (Tm E₂ ℓ).map σ₁.op (inst.ihName h f)))
        (Fin.append
          (fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁ (Fin.append inst.fds inst.recFds i)).app _ σ₁.op ρ)
          (fun f => (rawInterpret (piLimit E₂ ℓ) Γ₁ (inst.ih l ms mins f)).app _ σ₁.op ρ)) := by
  let Δ := (E₂.get η).block.caseTele η ls ps ms s c
  have hΔ := h.block.caseTele (s := s) (c := c) Γ₁.as.wf h.param h.motive
  have pΔ := hsound.caseTeleProperties hB hblock s c h.toIndData hR pps pms
  have ⟨_, _, hsort⟩ := Ctx.pi_isType_inv Δ Γ₁.as.wf (h.case s c).regular.choose_spec
  have pt := hsound.caseTypeProperties hB hblock h.toIndData pps pms s c
  have pσ := Ctor.forall_caseSubst (motive := fun _ e t => RawTyped Γ₁ e t)
    (fun v => (RawJudgment.var hR v).toRawTyped) pf prf pih
  let σ : Γ₁.as ⟶ (CtxCat.extendTele Γ₁ Δ hΔ).as := ⟨_, fun v => (pσ v).typed⟩
  have hk : Γ₁.as.len + ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields +
      (ι.ctors s c).nrecFields) = (CtxCat.extendTele Γ₁ Δ hΔ).as.len := by dsimp [Δ]; omega
  have hbase : σ ≫ RawCtx.Hom.teleProjection hΔ = 𝟙 Γ₁.as := by
    apply RawCtx.Hom.ext
    funext v
    exact (Fin.append_left _ _ _).trans ((Fin.append_left _ _ _).trans (Fin.append_left _ _ _))
  have q := RawTyped.apps Δ hk hΔ pΔ hsort (pt _) σ
    (by rw [hbase]; exact .id Γ₁) (fun i => pσ ((Fin.natAdd Γ₁.as.len i).cast hk))
    (by simp only [hbase, RawCtx.Hom.id_subst, Expr.subst_id]; exact pmins s c)
  let ns := Fin.append (Fin.append (Fin.append (Tm.varLabel Γ₁)
    (fun f => Tm.label Γ₁.as (pf f).typed)) (fun f => Tm.label Γ₁.as (prf f).typed))
      (fun f => Tm.label Γ₁.as (pih f).typed)
  have hn := Ctor.forall_caseSubst (Γ := Γ₁.as.ctx) (ctor := (E₂.get η).block.ctors s c)
    (η := η) (ls := ls) (ps := ps) (ms := ms) (fds := inst.fds) (recFds := inst.recFds)
    (ihs := inst.ih l ms mins)
    (motive := fun v e t => ∀ ht : E₂[Γ₁.as.ctx] ⊢ e : t, Tm.label Γ₁.as ht = ns v)
    (by intro v ht; simp [ns]; rfl) (by intro f ht; simp [ns])
    (by intro f ht; simp [ns]) (by intro f ht; simp [ns])
  have hargs : (fun i => σ.subst ((Fin.natAdd Γ₁.as.len i).cast hk)) =
      Fin.append (Fin.append inst.fds inst.recFds) (inst.ih l ms mins) := by
    funext i
    dsimp only [σ, CtorSig.caseSubst]
    rw [Fin.append_assoc, Fin.append_assoc]
    simp only [Function.comp_def, Fin.append_assoc]
    exact Fin.append_right _ _ (i.cast (Nat.add_assoc ..))
  have hnσ : (fun i => Tm.label Γ₁.as (σ.typed ((Fin.natAdd Γ₁.as.len i).cast hk))) =
      Fin.append (Fin.append (fun f => Tm.label Γ₁.as (pf f).typed)
        (fun f => Tm.label Γ₁.as (prf f).typed)) (fun f => Tm.label Γ₁.as (pih f).typed) := by
    funext i
    refine (hn _ (σ.typed _)).trans ?_
    dsimp only [ns]
    rw [Fin.append_assoc, Fin.append_assoc]
    simp only [Function.comp_def, Fin.append_assoc]
    exact Fin.append_right _ _ (i.cast (Nat.add_assoc ..))
  have he := q.2 σ₁ ρ hρ
  rw [congrArg (fun ns => fun i => (Tm E₂ ℓ).map σ₁.op (ns i)) hnσ] at he
  simp only [congrFun hargs] at he
  rw [Fin.append_comp _ _ (fun e => (rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ₁.op ρ),
    Fin.append_comp _ _ ((Tm E₂ ℓ).map σ₁.op)] at he
  simp only [Inductive.iotaRhs, Expr.apps_append, CtorTyping.names,
    CtorInstance.ihName, CtorInstance.ih, Inductive.iotaIHs, Fin.append_comp] at he ⊢
  exact he

theorem RawSound.iota (h : RecData Γ₁ η ls l ps ms mins)
    (hrel : l.rel = true) (hR : RawTeleProperties E₂ .nil Γ₁.as.ctx) (inst : CtorInstance Γ₁ η s c ls ps)
    (pps : ∀ p, RawTyped Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawTyped Γ₁ (ms s) ((E₂.get η).block.motiveType η ls ps l s))
    (pmins : ∀ s c, RawTyped Γ₁ (mins s c) ((E₂.get η).block.caseFnType η ls ps ms s c))
    (pf : ∀ f, RawTyped Γ₁ (inst.fds f)
      (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps inst.fds f))
    (prf : ∀ f, RawTyped Γ₁ (inst.recFds f)
      (((E₂.get η).block.ctors s c).recursiveFieldExpr η ls ps inst.fds f))
    (heq : E₂[Γ₁.as.ctx] ⊢ .recr η s ls l ps ms mins
        (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)
        (.ctor η s c ls ps inst.fds inst.recFds) ≡
      (E₂.get η).block.iotaRhs η ls l ps ms mins s c inst.fds inst.recFds :
      (E₂.get η).block.iotaType η ls ps ms s c inst.fds inst.recFds)
    (prhs : RawTyped Γ₁
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
  have pσ := Ctor.forall_ordinarySubst (motive := fun e _ t => RawTyped Γ₁ e t)
    (ps₂ := ps) (fds₂ := inst.fds) le_rfl pps pf
  let σsrc : Γ₁.as ⟶ (CtxCat.ctorSource h.toIndData s c).as := ⟨_, fun v => (pσ v).typed⟩
  have hsrc := SemanticHom.ofImages (CtxCat.ctorSource h.toIndData s c).as.wf
    (hsound.ordinaryPrefixProperties η hB hblock s c ls _ le_rfl) σsrc
    (fun v => (pσ v).term) (fun v => (pσ v).fixed)
  have pis i := hsrc.typed (hsound.sourceIndexProperties hB hblock s c h.toIndData i)
  simp only [Inductive.indexType_subst, Expr.subst, σsrc, Fin.append_left] at pis
  have pmaj := RawTyped.ctor hsound hB hblock h.block pps
    pf prf
  have pargs := Inductive.forall_recrSubst_image (motive := fun e => RawInterpretationProperties Γ₁ e)
    (fun p => (pps p).term) (fun t => (pms t).term) (fun t c => (pmins t c).term) (fun i => (pis i).term)
    pmaj.term
  have fargs := Inductive.forall_recrSubst (motive := fun _ e _ t => HasFixedness Γ₁ e t)
    (ps₂ := ps) (ms₂ := ms) (mins₂ := mins)
    (is₂ := ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds)
    (maj₂ := .ctor η s c ls ps inst.fds inst.recFds)
    (fun p => @(pps p).fixed) (fun t => @(pms t).fixed) (fun t c => @(pmins t c).fixed)
    (fun i => (pis i).fixed) @pmaj.fixed
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
  have ppsG := fun p => hsound.genericTyped hB hblock hd ls s (.param p)
  have pmsG := fun t => hsound.genericTyped hB hblock hd ls s (.motive t)
  have pminsG := fun t c => hsound.genericTyped hB hblock hd ls s (.case t c)
  have hRG := RawTeleProperties.append .nil (hsound.recrTeleProperties hB hblock hd ls s)
  have pfieldG := (hsound.fieldTeleProperties hB hblock s c gen.toIndData ppsG).1
  have hadmRecr := hsound.recrHom_admissible hB hblock hr pargs fargs σ₁ ρ₁ hρ
  have hsubRecr := SemanticSubstitution.ofHom (CtxCat.recr hd ls s).as.wf hr.recrHom σ₁ ρ₁
    (fun v => (pargs v).subst) hρ
  have ⟨hsubF, hadmF⟩ := inst.fields_admissible gen.toIndData hr.recrHom hps pfieldG pf prf σ₁ ρ' ρ₁
    hsubRecr hadmRecr hρ
  have hxs (i : Fin (CtorHead.mk η s c).arity) : (xs i).IsDirected := by
    cases i using Fin.addCases with
    | left f =>
      simp only [xs, Fin.append_left]
      exact (pf f).term.ideal σ₁ ρ₁ hρ
    | right f =>
      simp only [xs, Fin.append_right]
      exact (prf f).term.ideal σ₁ ρ₁ hρ
  have hfields : SemanticHom (inst.fieldsHom gen.toIndData hr.recrHom hps) := {
    image v := by
      cases v using Fin.addCases with
      | left v =>
        cases v using Fin.addCases <;> simp [CtorInstance.fieldsHom, CtorInstance.fieldsSubst]
        · exact (pargs _).subst
        · exact (pf _).term.subst
      | right f => simpa [CtorInstance.fieldsHom, CtorInstance.fieldsSubst] using (prf f).term.subst
    admissible _ τ ρ hρ := ⟨_, inst.fields_admissible gen.toIndData hr.recrHom hps pfieldG pf prf
      τ _ ρ (SemanticSubstitution.ofHom (CtxCat.recr hd ls s).as.wf hr.recrHom τ ρ
        (fun v => (pargs v).subst) hρ) (hsound.recrHom_admissible hB hblock hr pargs fargs τ ρ hρ) hρ⟩ }
  have pih f : RawTyped Γ₁ (inst.ih l ms mins f)
      (((E₂.get η).block.ctors s c).ihTypeWith ls ms ps inst.fds inst.recFds f) := by
    rw [← inst.ih_fieldsSubst gen.toRecData hr.recrHom hps hms hmins f,
      ← inst.ihType_fieldsSubst gen.toRecData hr.recrHom hps hms f]
    exact hfields.typed (hsound.genericIHProperties hB hblock gen.toRecData hRG ppsG pmsG pminsG s c f)
  have hcase (f : Fin (ι.ctors s c).nrecFields) :
      rawApps ((recursorHyp (piLimit E₂ ℓ) (fun Γ₁ e _ => rawInterpret (piLimit E₂ ℓ) Γ₁ e) hd ls
          (recursor (piLimit E₂ ℓ) hd ls) s c f).app _ σ'.op ρ')
        (fun i => (Tm E₂ ℓ).map σ₁.op (inst.typed.names i)) xs =
      (rawInterpret (piLimit E₂ ℓ) Γ₁ (inst.ih l ms mins f)).app _ σ₁.op ρ₁ := by
    have hproj : inst.fieldsHom gen.toIndData hr.recrHom hps ≫
        RawCtx.Hom.teleProjection ((gen.block.ctors s c).fieldTele rfl (CtxCat.recr hd ls s).as.wf gen.param) =
          hr.recrHom :=
      RawCtx.Hom.ext (funext fun v => inst.fieldsSubst_base gen.toIndData hr.recrHom v)
    have pe := (hsound.genericIHProperties hB hblock gen.toRecData hRG ppsG pmsG pminsG s c f).term
    rw [recursorHyp_eq (piLimit E₂ ℓ) hd hrel ls s c f]
    have hβ := RawFamily.ctxLam_openBeta _ (k := (CtorHead.mk η s c).arity)
      (by simp only [CtorHead.arity, CtorHead.sig]; omega) _ pfieldG
      (fieldTele_headRank_lt (CtxCat.recr hd ls s) (fun p => .var (RecrBinder.param p).resolve)
        (fun _ => Expr.headRank_var_le _) s c) _ (rawInterpret_isFinitary _ _ _)
      pe.ideal (σ₁ ≫ RawCtx.toCtx.map (inst.fieldsHom gen.toIndData hr.recrHom hps)) ρ' xs hadmF
    simp only [Category.assoc, ← RawCtx.toCtx.map_comp, hproj] at hβ
    refine Eq.trans ?_ (hβ.trans ?_)
    · congr 1
      funext i
      rw [op_comp, Functor.map_comp_apply]
      exact congrArg _ (inst.map_fieldsHom_fieldVar gen.toIndData hr.recrHom hps i).symm
    · rw [← pe.subst (inst.fieldsHom gen.toIndData hr.recrHom hps) σ₁ _ ρ₁ hsubF hadmF]
      exact congrArg (fun e => (rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ₁.op ρ₁)
        (inst.ih_fieldsSubst gen.toRecData hr.recrHom hps hms hmins f)
  have hname (hstruct : (E₂.get η).block.IsStructure s c) :
      ((inst.section gen.toRecData hr.recrHom hps).pullback σ₁).ProjectsFrom hstruct
        ((Tm E₂ ℓ).map σ'.op
          (Tm.varLabel (CtxCat.recr hd ls s) (RecrBinder.major (s := s)).resolve)) := by
    have hA := hstruct.indType gen.param
    have hi : (fun i => (Expr.var (RecrBinder.index (s := s) i).resolve :
        Expr ζ₂ ℓ (CtxCat.recr hd ls s).as.len)) = hstruct.indices :=
      funext hstruct.no_indices.elim
    have hvar : E₂[(CtxCat.recr hd ls s).as.ctx] ⊢ .var (RecrBinder.major (s := s)).resolve :
        .ind η s ls (fun p => .var (RecrBinder.param p).resolve) hstruct.indices := by
      have hm := gen.major
      rwa [hi] at hm
    rw [← Tm.label_eq_var hvar rfl]
    have hrec : inst.recFds = hstruct.recursive := funext hstruct.no_recursive.elim
    have hmaj : E₂[Γ₁.as.ctx] ⊢ .ctor η s c ls ps inst.fds hstruct.recursive :
        .ind η s ls ps hstruct.indices := by
      have hm := hr.major
      rwa [hrec, show (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i) = hstruct.indices from
        funext hstruct.no_indices.elim] at hm
    let msect := (Raw.ContextSection.ofTerm hA hvar).pullbackId σ'
    let sect := CtorSection.ofMajor (h := gen.toRecData) hstruct msect
    have heq : sect = (inst.section gen.toRecData hr.recrHom hps).pullback σ₁ := by
      apply CtorSection.eq_of_names_eq
      funext i
      cases i using Fin.addCases with
      | right f => exact hstruct.no_recursive.elim f
      | left f =>
        rw [sect.proj_name hstruct hvar ⟨msect, rfl⟩ f,
          CtorSection.names_pullback, CtorInstance.names_section]
        change (Tm E₂ ℓ).map (σ₁ ≫ RawCtx.toCtx.map hr.recrHom).op _ = _
        rw [op_comp, Functor.map_comp_apply, Tm.map_label]
        apply congrArg ((Tm E₂ ℓ).map σ₁.op)
        trans Tm.proj hstruct h.block ls ps h.param f (Tm.label Γ₁.as hmaj) rfl
        · congr 1 <;> simp [RecTyping.recrHom, Expr.subst, hrec,
            Inductive.IsStructure.projTerm_subst, Inductive.IsStructure.projType_subst]
        · simpa [CtorTyping.names] using
            Tm.proj_ctor_label hstruct h.block ls ps h.param inst.fds hmaj inst.typed.ordinary f
    exact heq ▸ (show sect.ProjectsFrom hstruct _ from ⟨msect, rfl⟩)

  have hX : (recoverMajor gen.toRecData s (𝟙 (CtxCat.recr hd ls s))
      (fun i => Tm.varLabel (CtxCat.recr hd ls s) (RecrBinder.index i).resolve)
      (fun i => RawFamily.lookup (Var.db (RecrBinder.index i).resolve))
      (RawFamily.lookup (Var.db (RecrBinder.major (s := s)).resolve))).app _ σ'.op ρ' =
      RawValue.ctor ⟨η, s, c⟩ ((inst.section gen.toRecData hr.recrHom hps).pullback σ₁).names xs := by
    rw [CtorSection.names_pullback, CtorInstance.names_section]
    by_cases hcar : Level.rel ((E₂.get η).block.level{ls}) = true
    · simp only [recoverMajor, hcar]
      change ρ' (Var.db (RecrBinder.major (s := s)).resolve) = _
      simp only [ρ', RawValuation.pushFin_variable, Inductive.recrSubst_major]
      rw [rawInterpret_ctor_typed _ inst.typed hcar]
      rfl
    · have hz : (E₂.get η).block.level{ls} = .zero := by simpa using hcar
      have hnames : (fun i => (Tm E₂ ℓ).map σ'.op
          (Tm.varLabel (CtxCat.recr hd ls s) (RecrBinder.index (s := s) i).resolve)) =
          fun i => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (hr.index i)) := by
        funext i
        rw [op_comp, Functor.map_comp_apply,
          ← Tm.label_eq_var (hsound.genericTyped hB hblock hd ls s (.index i)).typed rfl, Tm.map_label]
        congr 2 <;> simp [Expr.subst, RecTyping.recrHom, Inductive.recrBinderType]
      have hvals : (fun i => ρ' (Var.db (RecrBinder.index (s := s) i).resolve)) =
          fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁ (((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)).app _ σ₁.op ρ₁ := by
        funext i
        dsimp only [ρ']
        rw [RawValuation.pushFin_variable]
        simp
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
      rawInterpret_iotaRhs hsound hB hblock h hR pps pms
        pmins inst pf prf pih σ₁ ρ₁ hρ]
    simp only [CtorSection.names_pullback, CtorInstance.names_section, CtorSection.ihName_pullback,
      inst.ihName_section gen.toRecData hr.recrHom hps hms hmins h, caseArgs]
    congr 1
    · change ρ' (Var.db (RecrBinder.case (s := s) s c).resolve) = _
      dsimp only [ρ']
      rw [RawValuation.pushFin_variable, Inductive.recrSubst_case]
    · congr 1
      funext f
      exact hcase f
  have hn : Tm.label (t := Inductive.motiveResult (ms s)
      (fun i => ((E₂.get η).block.ctors s c).targetIndex ls ps inst.fds i)
      (.ctor η s c ls ps inst.fds inst.recFds)) Γ₁.as heq.left = Tm.label Γ₁.as prhs.typed :=
    Tm.label_eq (IsType.typeEq heq.left.regular) heq
  rw [hsound.recr_value hB hblock hr pargs fargs hrel σ₁ ρ₁ hρ, hpayload, hn]
  exact prhs.fixed prhs.typed σ₁ ρ₁ hρ

end Metalean
