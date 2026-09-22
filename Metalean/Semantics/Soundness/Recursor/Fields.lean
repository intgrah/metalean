/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Recursor.Fields
public import Metalean.Semantics.Soundness.Telescope.Application
public import Metalean.Semantics.Soundness.Function.Motive
public import Metalean.Semantics.Soundness.Rules.Inductive
public import Metalean.Semantics.Soundness.Telescope.Transport
import Metalean.Typing.InstLevel
import Metalean.Semantics.Soundness.Rules.Core
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

open CoherentShape CodeAssignment CategoryTheory

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {Γ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ.as.len} {ms : Fin ι.nsorts → Expr ζ₂ ℓ Γ.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ ℓ Γ.as.len} {e t : Expr ζ₂ ℓ Γ.as.len}

namespace CoherentShape

theorem RawTyped.ctorFields (p : RawTyped Γ e t)
    (h : IndData Γ η ls ps) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    RawTyped (CtxCat.ctorFields h s c)
      ((e.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
      ((t.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) := by
  have hp := (SemanticHom.teleProjection ((h.block.ctors s c).fieldTele rfl Γ.as.wf h.param)).typed p
  simp only [RawCtx.Hom.teleProjection, Expr.subst_vars] at hp
  simp only [Expr.wkN_eq_rename, Expr.rename_rename]
  exact hp

theorem SemanticHom.ctorFieldTarget (h : IndData Γ η ls ps)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields) :
    SemanticHom (CtxCat.ctorFieldTargetHom h s c f) := by
  have hp := (SemanticHom.teleProjection ((h.block.ctors s c).fieldTele rfl Γ.as.wf h.param)).comp
    (SemanticHom.teleProjection (fieldTelescope_wf h s c f))
  have he : RawCtx.Hom.teleProjection (fieldTelescope_wf h s c f) ≫
      CtxCat.ctorFieldsProjection h s c = CtxCat.ctorFieldTargetHom h s c f := by
    apply RawCtx.Hom.ext
    funext v
    exact (Expr.wkN_eq_subst _ _).symm
  exact he ▸ hp

end CoherentShape

variable (hsound : RawSound E₂ ℓ pre) (hB : InductiveWF E₁ I) (hblock : (E₂.get η).block = I.map pre.sigs)
  (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (h : IndData Γ η ls ps) (f : Fin (ι.ctors s c).nrecFields)

include hsound hB hblock

theorem RawSound.recursiveArgumentProperties :
    RawTeleProperties E₂ (CtxCat.ctorSource h s c).as.ctx
      ((((E₂.get η).block.ctors s c).recursive f).tele.instL ls) := by
  have hΔ := ((hB.ctors s c).recursive f).tele.instLevel (Q := fun _ => True) ls fun _ => trivial
  simpa [CtxCat.ctorSource, hblock, Inductive.map, Ctor.map, RecField.map, Ctor.ordinaryTele] using
    hsound.teleProperties (hB.ordinaryClosedWF s c ls _ le_rfl) hΔ

theorem RawSound.recursiveIndexProperties (i : Fin (ι.nindices ((ι.ctors s c).recursiveTarget f))) :
    RawJudgment (CtxCat.sourceFieldTarget h s c f)
      ((fun i => ((((E₂.get η).block.ctors s c).recursive f).indices i).instL ls) i) ((fun i => ((((E₂.get η).block.ctors s c).recursive f).indices i).instL ls) i)
      ((E₂.get η).block.indexType ls ((ι.ctors s c).recursiveTarget f)
        (fun p => ((Expr.var (p.castAdd (ι.ctors s c).nfields))).wkN ((ι.ctors s c).recursiveArity f))
        ((fun i => ((((E₂.get η).block.ctors s c).recursive f).indices i).instL ls)) i) := by
  have hctx : E₁[Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele)] ⊢ ok :=
    hB.ordinaryClosedWF s c ls (ι.ctors s c).nfields le_rfl
  have hΔ := ((hB.ctors s c).recursive f).tele.instLevel (Q := fun _ => True) ls fun _ => trivial
  have hi := ((hB.ctors s c).recursive f).instantiatedIndices (ls := ls) (σ := Subst.id)
    (ps := fun p => .var (p.castAdd (ι.ctors s c).nfields)) (fun _ => rfl) i
    (SubstWF.id hctx)
  simp only [RecField.instantiatedTelescope_id, RecField.instantiatedIndices_id] at hi
  have hfull := hΔ.appendCtxWF hctx
  have hp := hsound.properties hfull hi
  convert hp using 1 <;>
    simp [CtxCat.sourceFieldTarget, CtxCat.ctorSource, CtxCat.extendTele,
      hblock, Inductive.map, Ctor.map, RecField.map, Expr.map]

theorem RawSound.recursiveSourceProperties :
    RawTeleProperties E₂ (CtxCat.ctorSource h s c).as.ctx (recursiveSourceTele E₂ η ls s c) := by
  apply RawTeleProperties.ofTypes (recursiveSourceTele_wf h s c)
  intro f
  erw [← Subst.liftN_eq_append, Subst.liftN_id]
  let Δ := (((E₂.get η).block.ctors s c).recursive f).tele.instL ls
  have hΔ := sourceTelescope_wf h s c f
  have pΔ := hsound.recursiveArgumentProperties hB hblock s c h f
  let hI : IndTyping (CtxCat.sourceFieldTarget h s c f) η
      ((ι.ctors s c).recursiveTarget f) ls
      (fun p => ((Expr.var (p.castAdd (ι.ctors s c).nfields))).wkN ((ι.ctors s c).recursiveArity f))
      ((fun i => ((((E₂.get η).block.ctors s c).recursive f).indices i).instL ls)) := {
    param p := by
      have hp := (Inductive.paramType_var p (CtxCat.ctorSource h s c).as.wf).wkN (Δ := Δ)
      rwa [Inductive.paramType_wkN] at hp
    index := sourceIndexTyping h s c f }
  have hp (p : Fin ι.nparams) :=
    (RawInterpretationProperties.var (CtxCat.ctorSource h s c)
      (p.castAdd (ι.ctors s c).nfields)).wkN Δ hΔ
  rw [RecField.instantiatedType, RecField.instantiatedTelescope_id,
    RecField.instantiatedIndices_id]
  have pbody := RawInterpretationProperties.mk
    (HasIdeality.ind hI h.block
      (fun c' => (hsound.ctorTypeFnProperties η hB hblock ((ι.ctors s c).recursiveTarget f) c' ls).ideal)
      fun p => (hp p).ideal)
    (HasSubstitution.ind hI h.block fun p => (hp p).subst)
  simpa [Δ, Subst.id] using RawInterpretationProperties.pi (Src := CtxCat.ctorSource h s c)
    Δ hΔ pΔ _ (.indDF hI.param hI.index) pbody

theorem RawSound.fieldTeleProperties
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p)) :
    RawTeleProperties E₂ Γ.as.ctx (((E₂.get η).block.ctors s c).fieldTele η ls ps) ∧
      SemanticHom (CtxCat.ctorFieldsHom h s c) := by
  let := Subst.category ζ₂ ℓ
  let Src : CtxCat E₂ ℓ := ⟨Ctx.instL ls (E₂.get η).block.params, h.block.paramClosedWF ls⟩
  let O := Ctx.instL ls ((E₂.get η).block.ctors s c).ordinaryTele
  have hparams := hsound.paramTeleProperties hB hblock ls
  have hO := ((h.block.ctors s c).ordinaryTeleAux _ le_rfl).instLevel (Q := fun _ => True) ls fun _ => trivial
  have pO := hsound.ordinaryTeleProperties η hB hblock s c ls
  let σ : Γ.as ⟶ Src.as := ⟨ps, (Inductive.paramSubstEq h.param).left⟩
  have pf (p : Fin ι.nparams) : HasFixedness Γ (σ.subst p) ((Src.as.ctx.get p).subst σ.subst) := by
    rw [← Ctx.get_instL, Inductive.paramType_eq_get_subst]
    exact (pps p).fixed
  have hσ := SemanticHom.ofImages Src.as.wf hparams σ (fun p => (pps p).term) pf
  have pO' := hσ.tele hO pO
  have hg := hσ.liftTele hO pO
  let R := recursiveSourceTele E₂ η ls s c
  have hctx : Src.as.ctx ++ O = (CtxCat.ctorSource h s c).as.ctx :=
    (Ctx.instL_append _ _ _).symm
  have hR : TeleWF E₂ (fun _ => True) (Src.as.ctx ++ O) R := by
    rw [hctx]
    exact recursiveSourceTele_wf h s c
  have pR : RawTeleProperties E₂ (Src.as.ctx ++ O) R := by
    rw [hctx]
    exact hsound.recursiveSourceProperties hB hblock s c h
  have pR' := hg.tele hR pR
  have pall := pO'.append pR'
  change RawTeleProperties E₂ Γ.as.ctx
    (Ctx.substN ps (ι.ctors s c).nfields O ++
      Ctx.substN (Subst.liftN ps (ι.ctors s c).nfields) (ι.ctors s c).nrecFields R) at pall
  rw [recursiveSourceTele_subst] at pall
  have pp p := (pps p).ctorFields h s c
  simp only [Inductive.paramType_wkN] at pp
  have pf (f : Fin (ι.ctors s c).nfields) :
      RawTyped (CtxCat.ctorFields h s c) ((ι.ctors s c).fieldOrdinary f)
        (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls
          ((ι.ctors s c).fieldParams ps) (ι.ctors s c).fieldOrdinary f) := by
    rw [← CtxCat.ctorFields_get_ordinary h s c f]
    convert pall.var ((h.block.ctors s c).fieldTele rfl Γ.as.wf h.param)
      (fieldVar h s c (f.castAdd (ι.ctors s c).nrecFields)) (by dsimp [fieldVar]; omega) using 1
    simp [CtorSig.fieldOrdinary, fieldVar, Expr.var_wkN, Fin.natAdd]
  have pa := Ctor.forall_ordinarySubst (ctor := (E₂.get η).block.ctors s c)
    (motive := fun e _ t => RawTyped (CtxCat.ctorFields h s c) e t)
    (ps₂ := (ι.ctors s c).fieldParams ps) (fds₂ := (ι.ctors s c).fieldOrdinary) le_rfl pp pf
  exact ⟨pall, SemanticHom.ofImages (CtxCat.ctorSource h s c).as.wf
    (hsound.ordinaryPrefixProperties η hB hblock s c ls _ le_rfl) _
    (fun v => (pa v).term) (fun v => (pa v).fixed)⟩

theorem RawSound.fieldTelescopeProperties
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p)) :
    RawTeleProperties E₂ (CtxCat.ctorFields h s c).as.ctx (fieldTelescope h s c f) :=
  (hsound.fieldTeleProperties hB hblock s c h pps).2.tele (sourceTelescope_wf h s c f)
    (hsound.recursiveArgumentProperties hB hblock s c h f)

theorem RawSound.fieldIndexProperties
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (i : Fin (ι.nindices ((ι.ctors s c).recursiveTarget f))) :
    RawTyped (CtxCat.ctorFieldTarget h s c f) (fieldIndices h s c f i)
        ((E₂.get η).block.indexType ls ((ι.ctors s c).recursiveTarget f)
          (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
          (fieldIndices h s c f) i) := by
  have pargs := hsound.recursiveArgumentProperties hB hblock s c h f
  have hg := (hsound.fieldTeleProperties hB hblock s c h pps).2.liftTele
    (sourceTelescope_wf h s c f) pargs
  have pi := hsound.recursiveIndexProperties hB hblock s c h f i
  have hp := hg.typed pi.toRawTyped
  simp only [Inductive.indexType_subst, RawCtx.Hom.liftTele, Expr.wkN_subst,
    Expr.subst, CtxCat.ctorFieldsHom, Fin.append_left] at hp
  exact hp

theorem RawSound.sourceIndexProperties (h : IndData Γ η ls ps) (i : Fin (ι.nindices s)) :
    RawTyped (CtxCat.ctorSource h s c) ((((E₂.get η).block.ctors s c).targetIndices i).instL ls)
      ((E₂.get η).block.indexType ls s (fun p => .var (p.castAdd (ι.ctors s c).nfields))
        (fun j => (((E₂.get η).block.ctors s c).targetIndices j).instL ls) i) := by
  have hi := ((hB.ctors s c).targetIndices i).instLevel ls
  rw [Inductive.indexType_instL] at hi
  convert (hsound.properties (hB.ordinaryClosedWF s c ls _ le_rfl) hi).toRawTyped using 1 <;>
    simp [CtxCat.ctorSource, hblock, Inductive.map, Ctor.map, Expr.map, Expr.instL]
  rfl

theorem RawSound.appliedMajorProperties (h : IndData Γ η ls ps) (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (f : Fin (ι.ctors s c).nrecFields) :
    RawTyped (CtxCat.ctorFieldTarget h s c f) (appliedMajor h s c f)
      (.ind η ((ι.ctors s c).recursiveTarget f) ls
        (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
        (fieldIndices h s c f)) := by
  have pv := RawJudgment.var (Γ₁ := CtxCat.ctorFields h s c)
    (hR.append (by simpa using (hsound.fieldTeleProperties hB hblock s c h pps).1))
    (fieldVar h s c (Fin.natAdd (ι.ctors s c).nfields f))
  rw [CtxCat.ctorFields_get_recursive, Ctor.recursiveFieldExpr_eq, fieldVar_natAdd] at pv
  have ⟨_, _, hbody⟩ := Ctx.pi_isType_inv _ (CtxCat.ctorFields h s c).as.wf
    pv.syntactic.regular.choose_spec
  have hi := IndTyping.ofTyping (Γ₁ := CtxCat.ctorFieldTarget h s c f) h.block hbody
  have pp (p) := ((SemanticHom.ctorFieldTarget h s c f).typed (pps p)).term
  simp only [CtxCat.ctorFieldTargetHom_param] at pp
  have pbody := RawInterpretationProperties.mk
    (HasIdeality.ind hi h.block (fun c' => (hsound.ctorTypeFnProperties η hB hblock
      ((ι.ctors s c).recursiveTarget f) c' ls).ideal) fun p => (pp p).ideal)
    (HasSubstitution.ind hi h.block fun p => (pp p).subst)
  have pΔ := hsound.fieldTelescopeProperties hB hblock s c h f pps
  exact pv.toRawTyped.applyBound (fieldTelescope_wf h s c f) pΔ hbody pbody

theorem RawSound.recursiveMotiveResult (h : IndData Γ η ls ps) (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawTyped Γ (ms s) ((E₂.get η).block.motiveType η ls ps l s))
    (f : Fin (ι.ctors s c).nrecFields) :
    RawTyped (CtxCat.ctorFieldTarget h s c f)
      (Inductive.motiveResult
        ((ms ((ι.ctors s c).recursiveTarget f)).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
        (fieldIndices h s c f) (appliedMajor h s c f)) (.sort l) := by
  have pp (p) := (SemanticHom.ctorFieldTarget h s c f).typed (pps p)
  have pm := (SemanticHom.ctorFieldTarget h s c f).typed (pms ((ι.ctors s c).recursiveTarget f))
  simp only [Inductive.paramType_subst] at pp
  simp only [Inductive.motiveType_subst] at pm
  have pi := hsound.fieldIndexProperties hB hblock s c h f pps
  have pmaj := hsound.appliedMajorProperties hB hblock s c h hR pps f
  rw [← ctorFieldTargetHom_params h s c f] at pi pmaj
  exact RawTyped.motiveResult h.block ⟨fun p => (pp p).typed, fun i => (pi i).typed⟩
    pmaj.typed pm.typed
    (hsound.motiveTeleProperties hB hblock h.block (fun p => (pp p).typed)
      (fun p => (pp p).term) (fun p => (pp p).fixed) _)
    pm.term pm.fixed (fun i => (pi i).term) (fun i => (pi i).fixed) pmaj.term pmaj.fixed

theorem RawSound.fieldTargetArgProperties (h : IndData Γ η ls ps)
    (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ t, RawTyped Γ (ms t) ((E₂.get η).block.motiveType η ls ps l t))
    (pmins : ∀ t c, RawTyped Γ (mins t c) ((E₂.get η).block.caseFnType η ls ps ms t c))
    (f : Fin (ι.ctors s c).nrecFields) :
    let σ := Inductive.recrSubst
      (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
      (fun t => (ms t).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
      (fun t c₁ => (mins t c₁).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
      (fieldIndices h s c f) (appliedMajor h s c f)
    ∀ v, RawTyped (CtxCat.ctorFieldTarget h s c f) (σ v)
      ((Ctx.get v ((E₂.get η).block.recrTele η ((ι.ctors s c).recursiveTarget f) ls l)).subst σ) :=
  Inductive.forall_recrSubst (motive := fun _ _ e t => RawTyped _ e t)
    (fun p => by simpa only [Inductive.paramType_subst, ctorFieldTargetHom_params,
      CtxCat.ctorFieldTargetHom_param, CtorSig.fieldParams] using (SemanticHom.ctorFieldTarget h s c f).typed (pps p))
    (fun t => by simpa only [Inductive.motiveType_subst, ctorFieldTargetHom_params] using
      (SemanticHom.ctorFieldTarget h s c f).typed (pms t))
    (fun t c₁ => by simpa only [Inductive.caseFnType_subst, ctorFieldTargetHom_params] using
      (SemanticHom.ctorFieldTarget h s c f).typed (pmins t c₁))
    (hsound.fieldIndexProperties hB hblock s c h f pps)
    (hsound.appliedMajorProperties hB hblock s c h hR pps f)

theorem RawSound.caseTeleProperties (h : IndData Γ η ls ps) (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawTyped Γ (ms s) ((E₂.get η).block.motiveType η ls ps l s)) :
    RawTeleProperties E₂ Γ.as.ctx ((E₂.get η).block.caseTele η ls ps ms s c) :=
  (hsound.fieldTeleProperties hB hblock s c h pps).1.append
    (RawTeleProperties.ofTypes
      ((h.block.ctors s c).ihTele h.block Γ.as.wf h.param fun t => (pms t).typed)
      fun f => by
        have pm := hsound.recursiveMotiveResult hB hblock s c h hR pps pms f
        have hp := RawInterpretationProperties.pi (fieldTelescope h s c f)
          (fieldTelescope_wf h s c f) (hsound.fieldTelescopeProperties hB hblock s c h f pps)
          _ pm.typed pm.term
        simpa only [CtxCat.ctorFieldTargetHom_param] using hp)

end Metalean
