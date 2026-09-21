/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Recursor.Fields
public import Metalean.Semantics.Soundness.Function.Application
public import Metalean.Semantics.Soundness.Function.Motive
public import Metalean.Semantics.Soundness.Rules.Inductive
public import Metalean.Semantics.Soundness.Telescope.Transport
import Metalean.Strong.InstLevel
import Metalean.Semantics.Soundness.Rules.Core
import Metalean.Syntax.Substitution
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean

open CoherentShape CodeAssignment CategoryTheory TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {Γ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ.as.len} {ms : Fin ι.nsorts → Expr ζ₂ ℓ Γ.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ ℓ Γ.as.len} {e t : Expr ζ₂ ℓ Γ.as.len}

namespace CoherentShape

structure RawTyped (Γ : CtxCat E₂ ℓ) (e t : Expr ζ₂ ℓ Γ.as.len) : Prop where
  typed : E₂[Γ.as.ctx] ⊢ₛ e : t
  type : RawInterpretationProperties Γ t
  term : RawInterpretationProperties Γ e
  fixed : HasFixedness Γ e t

theorem RawJudgment.toRawTyped {e₁ e₂ t : Expr ζ₂ ℓ Γ.as.len} (p : RawJudgment Γ e₁ e₂ t) :
    RawTyped Γ e₁ t :=
  ⟨p.syntactic.left, p.type, p.left, p.fixed⟩

theorem RawTyped.ctorFields_properties (p : RawTyped Γ e t)
    (h : IndData Γ η ls ps) (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) :
    RawInterpretationProperties (CtxCat.ctorFields h s c)
      ((e.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) ∧
      RawInterpretationProperties (CtxCat.ctorFields h s c)
        ((t.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) ∧
      HasFixedness (CtxCat.ctorFields h s c)
        ((e.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
        ((t.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) := by
  let O := ((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps
  let R := ((E₂.get η).block.ctors s c).recursiveFieldTele η ls
    (fun p => (ps p).wkN (ι.ctors s c).nfields)
    (Expr.boundVars Γ.as.len (ι.ctors s c).nfields 0)
  have ⟨hO, hR⟩ := ((h.block.ctors s c).fieldTele rfl Γ.as.wf h.param).of_append
  have pe := p.term.wkN O hO
  have pt := p.type.wkN O hO
  have q (wf : E₂[Γ.as.ctx ++ O ++ R] ⊢ₛ ok) :
      RawInterpretationProperties (⟨Γ.as.ctx ++ O ++ R, wf⟩ : CtxCat E₂ ℓ)
        ((e.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) ∧
      RawInterpretationProperties (⟨Γ.as.ctx ++ O ++ R, wf⟩ : CtxCat E₂ ℓ)
        ((t.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) ∧
      HasFixedness (⟨Γ.as.ctx ++ O ++ R, wf⟩ : CtxCat E₂ ℓ)
        ((e.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
        ((t.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) :=
    ⟨pe.wkN R hR, pt.wkN R hR,
      HasFixedness.wkN R hR p.typed.wkN pt pe
        (HasFixedness.wkN O hO p.typed p.type p.term p.fixed)⟩
  rw [Tele.append_assoc] at q
  exact q (CtxCat.ctorFields h s c).as.wf

theorem RawTyped.ctorFieldTarget_properties (p : RawTyped Γ e t)
    (h : IndData Γ η ls ps) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (f : Fin (ι.ctors s c).nrecFields) :
    RawInterpretationProperties (CtxCat.ctorFieldTarget h s c f)
      (e.subst (CtxCat.ctorFieldTargetHom h s c f).subst) ∧
      RawInterpretationProperties (CtxCat.ctorFieldTarget h s c f)
        (t.subst (CtxCat.ctorFieldTargetHom h s c f).subst) ∧
      HasFixedness (CtxCat.ctorFieldTarget h s c f)
        (e.subst (CtxCat.ctorFieldTargetHom h s c f).subst)
        (t.subst (CtxCat.ctorFieldTargetHom h s c f).subst) := by
  have ⟨pe, pt, pf⟩ := p.ctorFields_properties h s c
  let Δ := fieldTelescope h s c f
  have hΔ := fieldTelescopeStrong h s c f
  have he := p.typed.substitution (CtxCat.ctorFieldsProjection h s c).typed
  have hw (x : Expr ζ₂ ℓ Γ.as.len) : x.subst (CtxCat.ctorFieldsProjection h s c).subst =
      (x.wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields := by
    rw [Expr.wkN_eq_rename, Expr.wkN_eq_rename, Expr.rename_rename, ← Expr.subst_vars]
    rfl
  erw [hw e, hw t] at he
  rw [CtxCat.ctorFieldTargetHom_param, CtxCat.ctorFieldTargetHom_param]
  exact ⟨pe.wkN Δ hΔ, pt.wkN Δ hΔ, HasFixedness.wkN Δ hΔ he pt pe pf⟩

end CoherentShape

variable (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁) (hblock : (E₂.get η).block = I.map pre.sigs)
  (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (h : IndData Γ η ls ps) (f : Fin (ι.ctors s c).nrecFields)

include hsound hB hblock

omit hsound hB in
theorem ctorSource_ctx_map :
    (Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele)).map pre.sigs =
      Ctx.instL ls ((E₂.get η).block.params ++ ((E₂.get η).block.ctors s c).ordinaryTele) :=
  (Ctx.map_instL pre.sigs ls _).trans
    (congrArg (Ctx.instL ls)
      (((Ctx.map_append pre.sigs _ _).trans
        (congrArg₂ Tele.append rfl (Ctor.ordinaryTele_map pre.sigs (I.ctors s c)))).trans
          (congrArg (fun J : Inductive ζ₂ ι => J.params ++ (J.ctors s c).ordinaryTele) hblock.symm)))

theorem RawSound.ctorSourceProperties :
    RawTeleProperties E₂ .nil (Ctx.instL ls ((E₂.get η).block.params ++ ((E₂.get η).block.ctors s c).ordinaryTele)) := by
  simpa [hblock] using
    hsound.ordinaryPrefixProperties hB s c ls (ι.ctors s c).nfields le_rfl

theorem RawSound.recursiveArgumentProperties :
    RawTeleProperties E₂ (CtxCat.ctorSource h s c).as.ctx (sourceTelescope E₂ η ls s c f) :=
  have hctx : E₁[Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele)] ⊢ₛ ok :=
    hB.ordinaryClosedWF s c ls (ι.ctors s c).nfields le_rfl
  have hΔ := ((hB.ctors s c).recursive f).tele.instLevel (Q := fun _ => True) ls fun _ => trivial
  (congrArg₂ (RawTeleProperties E₂) (ctorSource_ctx_map hblock s c)
    ((Ctx.map_instL pre.sigs ls _).trans
      (congrArg (fun J : Inductive ζ₂ ι => ((J.ctors s c).recursive f).tele.instL ls) hblock.symm))).mp
        (hsound.teleProperties hctx hΔ)

theorem RawSound.recursiveIndexProperties (i : Fin (ι.nindices ((ι.ctors s c).recursiveTarget f))) :
    RawJudgment (CtxCat.sourceFieldTarget h s c f)
      (sourceIndices E₂ η ls s c f i) (sourceIndices E₂ η ls s c f i)
      ((E₂.get η).block.indexType ls ((ι.ctors s c).recursiveTarget f)
        (fun p => (sourceParams ι s c p).wkN ((ι.ctors s c).recursiveArity f))
        (sourceIndices E₂ η ls s c f) i) := by
  have hctx : E₁[Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele)] ⊢ₛ ok :=
    hB.ordinaryClosedWF s c ls (ι.ctors s c).nfields le_rfl
  have hΔ := ((hB.ctors s c).recursive f).tele.instLevel (Q := fun _ => True) ls fun _ => trivial
  have hi := ((hB.ctors s c).recursive f).instantiatedIndices (ls := ls) (σ := Subst.id)
    (ps := fun p => .var (p.castAdd (ι.ctors s c).nfields)) (fun _ => rfl) i
    (SubstWFStrong.id hctx)
  simp only [RecField.instantiatedTelescope_id, RecField.instantiatedIndices_id] at hi
  have hfull := hΔ.appendCtxWFStrong hctx
  have hctxeq : Ctx.map pre.sigs
      (Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele) ++
        ((I.ctors s c).recursive f).tele.instL ls) =
      (CtxCat.sourceFieldTarget h s c f).as.ctx :=
    (Ctx.map_append pre.sigs _ _).trans (congrArg₂ Tele.append (ctorSource_ctx_map hblock s c)
      ((Ctx.map_instL pre.sigs ls _).trans
        (congrArg (fun J : Inductive ζ₂ ι => ((J.ctors s c).recursive f).tele.instL ls) hblock.symm)))
  have hp' := hsound.properties hfull hctxeq (CtxCat.sourceFieldTarget h s c f).as.wf hi
  have hx (j) : ((((I.ctors s c).recursive f).indices j).instL ls).map pre.sigs =
      sourceIndices E₂ η ls s c f j := by
    simp [sourceIndices, hblock, Inductive.map, Ctor.map, RecField.map]
  erw [hx i, Inductive.indexType_map] at hp'
  have hxs := funext hx
  erw [hxs] at hp'
  simp only [← hblock, Expr.map_wkN] at hp'
  exact hp'

omit hsound hB hblock in
theorem CoherentShape.recursiveTypeProperties
    (pΔ : RawTeleProperties E₂ (CtxCat.ctorSource h s c).as.ctx (sourceTelescope E₂ η ls s c f))
    (hfn : ∀ c' : Fin (ι.nctors ((ι.ctors s c).recursiveTarget f)),
      HasIdeality (CtxCat.nil E₂ ℓ)
        (((E₂.get η).block.ctorTypeFn ((ι.ctors s c).recursiveTarget f) c').instL
          fun p => ls p)) :
    RawInterpretationProperties (CtxCat.ctorSource h s c)
      ((((E₂.get η).block.ctors s c).recursive f).instantiatedType η ls
        (sourceParams ι s c) Subst.id) := by
  let Δ := sourceTelescope E₂ η ls s c f
  let hΔ := sourceTelescopeStrong h s c f
  let hI : IndTyping (CtxCat.sourceFieldTarget h s c f) η
      ((ι.ctors s c).recursiveTarget f) ls
      (fun p => (sourceParams ι s c p).wkN ((ι.ctors s c).recursiveArity f))
      (sourceIndices E₂ η ls s c f) := {
    param p := by
      have hp := (sourceParams_typed h s c p).wkN (Δ := Δ)
      rwa [Inductive.paramType_wkN] at hp
    index := sourceIndexTyping h s c f }
  have hp (p : Fin ι.nparams) :
      RawInterpretationProperties (CtxCat.sourceFieldTarget h s c f)
        ((sourceParams ι s c p).wkN ((ι.ctors s c).recursiveArity f)) :=
    (RawInterpretationProperties.var (CtxCat.ctorSource h s c)
      (p.castAdd (ι.ctors s c).nfields)).wkN Δ hΔ
  have hind : RawInterpretationProperties (CtxCat.sourceFieldTarget h s c f)
      (.ind η ((ι.ctors s c).recursiveTarget f) ls
        (fun p => (sourceParams ι s c p).wkN ((ι.ctors s c).recursiveArity f))
        (sourceIndices E₂ η ls s c f)) := {
    ideal := HasIdeality.ind hI h.block hfn fun p => (hp p).ideal
    subst := HasSubstitution.ind hI h.block fun p => (hp p).subst }
  rw [RecField.instantiatedType, RecField.instantiatedTelescope_id,
    RecField.instantiatedIndices_id]
  exact RawInterpretationProperties.pi (Src := CtxCat.ctorSource h s c) Δ hΔ pΔ _
    (DefeqStrong.indDF hI.param hI.index) hind

theorem RawSound.recursiveSourceProperties :
    RawTeleProperties E₂ (CtxCat.ctorSource h s c).as.ctx (recursiveSourceTele E₂ η ls s c) := by
  apply RawTeleProperties.ofTypes (recursiveSourceTeleStrong h s c)
  intro f
  erw [← Subst.liftN_eq_append, Subst.liftN_id]
  simp only [Subst.id, Expr.var_wkN]
  refine CoherentShape.recursiveTypeProperties s c h _
    (hsound.recursiveArgumentProperties hB hblock s c h _) fun c' => ?_
  rw [hblock]
  exact (hsound.ctorTypeFnProperties hB ((ι.ctors s c).recursiveTarget _) c' ls).ideal

theorem RawSound.fieldTeleProperties
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p)) :
    RawTeleProperties E₂ Γ.as.ctx (((E₂.get η).block.ctors s c).fieldTele η ls ps) ∧
      (∀ v, RawInterpretationProperties (CtxCat.ctorFields h s c)
        ((CtxCat.ctorFieldsHom h s c).subst v)) ∧
      ∀ v, HasFixedness (CtxCat.ctorFields h s c) ((CtxCat.ctorFieldsHom h s c).subst v)
        (((CtxCat.ctorSource h s c).as.ctx.get v).subst (CtxCat.ctorFieldsHom h s c).subst) := by
  let := Subst.category ζ₂ ℓ
  let Src : CtxCat E₂ ℓ := ⟨Ctx.instL ls (E₂.get η).block.params, h.block.paramClosedWF ls⟩
  let O := ((E₂.get η).block.ctors s c).ordinaryFieldTele η ls
    (Subst.id : Subst ζ₂ ℓ ι.nparams ι.nparams)
  have hparams : RawTeleProperties E₂ .nil Src.as.ctx := hsound.paramTeleProperties hB hblock ls
  have hO : WFTeleStrong E₂ (fun _ => True) Src.as.ctx O :=
    (h.block.ctors s c).ordinaryFieldTele
      fun p => Inductive.paramType_var (k := 0) (Δ := #t[]) p Src.as.wf
  have hOeq : O = Ctx.instL ls ((E₂.get η).block.ctors s c).ordinaryTele :=
    (Ctx.substFunctor _).map_id_apply _ _
  have pO : RawTeleProperties E₂ Src.as.ctx O := by
    rw [hOeq]
    simpa [Src, hblock] using
      hsound.ordinaryTeleProperties hB s c ls
  let σ : Γ.as ⟶ Src.as := ⟨ps, (Inductive.paramSubstEqStrong h.param).left⟩
  have pf (p : Fin ι.nparams) : HasFixedness Γ (σ.subst p) ((Src.as.ctx.get p).subst σ.subst) := by
    rw [← Ctx.get_instL, Inductive.paramType_eq_get_subst]
    exact (pps p).fixed
  have pO' := hparams.substitution O hO pO σ (fun p => (pps p).term) pf
  have ⟨pimages, pf'⟩ := hparams.substitution_images O hO pO σ (fun p => (pps p).term) pf
  let R := recursiveSourceTele E₂ η ls s c
  have hctx : Src.as.ctx ++ O = (CtxCat.ctorSource h s c).as.ctx := by
    rw [hOeq]
    exact (Ctx.instL_append _ _ _).symm
  have hR : WFTeleStrong E₂ (fun _ => True) (Src.as.ctx ++ O) R := by
    rw [hctx]
    exact recursiveSourceTeleStrong h s c
  have pR : RawTeleProperties E₂ (Src.as.ctx ++ O) R := by
    rw [hctx]
    exact hsound.recursiveSourceProperties hB hblock s c h
  have pR' := (hparams.append (by simpa using pO)).substitution
    (Src := CtxCat.extendTele Src O hO) R hR pR (σ.liftTele hO) pimages pf'
  have ⟨piR, pfR⟩ := (hparams.append (by simpa using pO)).substitution_images
    (Src := CtxCat.extendTele Src O hO) R hR pR (σ.liftTele hO) pimages pf'
  have ho : Ctx.substN ps (ι.ctors s c).nfields O =
      ((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps := by
    change Ctx.substN ps (ι.ctors s c).nfields
      (((E₂.get η).block.ctors s c).ordinaryFieldTeleAux η ls
        (Subst.id : Subst ζ₂ ℓ ι.nparams ι.nparams) (ι.ctors s c).nfields le_rfl) = _
    simp [Ctor.ordinaryFieldTele, Subst.id, Expr.subst]
  have hr := recursiveSourceTele_subst E₂ η ls s c ps
  let Tctx : Ctx ζ₂ ℓ 0 (Γ.as.len + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields) :=
    Γ.as.ctx ++ Ctx.substN ps (ι.ctors s c).nfields O ++
      Ctx.substN (Subst.liftN ps (ι.ctors s c).nfields) (ι.ctors s c).nrecFields R
  have ht : Tctx = (CtxCat.ctorFields h s c).as.ctx := by
    change Γ.as.ctx ++ Ctx.substN ps (ι.ctors s c).nfields O ++
      Ctx.substN (Subst.liftN ps (ι.ctors s c).nfields) (ι.ctors s c).nrecFields R =
      Γ.as.ctx ++ (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
        ((E₂.get η).block.ctors s c).recursiveFieldTele η ls
          (fun p => (ps p).wkN (ι.ctors s c).nfields)
          (Expr.boundVars Γ.as.len (ι.ctors s c).nfields 0))
    rw [hr, ho, Tele.append_assoc]
  have hsubst (v : Var (ι.nparams + (ι.ctors s c).nfields)) :
      (CtxCat.ctorFieldsHom h s c).subst v =
        ((σ.liftTele hO).liftTele hR).subst (v.castAdd (ι.ctors s c).nrecFields) := by
    rw [CtxCat.ctorFieldsHom_subst]
    exact (Subst.liftN_castAdd _ v _).symm
  have htype (v : Var (ι.nparams + (ι.ctors s c).nfields)) :
      ((CtxCat.ctorSource h s c).as.ctx.get v).subst (CtxCat.ctorFieldsHom h s c).subst =
        (Ctx.get (v.castAdd (ι.ctors s c).nrecFields) (Src.as.ctx ++ O ++ R)).subst
          ((σ.liftTele hO).liftTele hR).subst := by
    rw [Ctx.get_append, ← hctx]
    change _ = ((Ctx.get v (Src.as.ctx ++ O)).wkN (ι.ctors s c).nrecFields).subst
      ((Subst.liftN ps (ι.ctors s c).nfields).liftN (ι.ctors s c).nrecFields)
    rw [Expr.wkN_subst, CtxCat.ctorFieldsHom_subst]
    simp only [Expr.wkN_eq_rename, Expr.subst_rename]
    rfl
  have pi (wf : E₂[Tctx] ⊢ₛ ok) (v : Var (ι.nparams + (ι.ctors s c).nfields)) :
      RawInterpretationProperties (⟨Tctx, wf⟩ : CtxCat E₂ ℓ)
        ((CtxCat.ctorFieldsHom h s c).subst v) := by
    rw [hsubst]
    exact piR (v.castAdd (ι.ctors s c).nrecFields)
  have pfix (wf : E₂[Tctx] ⊢ₛ ok) (v : Var (ι.nparams + (ι.ctors s c).nfields)) :
      HasFixedness (⟨Tctx, wf⟩ : CtxCat E₂ ℓ) ((CtxCat.ctorFieldsHom h s c).subst v)
        (((CtxCat.ctorSource h s c).as.ctx.get v).subst (CtxCat.ctorFieldsHom h s c).subst) := by
    rw [hsubst, htype]
    exact pfR (v.castAdd (ι.ctors s c).nrecFields)
  rw [ht] at pi pfix
  refine ⟨?_, pi (CtxCat.ctorFields h s c).as.wf, pfix (CtxCat.ctorFields h s c).as.wf⟩
  have pall := pO'.append pR'
  change RawTeleProperties E₂ Γ.as.ctx
    (Ctx.substN ps (ι.ctors s c).nfields O ++
      Ctx.substN (Subst.liftN ps (ι.ctors s c).nfields) (ι.ctors s c).nrecFields R) at pall
  rwa [hr, ho] at pall

theorem RawSound.fieldTelescopeProperties
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p)) :
    RawTeleProperties E₂ (CtxCat.ctorFields h s c).as.ctx (fieldTelescope h s c f) :=
  have ⟨_, pimages, pfixed⟩ := hsound.fieldTeleProperties hB hblock s c h pps
  (hsound.ctorSourceProperties hB hblock s c).substitution (Src := CtxCat.ctorSource h s c)
    (sourceTelescope E₂ η ls s c f) (sourceTelescopeStrong h s c f)
    (hsound.recursiveArgumentProperties hB hblock s c h f) (CtxCat.ctorFieldsHom h s c)
    pimages pfixed

theorem RawSound.fieldIndexProperties
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (i : Fin (ι.nindices ((ι.ctors s c).recursiveTarget f))) :
    RawInterpretationProperties (CtxCat.ctorFieldTarget h s c f) (fieldIndices h s c f i) ∧
      HasFixedness (CtxCat.ctorFieldTarget h s c f) (fieldIndices h s c f i)
        ((E₂.get η).block.indexType ls ((ι.ctors s c).recursiveTarget f)
          (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
          (fieldIndices h s c f) i) := by
  have pctx : RawTeleProperties E₂ .nil (CtxCat.ctorSource h s c).as.ctx :=
    hsound.ctorSourceProperties hB hblock s c
  have pargs := hsound.recursiveArgumentProperties hB hblock s c h f
  have ⟨_, pimages, pfixed⟩ := hsound.fieldTeleProperties hB hblock s c h pps
  have ⟨pimages', pfixed'⟩ := pctx.substitution_images
    (sourceTelescope E₂ η ls s c f) (sourceTelescopeStrong h s c f) pargs
    (CtxCat.ctorFieldsHom h s c) pimages pfixed
  have pi := hsound.recursiveIndexProperties hB hblock s c h f i
  let g := (CtxCat.ctorFieldsHom h s c).liftTele (sourceTelescopeStrong h s c f)
  have pfull : RawTeleProperties E₂ .nil (CtxCat.sourceFieldTarget h s c f).as.ctx :=
    pctx.append (by simpa using pargs)
  have hg := SemanticHom.ofImages (CtxCat.sourceFieldTarget h s c f).as.wf pfull g pimages' pfixed'
  have hp := hg.props pi.left
  have hf : HasFixedness _ _ _ :=
    hg.fixed pi.syntactic.left pi.type.subst pi.left.subst pi.fixed
  have hparam (p) : ((sourceParams ι s c p).wkN ((ι.ctors s c).recursiveArity f)).subst g.subst =
      ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f) := by
    change ((sourceParams ι s c p).wkN ((ι.ctors s c).recursiveArity f)).subst
      ((CtxCat.ctorFieldsHom h s c).subst.liftN ((ι.ctors s c).recursiveArity f)) = _
    rw [Expr.wkN_subst]
    exact congrArg (Expr.wkN · _) (Fin.append_left _ _ p)
  have htype : ((E₂.get η).block.indexType ls ((ι.ctors s c).recursiveTarget f)
      (fun p => (sourceParams ι s c p).wkN ((ι.ctors s c).recursiveArity f))
      (sourceIndices E₂ η ls s c f) i).subst g.subst =
      (E₂.get η).block.indexType ls ((ι.ctors s c).recursiveTarget f)
        (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
        (fieldIndices h s c f) i := by
    erw [Inductive.indexType_subst]
    simp only [hparam]
    rfl
  erw [htype] at hf
  exact ⟨hp, hf⟩

theorem RawSound.sourceIndexProperties (h : IndData Γ η ls ps) {Γ₂ : CtxCat E₂ ℓ}
    (σ : Γ₂.as ⟶ (CtxCat.ctorSource h s c).as)
    (pσ : ∀ v, RawInterpretationProperties Γ₂ (σ.subst v))
    (fσ : ∀ v, HasFixedness Γ₂ (σ.subst v) (((CtxCat.ctorSource h s c).as.ctx.get v).subst σ.subst))
    (i : Fin (ι.nindices s)) :
    RawInterpretationProperties Γ₂ (((((E₂.get η).block.ctors s c).targetIndices i).instL ls).subst σ.subst) ∧
      HasFixedness Γ₂ (((((E₂.get η).block.ctors s c).targetIndices i).instL ls).subst σ.subst)
        ((E₂.get η).block.indexType ls s (fun p => σ.subst (p.castAdd (ι.ctors s c).nfields))
          (fun j => ((((E₂.get η).block.ctors s c).targetIndices j).instL ls).subst σ.subst) i) := by
  let Src := CtxCat.ctorSource h s c
  let xs : Fin (ι.nindices s) → Expr ζ₂ ℓ Src.as.len :=
    fun j => (((E₂.get η).block.ctors s c).targetIndices j).instL ls
  have hctx : E₁[Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele)] ⊢ₛ ok :=
    hB.ordinaryClosedWF s c ls (ι.ctors s c).nfields le_rfl
  have hctxeq : (Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele)).map pre.sigs = Src.as.ctx :=
    ctorSource_ctx_map hblock s c
  have psrc : RawJudgment Src (xs i) (xs i)
      ((E₂.get η).block.indexType ls s (sourceParams ι s c) xs i) := by
    have hi : E₁[Ctx.instL ls (I.params ++ (I.ctors s c).ordinaryTele)] ⊢ₛ
        ((I.ctors s c).targetIndices i).instL ls :
          I.indexType ls s (fun p => .var (p.castAdd (ι.ctors s c).nfields))
            (fun j => ((I.ctors s c).targetIndices j).instL ls) i := by
      have hi := ((hB.ctors s c).targetIndices i).instLevel ls
      simp only [Inductive.indexType_instL] at hi
      exact hi
    have hp' := hsound.properties hctx hctxeq Src.as.wf hi
    simp [xs, hblock] at hp' ⊢
    exact hp'
  have pctx : RawTeleProperties E₂ .nil Src.as.ctx := hsound.ctorSourceProperties hB hblock s c
  have hσ := SemanticHom.ofImages Src.as.wf pctx σ pσ fσ
  have ff : HasFixedness Γ₂ ((xs i).subst σ.subst)
      (((E₂.get η).block.indexType ls s (sourceParams ι s c) xs i).subst σ.subst) :=
    hσ.fixed psrc.syntactic.left psrc.type.subst psrc.left.subst psrc.fixed
  rw [Inductive.indexType_subst] at ff
  exact ⟨hσ.props psrc.left, ff⟩

theorem RawSound.targetIndexProperties (h : IndData Γ η ls ps)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (i : Fin (ι.nindices s)) :
    let is := fun i => ((E₂.get η).block.ctors s c).targetIndex ls
      ((ι.ctors s c).fieldParams ps) (ι.ctors s c).fieldOrdinary i
    RawInterpretationProperties (CtxCat.ctorFields h s c) (is i) ∧
      HasFixedness (CtxCat.ctorFields h s c) (is i)
        ((E₂.get η).block.indexType ls s ((ι.ctors s c).fieldParams ps) is i) := by
  have ⟨_, pimages, fimages⟩ := hsound.fieldTeleProperties hB hblock s c h pps
  have hp := hsound.sourceIndexProperties hB hblock s c h (CtxCat.ctorFieldsHom h s c) pimages fimages i
  simp only [CtxCat.ctorFieldsHom, Fin.append_left] at hp
  exact hp

theorem RawSound.instanceIndexProperties (h : IndData Γ η ls ps)
    {fds : Fin (ι.ctors s c).nfields → Expr ζ₂ ℓ Γ.as.len}
    (pps : ∀ p, RawJudgment Γ (ps p) (ps p) ((E₂.get η).block.paramType ls ps p))
    (pf : ∀ f, RawJudgment Γ (fds f) (fds f) (((E₂.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f))
    (i : Fin (ι.nindices s)) :
    RawInterpretationProperties Γ (((E₂.get η).block.ctors s c).targetIndex ls ps fds i) ∧
      HasFixedness Γ (((E₂.get η).block.ctors s c).targetIndex ls ps fds i)
        ((E₂.get η).block.indexType ls s ps (((E₂.get η).block.ctors s c).targetIndex ls ps fds) i) := by
  have hp := hsound.sourceIndexProperties hB hblock s c h
    (⟨Fin.append ps fds, fun v => (ctorSourceJudgment pps pf v).syntactic.left⟩ : Γ.as ⟶ (CtxCat.ctorSource h s c).as)
    (fun v => (ctorSourceJudgment pps pf v).left) (fun v => @(ctorSourceJudgment pps pf v).fixed) i
  simp only [Fin.append_left] at hp
  exact hp

omit hsound hB hblock in
theorem CoherentShape.appliedMajorProperties (h : IndData Γ η ls ps)
    (f : Fin (ι.ctors s c).nrecFields)
    (hctx : RawTeleProperties E₂ .nil (CtxCat.ctorFields h s c).as.ctx)
    (pΔ : RawTeleProperties E₂ (CtxCat.ctorFields h s c).as.ctx (fieldTelescope h s c f))
    (pfn : ∀ c' : Fin (ι.nctors ((ι.ctors s c).recursiveTarget f)),
      HasIdeality (CtxCat.nil E₂ ℓ)
        (((E₂.get η).block.ctorTypeFn ((ι.ctors s c).recursiveTarget f) c').instL
          fun p => ls p))
    (pps : ∀ p, RawInterpretationProperties (CtxCat.ctorFieldTarget h s c f)
      (((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))) :
    RawInterpretationProperties (CtxCat.ctorFieldTarget h s c f) (appliedMajor h s c f) ∧
      HasFixedness (CtxCat.ctorFieldTarget h s c f) (appliedMajor h s c f)
        (.ind η ((ι.ctors s c).recursiveTarget f) ls
          (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
          (fieldIndices h s c f)) := by
  have he := (h.block.ctors s c).fieldRecursive f Γ.as.wf h.param
  rw [RecField.instantiatedType] at he
  have ⟨_, _, hbody⟩ := Ctx.pi_isTypeStrong_inv _ (CtxCat.ctorFields h s c).as.wf
    he.regular.choose_spec
  have hi := IndTyping.ofTyping (Γ₁ := CtxCat.ctorFieldTarget h s c f) h.block hbody
  have pbody : RawInterpretationProperties (CtxCat.ctorFieldTarget h s c f)
      (.ind η ((ι.ctors s c).recursiveTarget f) ls
        (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
        (fieldIndices h s c f)) :=
    ⟨HasIdeality.ind hi h.block pfn fun p => (pps p).ideal,
      HasSubstitution.ind hi h.block fun p => (pps p).subst⟩
  have pe : RawInterpretationProperties (CtxCat.ctorFields h s c)
      ((ι.ctors s c).fieldRecursive f) := .var _ _
  have fe : HasFixedness _ _ _ :=
    HasFixedness.var (CtxCat.ctorFields h s c).as.wf hctx
      (fieldVar h s c (Fin.natAdd (ι.ctors s c).nfields f))
  erw [CtxCat.ctorFields_get_recursive, Ctor.recursiveFieldExpr_eq] at fe
  have hvar : Expr.var (fieldVar h s c (Fin.natAdd (ι.ctors s c).nfields f)) =
      ((ι.ctors s c).fieldRecursive f : Expr ζ₂ ℓ (CtxCat.ctorFields h s c).as.len) := by
    rw [fieldVar_natAdd]
    rfl
  rw [hvar] at fe
  have hp := applyBound_ideal_fixed (fieldTelescopeStrong h s c f) pΔ hbody pbody he pe fe
  exact ⟨⟨hp.1, HasSubstitution.applyBound (fieldTelescopeStrong h s c f) pΔ hbody pbody he pe fe⟩,
    hp.2.1⟩

theorem RawSound.appliedMajorProperties (h : IndData Γ η ls ps) (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (f : Fin (ι.ctors s c).nrecFields) :
    RawInterpretationProperties (CtxCat.ctorFieldTarget h s c f) (appliedMajor h s c f) ∧
      HasFixedness (CtxCat.ctorFieldTarget h s c f) (appliedMajor h s c f)
        (.ind η ((ι.ctors s c).recursiveTarget f) ls
          (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
          (fieldIndices h s c f)) := by
  refine CoherentShape.appliedMajorProperties s c h f
    (hR.append (by simpa using (hsound.fieldTeleProperties hB hblock s c h pps).1))
    (hsound.fieldTelescopeProperties hB hblock s c h f pps) ?_ ?_
  · intro c'
    rw [hblock]
    exact (hsound.ctorTypeFnProperties hB ((ι.ctors s c).recursiveTarget f) c' ls).ideal
  · intro p
    simpa only [CtxCat.ctorFieldTargetHom_param, CtorSig.fieldParams] using
      ((pps p).ctorFieldTarget_properties h s c f).1

theorem RawSound.recursiveMotiveResult (h : IndData Γ η ls ps) (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawTyped Γ (ms s) ((E₂.get η).block.motiveType η ls ps l s))
    (f : Fin (ι.ctors s c).nrecFields) :
    RawJudgment (CtxCat.ctorFieldTarget h s c f)
      (Inductive.motiveResult
        ((ms ((ι.ctors s c).recursiveTarget f)).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
        (fieldIndices h s c f) (appliedMajor h s c f))
      (Inductive.motiveResult
        ((ms ((ι.ctors s c).recursiveTarget f)).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
        (fieldIndices h s c f) (appliedMajor h s c f)) (.sort l) := by
  let g := CtxCat.ctorFieldTargetHom h s c f
  have hps (p : Fin ι.nparams) : E₂[(CtxCat.ctorFieldTarget h s c f).as.ctx] ⊢ₛ (ps p).subst g.subst :
      (E₂.get η).block.paramType ls (fun p => (ps p).subst g.subst) p := by
    simpa using (h.param p).substitution g.typed
  have hms (t : Fin ι.nsorts) : E₂[(CtxCat.ctorFieldTarget h s c f).as.ctx] ⊢ₛ (ms t).subst g.subst :
      (E₂.get η).block.motiveType η ls (fun p => (ps p).subst g.subst) l t := by
    simpa using (pms t).typed.substitution g.typed
  have pp (p) := (pps p).ctorFieldTarget_properties h s c f
  have fp (p) : HasFixedness (CtxCat.ctorFieldTarget h s c f) ((ps p).subst g.subst)
      ((E₂.get η).block.paramType ls (fun p => (ps p).subst g.subst) p) := by
    have hf : HasFixedness (CtxCat.ctorFieldTarget h s c f) ((ps p).subst g.subst)
        (((E₂.get η).block.paramType ls ps p).subst g.subst) := (pp p).2.2
    erw [Inductive.paramType_subst] at hf
    exact hf
  have pΔ := hsound.motiveTeleProperties hB hblock h.block hps
    (fun p => (pp p).1) fp ((ι.ctors s c).recursiveTarget f)
  have ⟨pm, _, fm⟩ := (pms ((ι.ctors s c).recursiveTarget f)).ctorFieldTarget_properties h s c f
  erw [Inductive.motiveType_subst] at fm
  have pi := hsound.fieldIndexProperties hB hblock s c h f pps
  have hi := indexTyping h s c f
  have hm := appliedMajor_typed h s c f
  have ⟨pmaj, fmaj⟩ := hsound.appliedMajorProperties hB hblock s c h hR pps f
  have hp := ctorFieldTargetHom_params h s c f
  erw [← hp] at hi hm pi fmaj
  let hI : IndTyping (CtxCat.ctorFieldTarget h s c f) η ((ι.ctors s c).recursiveTarget f) ls
      (fun p => (ps p).subst g.subst) (fieldIndices h s c f) := ⟨hps, hi⟩
  exact (RawJudgment.motiveResult h.block hI hm (hms _) pΔ pm fm
    (fun i => (pi i).1) (fun i => (pi i).2) pmaj fmaj).1

theorem RawSound.fieldTargetArgProperties (h : IndData Γ η ls ps)
    (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ t, RawTyped Γ (ms t) ((E₂.get η).block.motiveType η ls ps l t))
    (pmins : ∀ t c, RawTyped Γ (mins t c) ((E₂.get η).block.caseFnType η ls ps ms t c))
    (f : Fin (ι.ctors s c).nrecFields) :
    ∀ v, RawInterpretationProperties (CtxCat.ctorFieldTarget h s c f)
      (Inductive.recrSubst
        (fun p => ((ι.ctors s c).fieldParams ps p).wkN ((ι.ctors s c).recursiveArity f))
        (fun t => (ms t).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
        (fun t c₁ => (mins t c₁).subst (CtxCat.ctorFieldTargetHom h s c f).subst)
        (fieldIndices h s c f) (appliedMajor h s c f) v) :=
  Inductive.forall_recrSubst_image
    (fun p => by
      simpa only [CtxCat.ctorFieldTargetHom_param, CtorSig.fieldParams] using
        ((pps p).ctorFieldTarget_properties h s c f).1)
    (fun t => ((pms t).ctorFieldTarget_properties h s c f).1)
    (fun t c₁ => ((pmins t c₁).ctorFieldTarget_properties h s c f).1)
    (fun i => (hsound.fieldIndexProperties hB hblock s c h f pps i).1)
    (hsound.appliedMajorProperties hB hblock s c h hR pps f).1

theorem RawSound.ihTypeProperties (h : IndData Γ η ls ps) (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawTyped Γ (ms s) ((E₂.get η).block.motiveType η ls ps l s))
    (f : Fin (ι.ctors s c).nrecFields) :
    RawInterpretationProperties (CtxCat.ctorFields h s c)
      (((E₂.get η).block.ctors s c).ihType ls ps ms f) := by
  have pe' := hsound.recursiveMotiveResult hB hblock s c h hR pps pms f
  have pΔ := hsound.fieldTelescopeProperties hB hblock s c h f pps
  have hp := RawInterpretationProperties.pi (fieldTelescope h s c f)
    (fieldTelescopeStrong h s c f) pΔ _ pe'.syntactic.left pe'.left
  erw [CtxCat.ctorFieldTargetHom_param] at hp
  exact hp

theorem RawSound.caseTeleProperties (h : IndData Γ η ls ps) (hR : RawTeleProperties E₂ .nil Γ.as.ctx)
    (pps : ∀ p, RawTyped Γ (ps p) ((E₂.get η).block.paramType ls ps p))
    (pms : ∀ s, RawTyped Γ (ms s) ((E₂.get η).block.motiveType η ls ps l s)) :
    RawTeleProperties E₂ Γ.as.ctx ((E₂.get η).block.caseTele η ls ps ms s c) :=
  (hsound.fieldTeleProperties hB hblock s c h pps).1.append
    (RawTeleProperties.ofTypes
      ((h.block.ctors s c).ihTele h.block Γ.as.wf h.param fun t => (pms t).typed)
      (hsound.ihTypeProperties hB hblock s c h hR pps pms))

end Metalean
