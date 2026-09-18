/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Telescope
public import Metalean.Semantics.Soundness.Recursor.Case
public import Metalean.Semantics.Soundness.Recursor.Recovery
public import Metalean.Semantics.Soundness.Telescope.Beta
import Metalean.Semantics.Domain.Decoder.FixedPoint
import Metalean.Semantics.Soundness.Rules.Core
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean

open CoherentShape CodeAssignment CategoryTheory Presheaf IndSig TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ} {Γ : CtxCat E₂ ℓ}
  {ps ps₁ ps₂ : Fin ι.nparams → Expr ζ₂ ℓ Γ.as.len} {ms ms₁ ms₂ : Fin ι.nsorts → Expr ζ₂ ℓ Γ.as.len}
  {mins mins₁ mins₂ : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ ℓ Γ.as.len}
  {is is₁ is₂ : Fin (ι.nindices s) → Expr ζ₂ ℓ Γ.as.len} {maj maj₁ maj₂ : Expr ζ₂ ℓ Γ.as.len}

theorem CoherentShape.RawTyped.var {n : Nat} {ctx : Ctx ζ₂ ℓ 0 n} {hctx : E₂[ctx] ⊢ₛ ok}
    (pctx : RawTeleProperties E₂ .nil ctx) (v : Var n) :
    RawTyped (⟨ctx, hctx⟩ : CtxCat E₂ ℓ) (.var v) (ctx.get v) :=
  ⟨hctx.var v, RawTeleProperties.get hctx pctx v,
    RawInterpretationProperties.var (⟨ctx, hctx⟩ : CtxCat E₂ ℓ) v, HasFixedness.var hctx pctx v⟩

theorem RawSound.recrTeleProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hd : RecDecl E₂ η l)
    (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts) :
    RawTeleProperties E₂ .nil ((E₂.get η).block.recrTele η s ls l) := by
  have hI := hd.block
  have hP : WFTeleStrong E₂ (fun _ => True) .nil (Ctx.instL ls (E₂.get η).block.params) := by
    simpa [Ctx.instL] using hI.params.instLevel (Q := fun _ => True) ls fun _ => trivial
  let P₁ := CtxCat.extendTele (CtxCat.nil E₂ ℓ) _ hP
  have pP : RawTeleProperties E₂ .nil (Ctx.instL ls (E₂.get η).block.params) :=
    hsound.paramTeleProperties hB hblock ls
  have pP₁ : RawTeleProperties E₂ .nil P₁.as.ctx := RawTeleProperties.append .nil pP
  have heq₁ (p : Fin ι.nparams) :
      Ctx.get p P₁.as.ctx = (E₂.get η).block.paramType ls Expr.var p := by
    change Ctx.get p (#t[] ++ Ctx.instL ls (E₂.get η).block.params) = _
    rw [Tele.nil_append, ← Ctx.get_instL, ← Inductive.paramType_eq_get_subst]
    exact (Expr.subst_id _).symm
  have pps₁ (p : Fin ι.nparams) :
      RawTyped P₁ (.var p) ((E₂.get η).block.paramType ls Expr.var p) :=
    heq₁ p ▸ RawTyped.var pP₁ p
  have hM := hI.motiveBinders (l := l) P₁.as.wf fun p => (pps₁ p).typed
  have pM : RawTeleProperties E₂ P₁.as.ctx ((E₂.get η).block.motiveBinders η ls l) :=
    RawTeleProperties.ofTypes (Γ₁ := P₁) (types := (E₂.get η).block.motiveType η ls Expr.var l) hM fun t =>
      RawInterpretationProperties.pi (Src := P₁) (k := ι.nindices t + 1)
        ((E₂.get η).block.motiveTele η ls Expr.var t)
        (hI.motiveTele (s := t) P₁.as.wf fun p => (pps₁ p).typed)
        (hsound.motiveTeleProperties hB hblock hI (fun p => (pps₁ p).typed) (fun p => (pps₁ p).term)
          (fun p => (pps₁ p).fixed) t)
        (.sort l) .sortDF (RawInterpretationProperties.sort _ l)
  let P₂ := CtxCat.extendTele P₁ _ hM
  have pP₂ : RawTeleProperties E₂ .nil P₂.as.ctx :=
    pP₁.append ((Tele.nil_append P₁.as.ctx).symm ▸ pM)
  let ps₂ : Fin ι.nparams → Expr ζ₂ ℓ (ι.nparams + ι.nsorts) := fun p => .var (p.castLE (by omega))
  let ms₂ : Fin ι.nsorts → Expr ζ₂ ℓ (ι.nparams + ι.nsorts) := fun t => .var (Fin.natAdd ι.nparams t)
  have heq₂ (p : Fin ι.nparams) :
      Ctx.get (p.castAdd ι.nsorts) P₂.as.ctx = (E₂.get η).block.paramType ls ps₂ p := by
    rw [Ctx.get_append, heq₁ p, Inductive.paramType_wkN]
    simp only [Expr.var_wkN]
    rfl
  have pps₂ (p : Fin ι.nparams) : RawTyped P₂ (ps₂ p) ((E₂.get η).block.paramType ls ps₂ p) :=
    heq₂ p ▸ RawTyped.var pP₂ (p.castAdd ι.nsorts)
  have pms₂ (t : Fin ι.nsorts) :
      RawTyped P₂ (ms₂ t) ((E₂.get η).block.motiveType η ls ps₂ l t) := by
    have heq : Ctx.get (Fin.natAdd ι.nparams t) P₂.as.ctx =
        (E₂.get η).block.motiveType η ls ps₂ l t := by
      change Ctx.get (Fin.natAdd ι.nparams t)
        (P₁.as.ctx ++ Ctx.ofTypes ((E₂.get η).block.motiveType η ls Expr.var l)) = _
      simp
      rfl
    exact heq ▸ RawTyped.var pP₂ (Fin.natAdd ι.nparams t)
  have hI₂ : IndData P₂ η ls ps₂ := ⟨hI, fun p => (pps₂ p).typed⟩
  have hC := hI.caseBinders (l := l) P₂.as.wf (fun p => (pps₂ p).typed) fun t => (pms₂ t).typed
  have pC : RawTeleProperties E₂ P₂.as.ctx ((E₂.get η).block.caseBinders η ls) := by
    refine RawTeleProperties.ofTypes (Γ₁ := P₂) (types := fun tag =>
      let ⟨t, c⟩ := Fin.decodeSigma ι.nctors tag
      (E₂.get η).block.caseFnType η ls ps₂ ms₂ t c) hC fun tag => ?_
    obtain ⟨⟨t, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
      ⟨_, Fin.encodeSigma_decodeSigma ..⟩
    rw [Fin.decodeSigma_encodeSigma]
    exact hsound.caseFnTypeProperties hB hblock hI₂ pP₂ pps₂ pms₂ t c
  let P₃ := CtxCat.extendTele P₂ _ hC
  have pP₃ : RawTeleProperties E₂ .nil P₃.as.ctx :=
    pP₂.append ((Tele.nil_append P₂.as.ctx).symm ▸ pC)
  let ps₃ : Fin ι.nparams → Expr ζ₂ ℓ (ι.nparams + ι.nsorts + Fin.sum ι.nctors) :=
    fun p => .var (p.castLE (by omega))
  have pps₃ (p : Fin ι.nparams) : RawTyped P₃ (ps₃ p) ((E₂.get η).block.paramType ls ps₃ p) := by
    have heq : Ctx.get ((p.castAdd ι.nsorts).castAdd (Fin.sum ι.nctors)) P₃.as.ctx =
        (E₂.get η).block.paramType ls ps₃ p := by
      change Ctx.get ((p.castAdd ι.nsorts).castAdd (Fin.sum ι.nctors))
        (P₂.as.ctx ++ (E₂.get η).block.caseBinders η ls) = _
      simp only [Ctx.get_append, heq₂ p, Inductive.paramType_wkN, ps₂, Expr.var_wkN]
      rfl
    exact heq ▸ RawTyped.var pP₃ ((p.castAdd ι.nsorts).castAdd (Fin.sum ι.nctors))
  have hIdx := hI.indexTele (s := s) fun p => (pps₃ p).typed
  have pI := hsound.indexTeleProperties hB hblock hI (fun p => (pps₃ p).typed)
    (fun p => (pps₃ p).term) (fun p => (pps₃ p).fixed) s
  let P₄ := CtxCat.extendTele P₃ _ hIdx
  have hmaj : IndTyping P₄ η s ls (fun p => (ps₃ p).wkN (ι.nindices s))
      fun i => .var (Fin.natAdd P₃.as.len i) :=
    IndTyping.ofTyping hI (hI.motiveTele (s := s) P₃.as.wf fun p => (pps₃ p).typed).last.choose_spec.2
  have pfn (c : Fin (ι.nctors s)) := hsound.blockCtorTypeFnProperties η hB hblock s c ls
  have pmaj : RawInterpretationProperties P₄
      (.ind η s ls (fun p => (ps₃ p).wkN (ι.nindices s)) fun i => .var (Fin.natAdd P₃.as.len i)) :=
    ⟨HasIdeality.ind hmaj hI (fun c => (pfn c).ideal)
        fun p => ((pps₃ p).term.wkN _ hIdx).ideal,
      HasSubstitution.ind hmaj hI fun p => ((pps₃ p).term.wkN _ hIdx).subst⟩
  have hnil : P₄.as.ctx =
      Ctx.instL ls (E₂.get η).block.params ++ (E₂.get η).block.motiveBinders η ls l ++
        (E₂.get η).block.caseBinders η ls ++ (E₂.get η).block.indexTele ls s ps₃ :=
    congrArg (· ++ (E₂.get η).block.indexTele ls s ps₃)
      (congrArg (· ++ (E₂.get η).block.caseBinders η ls)
        (congrArg (· ++ (E₂.get η).block.motiveBinders η ls l) (Tele.nil_append _)))
  refine .snoc (hnil ▸ pP₃.append ((Tele.nil_append P₃.as.ctx).symm ▸ pI)) ?_
  show ∀ wf, RawInterpretationProperties (⟨_, wf⟩ : CtxCat E₂ ℓ) _
  rw [Tele.nil_append, ← hnil]
  exact fun _ => pmaj

section Generic

variable (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁) (hblock : (E₂.get η).block = I.map pre.sigs)
  (hd : RecDecl E₂ η l) (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts)

include hsound hB hblock

theorem RawSound.genericTyped (v : Fin (ι.recrEnd s)) :
    RawTyped (CtxCat.recr hd ls s) (.var v)
      ((Ctx.get v ((E₂.get η).block.recrTele η s ls l)).subst
        (Inductive.recrSubst (fun p => .var (RecrBinder.param p).resolve)
          (fun t => .var (RecrBinder.motive t).resolve)
          (fun t c => .var (RecrBinder.case t c).resolve)
          (fun i => .var (RecrBinder.index i).resolve) (.var RecrBinder.major.resolve))) := by
  rw [Inductive.recrSubst_vars, Expr.subst_id]
  exact (congrArg (RawTyped _ _) (congrArg (Ctx.get v) (Tele.nil_append _))).mp
    (RawTyped.var (RawTeleProperties.append .nil (hsound.recrTeleProperties hB hblock hd ls s)) v)

theorem RawSound.genericParam (p : Fin ι.nparams) :
    RawTyped (CtxCat.recr hd ls s) (.var (RecrBinder.param p).resolve)
      ((E₂.get η).block.paramType ls (fun p => .var (RecrBinder.param p).resolve) p) := by
  have hp := hsound.genericTyped hB hblock hd ls s
    (((p.castAdd ι.nsorts).castAdd (Fin.sum ι.nctors)).castAdd (ι.nindices s)).castSucc
  rwa [Inductive.recrTele_get_param_subst] at hp

theorem RawSound.genericMotive (t : Fin ι.nsorts) :
    RawTyped (CtxCat.recr hd ls s) (.var (RecrBinder.motive t).resolve)
      ((E₂.get η).block.motiveType η ls (fun p => .var (RecrBinder.param p).resolve) l t) := by
  have hp := hsound.genericTyped hB hblock hd ls s
    (((Fin.natAdd ι.nparams t).castAdd (Fin.sum ι.nctors)).castAdd (ι.nindices s)).castSucc
  rwa [Inductive.recrTele_get_motive_subst] at hp

theorem RawSound.genericCase (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) :
    RawTyped (CtxCat.recr hd ls s) (.var (RecrBinder.case t c).resolve)
      ((E₂.get η).block.caseFnType η ls (fun p => .var (RecrBinder.param p).resolve)
        (fun t => .var (RecrBinder.motive t).resolve) t c) := by
  have hp := hsound.genericTyped hB hblock hd ls s
    ((Fin.natAdd (ι.nparams + ι.nsorts) (Fin.encodeSigma ι.nctors ⟨t, c⟩)).castAdd (ι.nindices s)).castSucc
  rwa [Inductive.recrTele_get_case_subst] at hp

theorem RawSound.genericIndex (i : Fin (ι.nindices s)) :
    RawTyped (CtxCat.recr hd ls s) (.var (RecrBinder.index i).resolve)
      ((E₂.get η).block.indexType ls s (fun p => .var (RecrBinder.param p).resolve)
        (fun i => .var (RecrBinder.index i).resolve) i) := by
  have hp := hsound.genericTyped hB hblock hd ls s
    (Fin.natAdd (ι.nparams + ι.nsorts + Fin.sum ι.nctors) i).castSucc
  rwa [Inductive.recrTele_get_index_subst] at hp

theorem RawSound.genericMajor :
    RawTyped (CtxCat.recr hd ls s) (.var RecrBinder.major.resolve)
      (.ind η s ls (fun p => .var (RecrBinder.param p).resolve)
        (fun i => .var (RecrBinder.index i).resolve)) := by
  have hp := hsound.genericTyped hB hblock hd ls s (Fin.last _)
  rwa [Inductive.recrTele_get_major_subst] at hp

theorem RawSound.recrBodyProperties :
    RawInterpretationProperties (CtxCat.recr hd ls s) (ι.recrBody s) :=
  have hg := RecTyping.generic hd ls s
  have pps := hsound.genericParam hB hblock hd ls s
  have pms := hsound.genericMotive hB hblock hd ls s
  have pis := hsound.genericIndex hB hblock hd ls s
  RawInterpretationProperties.motiveResult hd.block ⟨hg.param, hg.index⟩ hg.major (hg.motive s)
    (hsound.motiveTeleProperties hB hblock hd.block (fun p => (pps p).typed)
      (fun p => (pps p).term) (fun p => (pps p).fixed) s)
    (pms s).term (pms s).fixed (fun i => (pis i).term) (fun i => (pis i).fixed)
    (hsound.genericMajor hB hblock hd ls s).term

theorem RawSound.recursorPayload_isDirected (hrel : l.rel = true) {V : RecApprox E₂ ℓ ι}
    (hV : ∀ t {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ CtxCat.nil E₂ ℓ) (ρ : RawValuation Ξ),
      ((V t).app _ σ.op ρ).IsDirected)
    ⦃Ξ : CtxCat E₂ ℓ⦄ (σ : Ξ ⟶ CtxCat.recr hd ls s) (υ : RawValuation Ξ)
    (hυ : SourceAdmissible σ υ) :
    ((recursorPayload (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) hd ls V s).app _
      σ.op υ).IsDirected := by
  have hg := RecTyping.generic hd ls s
  have hR := RawTeleProperties.append .nil (hsound.recrTeleProperties hB hblock hd ls s)
  have pps := hsound.genericParam hB hblock hd ls s
  have pms := hsound.genericMotive hB hblock hd ls s
  have pmins := hsound.genericCase hB hblock hd ls s
  have hvar (v : Fin (ι.recrEnd s)) {Ξ' : CtxCat E₂ ℓ} (σ' : Ξ' ⟶ CtxCat.recr hd ls s)
      (υ' : RawValuation Ξ') (hυ' : SourceAdmissible σ' υ') : (υ' (Var.db v)).IsDirected :=
    SourceAdmissible.variable_isDirected hυ' v
  have hideal (c : Fin (ι.nctors s)) (f : Fin (ι.ctors s c).nrecFields)
      (v : Fin (ι.recrEnd ((ι.ctors s c).recursiveTarget f))) :=
    hsound.fieldTargetArgProperties hB hblock s c hg.toIndData hR pps pms pmins f v
  unfold recursorPayload
  rw [RawActionFamily.apply_app, rawRecCaseFamily_value]
  apply rawRecCase_isDirected
  rotate_left
  · exact recoverMajor_isDirected hg.toRecData hrel s _ _ _ _ σ υ (fun _ => hvar _ σ υ hυ) (hvar _ σ υ hυ)
  · intro c Γ₃ σ₂
    exact hvar _ (σ₂ ≫ σ) (υ.pullback σ₂) (hυ.pullback σ₂)
  intro c f Γ₃ σ₂
  exact RawFamily.ctxLam_isDirected _ _ (hsound.fieldTeleProperties hB hblock s c hg.toIndData pps).1 _
    (fun _ σ' υ' hυ' => RawFamily.ctxLam_isDirected _ _
      (hsound.fieldTelescopeProperties hB hblock s c hg.toIndData f pps) _
      (fun _ σ'' υ'' hυ'' => by
        rw [RawFamily.closedApps_value]
        exact rawApps_isDirected ⟨_, hV _ _ _⟩ _ fun v => ⟨_, (hideal c f v).ideal σ'' υ'' hυ''⟩)
      σ' υ' hυ')
    (σ₂ ≫ σ) (υ.pullback σ₂) (hυ.pullback σ₂)

theorem RawSound.recursorBody_isDirected (hrel : l.rel = true) {V : RecApprox E₂ ℓ ι}
    (hV : ∀ t {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ CtxCat.nil E₂ ℓ) (ρ : RawValuation Ξ),
      ((V t).app _ σ.op ρ).IsDirected)
    ⦃Ξ : CtxCat E₂ ℓ⦄ (σ : Ξ ⟶ CtxCat.recr hd ls s) (υ : RawValuation Ξ)
    (hυ : SourceAdmissible σ υ) :
    ((recursorBody (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) hd ls V s).app _
      σ.op υ).IsDirected := by
  apply (piLimit E₂ ℓ).rawExtend_isDirected
  · exact (hsound.recrBodyProperties hB hblock hd ls s).ideal σ υ hυ
  · exact hsound.recursorPayload_isDirected hB hblock hd ls s hrel hV σ υ hυ

theorem RawSound.recursor_isDirected (hrel : l.rel = true) (t : Fin ι.nsorts)
    {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ CtxCat.nil E₂ ℓ) (ρ : RawValuation Ξ) :
    ((recursor (piLimit E₂ ℓ) hd ls t).app _ σ.op ρ).IsDirected := by
  let step := recursorStep (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) hd ls
  have hiter (n : Nat) : ∀ t {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ CtxCat.nil E₂ ℓ) (ρ : RawValuation Ξ),
      ((step^[n] ⊥ t).app _ σ.op ρ).IsDirected := by
    induction n with
    | zero => exact fun _ _ _ _ => ΩLower.isDirected_bot
    | succ n ih =>
      intro t Ξ σ ρ
      rw [Function.iterate_succ_apply']
      exact RawFamily.ctxLam_isDirected _ _ (hsound.recrTeleProperties hB hblock hd ls t)
        (recrTele_headRank_lt η ls t)
        (hsound.recursorBody_isDirected hB hblock hd ls t hrel ih) σ ρ (.nil σ ρ)
  have hmono : Monotone fun n => step^[n] ⊥ := Monotone.monotone_iterate_of_le_map step.monotone bot_le
  change ((OrderHom.lfp step t).app _ σ.op ρ).IsDirected
  rw [fixedPoints.lfp_eq_sSup_iterate step (recursorStep_ωScottContinuous _ _ hd ls),
    RecApprox.iSup_apply, RawFamily.iSup_app]
  exact ΩLower.IsDirected.iSup
    (Monotone.directed_le fun _ _ hab => hmono hab t _ σ.op ρ) fun n => hiter n t σ ρ

end Generic

theorem CoherentShape.RawJudgment.recrSubst
    (pps : ∀ p, RawJudgment Γ (ps₁ p) (ps₂ p) ((E₂.get η).block.paramType ls ps₁ p))
    (pms : ∀ t, RawJudgment Γ (ms₁ t) (ms₂ t) ((E₂.get η).block.motiveType η ls ps₁ l t))
    (pmins : ∀ t c, RawJudgment Γ (mins₁ t c) (mins₂ t c)
      ((E₂.get η).block.caseFnType η ls ps₁ ms₁ t c))
    (pis : ∀ i, RawJudgment Γ (is₁ i) (is₂ i) ((E₂.get η).block.indexType ls s ps₁ is₁ i))
    (pmaj : RawJudgment Γ maj₁ maj₂ (.ind η s ls ps₁ is₁)) (v : Fin (ι.recrEnd s)) :
    RawJudgment Γ (Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁ v)
      (Inductive.recrSubst ps₂ ms₂ mins₂ is₂ maj₂ v)
      ((Ctx.get v ((E₂.get η).block.recrTele η s ls l)).subst
        (Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁)) :=
  Inductive.forall_recrSubst (motive := fun _ e₁ e₂ t => RawJudgment Γ e₁ e₂ t) pps pms pmins pis pmaj v

theorem CoherentShape.HasIdeality.recr_prop (hrel : l.rel = false) :
    HasIdeality Γ (.recr η s ls l ps ms mins is maj) := fun _ _ _ _ => by
  rw [rawInterpret_recr_prop _ hrel]
  exact ΩLower.isDirected_bot

theorem CoherentShape.HasSubstitution.recr_prop (hrel : l.rel = false) :
    HasSubstitution Γ (.recr η s ls l ps ms mins is maj) := fun _ _ σ _ _ _ _ _ => by
  change (rawInterpret (piLimit E₂ ℓ) _ (.recr η s ls l (fun p => (ps p).subst σ.subst)
    (fun s₁ => (ms s₁).subst σ.subst) (fun s₁ c₁ => (mins s₁ c₁).subst σ.subst)
    (fun i => (is i).subst σ.subst) (maj.subst σ.subst))).app _ _ _ = _
  rw [rawInterpret_recr_prop _ hrel, rawInterpret_recr_prop _ hrel]
  rfl

theorem CoherentShape.HasFixedness.recr_prop (hrel : l.rel = false) :
    HasFixedness Γ (.recr η s ls l ps ms mins is maj) (Inductive.motiveResult (ms s) is maj) :=
  fun _ _ _ _ _ => by
    rw [rawInterpret_recr_prop _ hrel]
    exact rawExtend_bottom_payload piLimit_isPayloadStrict _ _

theorem CoherentShape.HasSubstitution.recr (h : RecTyping Γ η s ls l ps ms mins is maj)
    (pargs : ∀ v, HasSubstitution Γ (Inductive.recrSubst ps ms mins is maj v)) :
    HasSubstitution Γ (.recr η s ls l ps ms mins is maj) := by
  intro Γ₂ Γ₃ σ₁ σ₂ ρs ρt hσ hadm
  cases hrel : l.rel with
  | false => exact HasSubstitution.recr_prop hrel σ₁ σ₂ ρs ρt hσ hadm
  | true =>
    have hterm (v : Fin (ι.recrEnd s)) :=
      congrFun (Inductive.recrSubst_comp (ps₁ := ps) (ms₁ := ms) (mins₁ := mins) (is₁ := is)
        (maj₁ := maj) σ₁.subst) v
    have hlabel {e₁ e₂ t₁ t₂ : Expr ζ₂ ℓ Γ₂.as.len} (he₁ : E₂[Γ₂.as.ctx] ⊢ₛ e₁ : t₁)
        (he₂ : E₂[Γ₂.as.ctx] ⊢ₛ e₂ : t₂) (he : e₁ = e₂) (ht : t₁ = t₂) :
        Tm.label Γ₂.as he₁ = Tm.label Γ₂.as he₂ := by
      subst he ht
      rfl
    change (rawInterpret (piLimit E₂ ℓ) Γ₂ (.recr η s ls l (fun p => (ps p).subst σ₁.subst)
      (fun t => (ms t).subst σ₁.subst) (fun t c => (mins t c).subst σ₁.subst)
      (fun i => (is i).subst σ₁.subst) (maj.subst σ₁.subst))).app _ σ₂.op ρt = _
    rw [rawInterpret_recr _ (h.subst σ₁) hrel, rawInterpret_recr _ h hrel, RawFamily.closedApps_value,
      RawFamily.closedApps_value]
    congr 1
    · exact congrArg (fun τ => (recursor (piLimit E₂ ℓ) h.toRecDecl ls s).app _ (Quiver.Hom.op τ) fun _ => ⊥)
        (CtxCat.hom_nil_eq _ _)
    · funext v
      rw [op_comp, Functor.map_comp_apply, Tm.map_label]
      exact congrArg _ (hlabel _ _ (hterm v).symm (by rw [Expr.subst_subst, Inductive.recrSubst_comp]))
    · funext v
      rw [← hterm v]
      exact pargs v σ₁ σ₂ ρs ρt hσ hadm

theorem CoherentShape.HasEquality.recr (h₁ : RecTyping Γ η s ls l ps₁ ms₁ mins₁ is₁ maj₁)
    (h₂ : RecTyping Γ η s ls l ps₂ ms₂ mins₂ is₂ maj₂)
    (hargs : ∀ v, E₂[Γ.as.ctx] ⊢ₛ Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁ v ≡
      Inductive.recrSubst ps₂ ms₂ mins₂ is₂ maj₂ v :
      (Ctx.get v ((E₂.get η).block.recrTele η s ls l)).subst (Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁))
    (eargs : ∀ v, HasEquality Γ (Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁ v)
      (Inductive.recrSubst ps₂ ms₂ mins₂ is₂ maj₂ v)) :
    HasEquality Γ (.recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁) (.recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂) := by
  intro Ξ σ ρ hρ
  cases hrel : l.rel with
  | false => rw [rawInterpret_recr_prop _ hrel, rawInterpret_recr_prop _ hrel]
  | true =>
    have hσ : E₂[Γ.as.ctx] ⊢ₛ Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁ ≡
        Inductive.recrSubst ps₂ ms₂ mins₂ is₂ maj₂ ⊣ (CtxCat.recr h₁.toRecDecl ls s).as.ctx :=
      fun v => (congrArg (fun X => E₂[Γ.as.ctx] ⊢ₛ _ ≡ _ : (Ctx.get v X).subst _)
        (Tele.nil_append _)).mpr (hargs v)
    rw [rawInterpret_recr _ h₁ hrel, rawInterpret_recr _ h₂ hrel, RawFamily.closedApps_value,
      RawFamily.closedApps_value]
    congr 1
    · funext v
      exact congrArg _ (Tm.label_eq (IsTypeEq.substitution_congr (CtxCat.recr h₁.toRecDecl ls s).as.wf hσ
        (IsTypeStrong.isTypeEq ((CtxCat.recr h₁.toRecDecl ls s).as.wf.var v).regular)) (hσ v))
    · funext v
      exact eargs v σ ρ hρ

variable (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁) (hblock : (E₂.get η).block = I.map pre.sigs)

include hsound hB hblock

section RecrArgs

variable (h : RecTyping Γ η s ls l ps ms mins is maj)
  (pargs : ∀ v, RawInterpretationProperties Γ (Inductive.recrSubst ps ms mins is maj v))
  (fargs : ∀ v, HasFixedness Γ (Inductive.recrSubst ps ms mins is maj v)
    ((Ctx.get v ((E₂.get η).block.recrTele η s ls l)).subst (Inductive.recrSubst ps ms mins is maj)))

include h in
theorem RawSound.recr_ideal (iargs : ∀ v, HasIdeality Γ (Inductive.recrSubst ps ms mins is maj v)) :
    HasIdeality Γ (.recr η s ls l ps ms mins is maj) := by
  intro Ξ σ ρ hρ
  cases hrel : l.rel with
  | false => exact HasIdeality.recr_prop hrel σ ρ hρ
  | true =>
    rw [rawInterpret_recr _ h hrel, RawFamily.closedApps_value]
    exact rawApps_isDirected ⟨_, hsound.recursor_isDirected hB hblock h.toRecDecl ls hrel s _ _⟩ _
      fun v => ⟨_, iargs v σ ρ hρ⟩

include h pargs fargs in
theorem RawSound.recrHom_admissible
    {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ Γ) (ρ : RawValuation Ξ) (hρ : SourceAdmissible σ ρ) :
    SourceAdmissible (σ ≫ RawCtx.toCtx.map h.recrHom)
        (RawValuation.pushFin (fun _ => ⊥)
          fun v => (rawInterpret (piLimit E₂ ℓ) Γ (Inductive.recrSubst ps ms mins is maj v)).app _ σ.op ρ) :=
  RawTeleProperties.admissible_of_images (CtxCat.recr h.toRecDecl ls s).as.wf
    (RawTeleProperties.append .nil (hsound.recrTeleProperties hB hblock h.toRecDecl ls s))
    h.recrHom σ ρ hρ (fun v => (pargs v).ideal) (fun v => (pargs v).subst) fun v =>
      (congrArg (fun X => HasFixedness Γ _ ((Ctx.get v X).subst _)) (Tele.nil_append _)).mpr (fargs v)

include h pargs fargs in
theorem RawSound.recr_eval (hrel : l.rel = true)
    {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ Γ) (ρ : RawValuation Ξ) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ (.recr η s ls l ps ms mins is maj)).app _ σ.op ρ =
      (recursorBody (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) h.toRecDecl ls
        (recursor (piLimit E₂ ℓ) h.toRecDecl ls) s).app _ (σ ≫ RawCtx.toCtx.map h.recrHom).op
        (RawValuation.pushFin (fun _ => ⊥)
          fun v => (rawInterpret (piLimit E₂ ℓ) Γ (Inductive.recrSubst ps ms mins is maj v)).app _ σ.op ρ) := by
  have hd := h.toRecDecl
  have hβ := RawFamily.ctxLam_beta hd.block.recrTele (hsound.recrTeleProperties hB hblock hd ls s)
    (recrTele_headRank_lt η ls s)
    (recursorBody (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) hd ls
      (recursor (piLimit E₂ ℓ) hd ls) s)
    (recursorBody_isFinitary _ _ hd ls (fun Γ e _ => rawInterpret_isFinitary _ Γ e)
      (recursorWith_isFinitary _ _ hd ls fun Γ e _ => rawInterpret_isFinitary _ Γ e) s)
    (hsound.recursorBody_isDirected hB hblock hd ls s hrel
      (hsound.recursor_isDirected hB hblock hd ls hrel))
    (σ ≫ RawCtx.toCtx.map h.recrHom) _ (hsound.recrHom_admissible hB hblock h pargs fargs σ ρ hρ)
  rw [RawValuation.tailN_pushFin] at hβ
  rw [rawInterpret_recr _ h hrel, RawFamily.closedApps_value, recursor_unfold]
  refine Eq.trans ?_ hβ
  congr 1
  · exact congrArg (fun τ => (RawFamily.ctxLam (piLimit E₂ ℓ) _ (CtxCat.nil E₂ ℓ) _ hd.block.recrTele
      (recrTele_headRank_lt η ls s) _).app _ (Quiver.Hom.op τ) fun _ => ⊥) (CtxCat.hom_nil_eq _ _)
  · funext v
    rw [op_comp, Functor.map_comp_apply]
    rfl
  · funext v
    rw [RawValuation.pushFin_variable]

include h pargs fargs in
theorem RawSound.recr_type_eq
    {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ Γ) (ρ : RawValuation Ξ) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ (Inductive.motiveResult (ms s) is maj)).app _ σ.op ρ =
      (rawInterpret (piLimit E₂ ℓ) (CtxCat.recr h.toRecDecl ls s) (ι.recrBody s)).app _
        (σ ≫ RawCtx.toCtx.map h.recrHom).op
        (RawValuation.pushFin (fun _ => ⊥)
          fun v => (rawInterpret (piLimit E₂ ℓ) Γ (Inductive.recrSubst ps ms mins is maj v)).app _ σ.op ρ) := by
  have htype := (hsound.recrBodyProperties hB hblock h.toRecDecl ls s).subst h.recrHom σ _ ρ
    (SemanticSubstitution.ofHom (CtxCat.recr h.toRecDecl ls s).as.wf h.recrHom σ ρ
      (fun v => (pargs v).subst) hρ)
    (hsound.recrHom_admissible hB hblock h pargs fargs σ ρ hρ)
  change (rawInterpret (piLimit E₂ ℓ) Γ ((ι.recrBody s).subst
    (Inductive.recrSubst ps ms mins is maj))).app _ σ.op ρ = _ at htype
  rwa [IndSig.recrBody_subst] at htype

include h pargs fargs in
theorem RawSound.recr_value (hrel : l.rel = true)
    (he : E₂[Γ.as.ctx] ⊢ₛ .recr η s ls l ps ms mins is maj : Inductive.motiveResult (ms s) is maj)
    {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ Γ) (ρ : RawValuation Ξ) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ (.recr η s ls l ps ms mins is maj)).app _ σ.op ρ =
      (piLimit E₂ ℓ).rawExtend
        ((rawInterpret (piLimit E₂ ℓ) Γ (Inductive.motiveResult (ms s) is maj)).app _ σ.op ρ)
        ((Tm E₂ ℓ).map σ.op (Tm.label Γ.as he))
        ((recursorPayload (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) h.toRecDecl ls
          (recursor (piLimit E₂ ℓ) h.toRecDecl ls) s).app _ (σ ≫ RawCtx.toCtx.map h.recrHom).op
          (RawValuation.pushFin (fun _ => ⊥)
          fun v => (rawInterpret (piLimit E₂ ℓ) Γ (Inductive.recrSubst ps ms mins is maj v)).app _ σ.op ρ)) := by
  have hbodyEq : (ι.recrBody s).subst h.recrHom.subst = Inductive.motiveResult (ms s) is maj :=
    IndSig.recrBody_subst ..
  have hrecEq : (Expr.recr η s ls l (fun p => .var (RecrBinder.param p).resolve)
      (fun t => .var (RecrBinder.motive t).resolve) (fun t c => .var (RecrBinder.case t c).resolve)
      (fun i => .var (RecrBinder.index i).resolve) (.var RecrBinder.major.resolve)).subst
        h.recrHom.subst = .recr η s ls l ps ms mins is maj := by
    simp [Expr.subst, RecTyping.recrHom]
  have hlabel : (Tm E₂ ℓ).map (σ ≫ RawCtx.toCtx.map h.recrHom).op
      (Tm.label (CtxCat.recr h.toRecDecl ls s).as (RecTyping.recrBody_typed h.toRecDecl ls s)) =
      (Tm E₂ ℓ).map σ.op (Tm.label Γ.as he) := by
    rw [op_comp, Functor.map_comp_apply]
    have ht' : E₂[Γ.as.ctx] ⊢ₛ (ι.recrBody s).subst h.recrHom.subst ≡
        Inductive.motiveResult (ms s) is maj typ := by
      rw [hbodyEq]
      exact IsTypeStrong.isTypeEq he.regular
    have he' : E₂[Γ.as.ctx] ⊢ₛ (Expr.recr η s ls l (fun p => .var (RecrBinder.param p).resolve)
        (fun t => .var (RecrBinder.motive t).resolve) (fun t c => .var (RecrBinder.case t c).resolve)
        (fun i => .var (RecrBinder.index i).resolve) (.var RecrBinder.major.resolve)).subst
          h.recrHom.subst ≡ .recr η s ls l ps ms mins is maj : (ι.recrBody s).subst h.recrHom.subst := by
      rwa [hrecEq, hbodyEq]
    exact congrArg _ (Tm.label_eq ht' he')
  rw [hsound.recr_eval hB hblock h pargs fargs hrel σ ρ hρ,
    hsound.recr_type_eq hB hblock h pargs fargs σ ρ hρ, recursorBody, RawFamily.decode_app_hom_coe,
    hlabel]

include h pargs fargs in
theorem RawSound.recr_fixed :
    HasFixedness Γ (.recr η s ls l ps ms mins is maj) (Inductive.motiveResult (ms s) is maj) := by
  intro Ξ he σ ρ hρ
  cases hrel : l.rel with
  | false => exact HasFixedness.recr_prop hrel he σ ρ hρ
  | true =>
    have hadm := hsound.recrHom_admissible hB hblock h pargs fargs σ ρ hρ
    have hT : ((rawInterpret (piLimit E₂ ℓ) Γ (Inductive.motiveResult (ms s) is maj)).app _ σ.op ρ).IsDirected := by
      rw [hsound.recr_type_eq hB hblock h pargs fargs σ ρ hρ]
      exact (hsound.recrBodyProperties hB hblock h.toRecDecl ls s).ideal _ _ hadm
    rw [hsound.recr_value hB hblock h pargs fargs hrel he σ ρ hρ]
    exact (piLimit E₂ ℓ).rawExtend_idempotent piLimit_isIdempotent _ hT
      (hsound.recursorPayload_isDirected hB hblock h.toRecDecl ls s hrel
        (hsound.recursor_isDirected hB hblock h.toRecDecl ls hrel) _ _ hadm)

end RecrArgs

theorem CoherentShape.RawJudgment.recrDF (h₁ : RecTyping Γ η s ls l ps₁ ms₁ mins₁ is₁ maj₁)
    (h₂ : RecTyping Γ η s ls l ps₂ ms₂ mins₂ is₂ maj₂)
    (hrec : E₂[Γ.as.ctx] ⊢ₛ .recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁ ≡ .recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂ :
      Inductive.motiveResult (ms₁ s) is₁ maj₁)
    (pargs : ∀ v, RawJudgment Γ (Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁ v)
      (Inductive.recrSubst ps₂ ms₂ mins₂ is₂ maj₂ v)
      ((Ctx.get v ((E₂.get η).block.recrTele η s ls l)).subst (Inductive.recrSubst ps₁ ms₁ mins₁ is₁ maj₁)))
    (ptype : RawJudgment Γ (Inductive.motiveResult (ms₁ s) is₁ maj₁)
      (Inductive.motiveResult (ms₂ s) is₂ maj₂) (.sort l)) :
    RawJudgment Γ (.recr η s ls l ps₁ ms₁ mins₁ is₁ maj₁) (.recr η s ls l ps₂ ms₂ mins₂ is₂ maj₂)
      (Inductive.motiveResult (ms₁ s) is₁ maj₁) where
  syntactic := hrec
  type := ptype.left
  left := ⟨hsound.recr_ideal hB hblock h₁ fun v => (pargs v).left.ideal,
    HasSubstitution.recr h₁ fun v => (pargs v).left.subst⟩
  right := ⟨hsound.recr_ideal hB hblock h₂ fun v => (pargs v).right.ideal,
    HasSubstitution.recr h₂ fun v => (pargs v).right.subst⟩
  equal := HasEquality.recr h₁ h₂ (fun v => (pargs v).syntactic) fun v => (pargs v).equal
  fixed := hsound.recr_fixed hB hblock h₁ (fun v => (pargs v).left) fun v => (pargs v).fixed

end Metalean
