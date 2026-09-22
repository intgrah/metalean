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
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

open CoherentShape CodeAssignment CategoryTheory Presheaf IndSig

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ} {Γ : CtxCat E₂ ℓ}
  {ps ps₁ ps₂ : Fin ι.nparams → Expr ζ₂ ℓ Γ.as.len} {ms ms₁ ms₂ : Fin ι.nsorts → Expr ζ₂ ℓ Γ.as.len}
  {mins mins₁ mins₂ : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ ℓ Γ.as.len}
  {is is₁ is₂ : Fin (ι.nindices s) → Expr ζ₂ ℓ Γ.as.len} {maj maj₁ maj₂ : Expr ζ₂ ℓ Γ.as.len}

theorem RawSound.recrTeleProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hd : RecDecl E₂ η l)
    (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts) :
    RawTeleProperties E₂ .nil ((E₂.get η).block.recrTele η s ls l) := by
  have hI := hd.block
  let P₁ : CtxCat E₂ ℓ := ⟨Ctx.instL ls (E₂.get η).block.params, hI.paramClosedWF ls⟩
  have pP₁ : RawTeleProperties E₂ .nil P₁.as.ctx := hsound.paramTeleProperties hB hblock ls
  have heq₁ (p : Fin ι.nparams) :
      Ctx.get p P₁.as.ctx = (E₂.get η).block.paramType ls Expr.var p := by
    change Ctx.get p (Ctx.instL ls (E₂.get η).block.params) = _
    rw [← Ctx.get_instL, ← Inductive.paramType_eq_get_subst]
    exact (Expr.subst_id _).symm
  have pps₁ (p : Fin ι.nparams) :
      RawTyped P₁ (.var p) ((E₂.get η).block.paramType ls Expr.var p) :=
    heq₁ p ▸ (RawJudgment.var pP₁ p).toRawTyped
  have hM := hI.motiveBinders (l := l) P₁.as.wf fun p => (pps₁ p).typed
  have pM : RawTeleProperties E₂ P₁.as.ctx ((E₂.get η).block.motiveBinders η ls l) :=
    RawTeleProperties.ofTypes (Γ₁ := P₁) (types := (E₂.get η).block.motiveType η ls Expr.var l) hM fun t =>
      RawInterpretationProperties.pi (Src := P₁)
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
  have pps₂ (p : Fin ι.nparams) : RawTyped P₂ (ps₂ p) ((E₂.get η).block.paramType ls ps₂ p) := by
    have q := (SemanticHom.teleProjection hM).typed (pps₁ p)
    simp only [Inductive.paramType_subst] at q
    exact q
  have pms₂ (t : Fin ι.nsorts) :
      RawTyped P₂ (ms₂ t) ((E₂.get η).block.motiveType η ls ps₂ l t) := by
    have heq : Ctx.get (Fin.natAdd ι.nparams t) P₂.as.ctx =
        (E₂.get η).block.motiveType η ls ps₂ l t := by
      change Ctx.get (Fin.natAdd ι.nparams t)
        (P₁.as.ctx ++ Ctx.ofTypes ((E₂.get η).block.motiveType η ls Expr.var l)) = _
      simp
      rfl
    exact heq ▸ (RawJudgment.var pP₂ (Fin.natAdd ι.nparams t)).toRawTyped
  have hI₂ : IndData P₂ η ls ps₂ := ⟨hI, fun p => (pps₂ p).typed⟩
  have hC := hI.caseBinders (l := l) P₂.as.wf (fun p => (pps₂ p).typed) fun t => (pms₂ t).typed
  have pC : RawTeleProperties E₂ P₂.as.ctx ((E₂.get η).block.caseBinders η ls) := by
    refine RawTeleProperties.ofTypes (Γ₁ := P₂) (types := fun tag =>
      let ⟨t, c⟩ := Fin.decodeSigma ι.nctors tag
      (E₂.get η).block.caseFnType η ls ps₂ ms₂ t c) hC fun tag => ?_
    obtain ⟨⟨t, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
      ⟨_, Fin.encodeSigma_decodeSigma ..⟩
    rw [Fin.decodeSigma_encodeSigma]
    have hΔ := hI.caseTele (s := t) (c := c) P₂.as.wf hI₂.param fun t => (pms₂ t).typed
    exact .pi _ hΔ (hsound.caseTeleProperties hB hblock t c hI₂ pP₂ pps₂ pms₂) _
      (hI.caseType_congr (hΔ.appendCtxWFStrong P₂.as.wf)
        (Inductive.caseParams_congr · hI₂.param)
        (Inductive.caseMotives_congr · fun t => (pms₂ t).typed)
        (hI.caseOrdinary_typed · hI₂.param)
        (hI.caseRecursive_typed · P₂.as.wf hI₂.param))
      (hsound.caseTypeProperties hB hblock hI₂ pps₂ pms₂ t c _)
  let P₃ := CtxCat.extendTele P₂ _ hC
  have pP₃ : RawTeleProperties E₂ .nil P₃.as.ctx :=
    pP₂.append ((Tele.nil_append P₂.as.ctx).symm ▸ pC)
  let ps₃ : Fin ι.nparams → Expr ζ₂ ℓ (ι.nparams + ι.nsorts + Fin.sum ι.nctors) :=
    fun p => .var (p.castLE (by omega))
  have pps₃ (p : Fin ι.nparams) : RawTyped P₃ (ps₃ p) ((E₂.get η).block.paramType ls ps₃ p) := by
    have q := (SemanticHom.teleProjection hC).typed (pps₂ p)
    simp only [Inductive.paramType_subst] at q
    exact q
  exact pP₃.append (by
    simpa using hsound.motiveTeleProperties hB hblock hI (fun p => (pps₃ p).typed)
      (fun p => (pps₃ p).term) (fun p => (pps₃ p).fixed) s)

section Generic

variable (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁) (hblock : (E₂.get η).block = I.map pre.sigs)
  (hd : RecDecl E₂ η l) (ls : Fin ι.nlevels → Level ℓ) (s : Fin ι.nsorts)

include hsound hB hblock

theorem RawSound.genericTyped (b : RecrBinder ι s) :
    RawTyped (CtxCat.recr hd ls s) (.var b.resolve)
      ((E₂.get η).block.recrBinderType η ls l (fun p => .var (RecrBinder.param p).resolve)
        (fun t => .var (RecrBinder.motive t).resolve) (fun i => .var (RecrBinder.index i).resolve) b) := by
  have ht := (E₂.get η).block.recrTele_get_subst η ls l
    (fun p => .var (RecrBinder.param p).resolve) (fun t => .var (RecrBinder.motive t).resolve)
    (fun t c => .var (RecrBinder.case t c).resolve) (fun i => .var (RecrBinder.index i).resolve)
    (.var RecrBinder.major.resolve) b
  rw [Inductive.recrSubst_vars, Expr.subst_id] at ht
  rw [← ht]
  simpa [CtxCat.recr, CtxCat.extendTele, CtxCat.nil] using
    (RawJudgment.var (Γ₁ := CtxCat.recr hd ls s)
      (RawTeleProperties.append .nil (hsound.recrTeleProperties hB hblock hd ls s)) b.resolve).toRawTyped

theorem RawSound.recrBodyProperties :
    RawInterpretationProperties (CtxCat.recr hd ls s) (ι.recrBody s) :=
  have hg := RecTyping.generic hd ls s
  have pps := fun p => hsound.genericTyped hB hblock hd ls s (.param p)
  have pms := fun t => hsound.genericTyped hB hblock hd ls s (.motive t)
  have pis := fun i => hsound.genericTyped hB hblock hd ls s (.index i)
  RawInterpretationProperties.motiveResult hd.block ⟨hg.param, hg.index⟩ hg.major (hg.motive s)
    (hsound.motiveTeleProperties hB hblock hd.block (fun p => (pps p).typed)
      (fun p => (pps p).term) (fun p => (pps p).fixed) s)
    (pms s).term (pms s).fixed (fun i => (pis i).term) (fun i => (pis i).fixed)
    (hsound.genericTyped hB hblock hd ls s .major).term

theorem RawSound.recursorPayload_isDirected (hrel : l.rel = true) {V : RecApprox E₂ ℓ ι}
    (hV : ∀ t {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ CtxCat.nil E₂ ℓ) (ρ : RawValuation Ξ),
      ((V t).app _ σ.op ρ).IsDirected)
    ⦃Ξ : CtxCat E₂ ℓ⦄ (σ : Ξ ⟶ CtxCat.recr hd ls s) (υ : RawValuation Ξ)
    (hυ : SourceAdmissible σ υ) :
    ((recursorPayload (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) hd ls V s).app _
      σ.op υ).IsDirected := by
  have hg := RecTyping.generic hd ls s
  have hR := RawTeleProperties.append .nil (hsound.recrTeleProperties hB hblock hd ls s)
  have pps := fun p => hsound.genericTyped hB hblock hd ls s (.param p)
  have pms := fun t => hsound.genericTyped hB hblock hd ls s (.motive t)
  have pmins := fun t c => hsound.genericTyped hB hblock hd ls s (.case t c)
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
        exact rawApps_isDirected ⟨_, hV _ _ _⟩ _ fun v => ⟨_, (hideal c f v).term.ideal σ'' υ'' hυ''⟩)
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
      refine congr((Tm E₂ ℓ).map σ₂.op (Tm.label _ (e := $((hterm v).symm)) (t := $(?_)) _))
      simp [RecTyping.recrHom, Inductive.recrSubst_comp]
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
      fun v => (congrArg (fun X => E₂[Γ.as.ctx] ⊢ₛ _ : (Ctx.get v X).subst _)
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
    h.recrHom σ ρ hρ pargs fun v =>
      (congrArg (fun X => HasFixedness Γ _ ((Ctx.get v X).subst _)) (Tele.nil_append _)).mpr (fargs v)

include h pargs fargs in
theorem RawSound.recr_value (hrel : l.rel = true)
    {Ξ : CtxCat E₂ ℓ} (σ : Ξ ⟶ Γ) (ρ : RawValuation Ξ) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ (.recr η s ls l ps ms mins is maj)).app _ σ.op ρ =
      (piLimit E₂ ℓ).rawExtend
        ((rawInterpret (piLimit E₂ ℓ) Γ (Inductive.motiveResult (ms s) is maj)).app _ σ.op ρ)
        ((Tm E₂ ℓ).map σ.op (Tm.label Γ.as h.typed))
        ((recursorPayload (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) h.toRecDecl ls
          (recursor (piLimit E₂ ℓ) h.toRecDecl ls) s).app _ (σ ≫ RawCtx.toCtx.map h.recrHom).op
          (RawValuation.pushFin (fun _ => ⊥)
          fun v => (rawInterpret (piLimit E₂ ℓ) Γ (Inductive.recrSubst ps ms mins is maj v)).app _ σ.op ρ)) := by
  have hlabel : (Tm E₂ ℓ).map (σ ≫ RawCtx.toCtx.map h.recrHom).op
      (Tm.label (CtxCat.recr h.toRecDecl ls s).as ((RecTyping.generic h.toRecDecl ls s).typed)) =
      (Tm E₂ ℓ).map σ.op (Tm.label Γ.as h.typed) := by
    rw [op_comp, Functor.map_comp_apply, Tm.map_label]
    simp [Expr.subst, RecTyping.recrHom]
  have hd := h.toRecDecl
  have hβ := RawFamily.ctxLam_openBeta (Γ₁ := CtxCat.nil E₂ ℓ)
    ((E₂.get η).block.recrTele η s ls l) (k := ι.recrEnd s) (by simp) hd.block.recrTele (hsound.recrTeleProperties hB hblock hd ls s)
    (recrTele_headRank_lt η ls s)
    (recursorBody (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) hd ls
      (recursor (piLimit E₂ ℓ) hd ls) s)
    (recursorBody_isFinitary _ _ hd ls (fun Γ e _ => rawInterpret_isFinitary _ Γ e)
      (recursorWith_isFinitary _ _ hd ls fun Γ e _ => rawInterpret_isFinitary _ Γ e) s)
    (hsound.recursorBody_isDirected hB hblock hd ls s hrel
      (hsound.recursor_isDirected hB hblock hd ls hrel))
    (σ ≫ RawCtx.toCtx.map h.recrHom) (fun _ => ⊥)
    (fun v => (rawInterpret (piLimit E₂ ℓ) Γ (Inductive.recrSubst ps ms mins is maj v)).app _ σ.op ρ)
    (hsound.recrHom_admissible hB hblock h pargs fargs σ ρ hρ)
  rw [rawInterpret_recr _ h hrel, RawFamily.closedApps_value, recursor_unfold]
  have htype := (hsound.recrBodyProperties hB hblock h.toRecDecl ls s).subst h.recrHom σ _ ρ
    (SemanticSubstitution.ofHom (CtxCat.recr h.toRecDecl ls s).as.wf h.recrHom σ ρ
      (fun v => (pargs v).subst) hρ)
    (hsound.recrHom_admissible hB hblock h pargs fargs σ ρ hρ)
  simp only [show h.recrHom.subst = Inductive.recrSubst ps ms mins is maj from rfl,
    IndSig.recrBody_subst] at htype
  rw [htype]
  refine Eq.trans (Eq.trans ?_ hβ) ?_
  · congr 1
    · exact congrArg (fun τ => (RawFamily.ctxLam (piLimit E₂ ℓ) _ (CtxCat.nil E₂ ℓ) _ hd.block.recrTele
        (recrTele_headRank_lt η ls s) _).app _ (Quiver.Hom.op τ) fun _ => ⊥) (CtxCat.hom_nil_eq _ _)
    · funext v
      rw [op_comp, Functor.map_comp_apply]
      simp only [CtxCat.nil, Fin.natAdd, Nat.zero_add, Fin.cast_mk]
      exact congrArg ((Tm E₂ ℓ).map σ.op) (Tm.map_varLabel h.recrHom v).symm
  · rw [recursorBody, RawFamily.decode_app_hom_coe, hlabel]

include h pargs fargs in
theorem RawSound.recr_fixed :
    HasFixedness Γ (.recr η s ls l ps ms mins is maj) (Inductive.motiveResult (ms s) is maj) := by
  intro Ξ he σ ρ hρ
  cases hrel : l.rel with
  | false => exact HasFixedness.recr_prop hrel he σ ρ hρ
  | true =>
    have hadm := hsound.recrHom_admissible hB hblock h pargs fargs σ ρ hρ
    have hT : ((rawInterpret (piLimit E₂ ℓ) Γ (Inductive.motiveResult (ms s) is maj)).app _ σ.op ρ).IsDirected := by
      have ht := (hsound.recrBodyProperties hB hblock h.toRecDecl ls s).subst h.recrHom σ _ ρ
        (SemanticSubstitution.ofHom (CtxCat.recr h.toRecDecl ls s).as.wf h.recrHom σ ρ
          (fun v => (pargs v).subst) hρ) hadm
      simp only [show h.recrHom.subst = Inductive.recrSubst ps ms mins is maj from rfl,
        IndSig.recrBody_subst] at ht
      rw [ht]
      exact fun {_} => (hsound.recrBodyProperties hB hblock h.toRecDecl ls s).ideal _ _ hadm
    rw [hsound.recr_value hB hblock h pargs fargs hrel σ ρ hρ]
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
