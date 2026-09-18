/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Strong.Structure
public import Metalean.Semantics.Soundness.Recursor.Typing
public import Metalean.Semantics.Soundness.Structure.Case

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment IndSig TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {Γ₁ Γ₂ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
  {ms : Fin ι.nsorts → Expr ζ₂ ℓ Γ₁.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ ℓ Γ₁.as.len}
  {maj : Expr ζ₂ ℓ Γ₁.as.len} {h : RecData Γ₁ η ls l ps ms mins}

theorem rawApps_append_no_recursive {k : Nat}
    (hs : (E₂.get η).block.IsStructure s c) (F : RawValue Γ₁)
    (ns : Fin k → Tm_ Γ₁) (args : Fin k → RawValue Γ₁)
    (ns' : Fin (ι.ctors s c).nrecFields → Tm_ Γ₁)
    (args' : Fin (ι.ctors s c).nrecFields → RawValue Γ₁) :
    rawApps F (Fin.append ns ns') (Fin.append args args') = rawApps F ns args := by
  revert ns' args'
  rw [Fin.eq_zero_of_isEmpty hs.no_recursive]
  intro ns' args'
  rw [rawApps_append, rawApps_zero]

theorem RecTyping.structure_projection (hs : (E₂.get η).block.IsStructure s c)
    (hB : (E₂.get η).block.WFStrong E₂)
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (hmaj : E₂[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps hs.indices)
    (f : Fin (ι.ctors s c).nfields) :
    RecTyping Γ₁ η s ls ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls)
      ps (hs.projectionMotives η ls ps f)
      (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f)) hs.indices maj := by
  have hp := hs.projectionStrong hB Γ₁.as.wf hps hmaj f
  exact {
    block := hB
    allowed := hs.recAllowed _
    param := hps
    motive := hp.motive
    case := fun other ctor => by
      obtain rfl := hs.sort_unique other
      obtain rfl := hs.ctor_unique ctor
      exact hp.case
    index := hs.no_indices.elim
    major := hmaj }

theorem rawRecCase_of_structural (hs : (E₂.get η).block.IsStructure s c)
    (minValue : (d : Fin (ι.nctors s)) → RawFamily Γ₁)
    (ih : (d : Fin (ι.nctors s)) → Fin (ι.ctors s d).nrecFields → RawFamily Γ₁)
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (majorName : Tm_ Γ₂) (X : RawValue Γ₂)
    (sect : CtorSection h s c σ₁) (hp : sect.ProjectsFrom hs majorName) :
    rawRecCase h minValue ih σ₁ ρ majorName X =
      rawApps ((minValue c).app _ σ₁.op ρ) sect.names fun i => RawValue.proj ⟨η, s, c⟩ i X := by
  ext Γ₃ σ₂ y
  constructor
  · rintro (hy | ⟨d, sect', fields, hobs, hy⟩)
    · exact ΩLower.lower _ σ₂ hy (ΩLower.bottom _ σ₂)
    · have hd : d = c := hs.ctor_unique d
      subst d
      have hfields : ∀ i, (RawValue.proj ⟨η, s, c⟩ i X).mem σ₂ (fields i) := by
        rcases hobs with ⟨hns, _⟩ | ⟨_, _, hf⟩
        · exact (hns hs).elim
        · exact hf
      have hn : sect'.names = fun i => (Tm E₂ ℓ).map σ₂.op (sect.names i) := by
        rcases hobs with ⟨hns, _⟩ | ⟨_, hp', _⟩
        · exact (hns hs).elim
        · simpa using CtorSection.names_eq_of_projectsFrom sect' (sect.pullback σ₂) hp' (hp.pullback σ₂)
      rw [caseArgs, rawApps_append_no_recursive hs, hn] at hy
      rw [← ΩLower.presheaf_map_mem_id, pullback_rawApps, RawFamily.app_pullback]
      exact rawApps_mono (fun _ _ h => h) _ (fun i =>
        ΩLower.principal_le_iff.mpr ((ΩLower.presheaf_map_mem_id _ σ₂ _).mpr (hfields i)))
        (𝟙 Γ₃) y hy
  · intro hy
    have ⟨fields, hf, hy⟩ := exists_shapes_of_mem_rawApps ((minValue c).app _ σ₁.op ρ) σ₂ sect.names
      (fun i => RawValue.proj ⟨η, s, c⟩ i X) y hy
    rw [RawFamily.app_pullback] at hy
    refine Or.inr ⟨c, sect.pullback σ₂, fields, Or.inr ⟨hs, hp.pullback σ₂, hf⟩, ?_⟩
    rw [caseArgs, rawApps_append_no_recursive hs]
    simpa using hy

theorem RawSound.recr_structural (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hs : (E₂.get η).block.IsStructure s c)
    (h : RecTyping Γ₁ η s ls l ps ms mins hs.indices maj) (hrel : l.rel = true)
    (hcarrier : Level.rel ((E₂.get η).block.level.inst ls) = true)
    (pargs : ∀ v, RawInterpretationProperties Γ₁ (Inductive.recrSubst ps ms mins hs.indices maj v))
    (fargs : ∀ v, HasFixedness Γ₁ (Inductive.recrSubst ps ms mins hs.indices maj v)
      ((Ctx.get v ((E₂.get η).block.recrTele η s ls l)).subst (Inductive.recrSubst ps ms mins hs.indices maj)))
    (hr : E₂[Γ₁.as.ctx] ⊢ₛ .recr η s ls l ps ms mins hs.indices maj :
      Inductive.motiveResult (ms s) hs.indices maj)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ₁ (.recr η s ls l ps ms mins hs.indices maj)).app _ σ.op ρ =
      (piLimit E₂ ℓ).rawExtend
        ((rawInterpret (piLimit E₂ ℓ) Γ₁ (Inductive.motiveResult (ms s) hs.indices maj)).app _ σ.op ρ)
        ((Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as hr))
        (rawApps ((rawInterpret (piLimit E₂ ℓ) Γ₁ (mins s c)).app _ σ.op ρ)
          (Fin.append (fun f => (Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as
              (hs.projTerm_hasTypeStrong h.block f Γ₁.as.wf h.param h.major)))
            hs.no_recursive.elim)
          fun i => RawValue.proj ⟨η, s, c⟩ i ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ.op ρ)) := by
  let hd := h.toRecDecl
  let gen := RecTyping.generic hd ls s
  have hA := gen.toIndData.indTyped s c hs
  have hvar : E₂[(CtxCat.recr hd ls s).as.ctx] ⊢ₛ .var (RecrBinder.major (s := s)).resolve :
      .ind η s ls (fun p => .var (RecrBinder.param p).resolve) hs.indices := by
    have hm := gen.major
    rwa [show (fun i => (Expr.var (RecrBinder.index (s := s) i).resolve :
      Expr ζ₂ ℓ (CtxCat.recr hd ls s).as.len)) = hs.indices from funext hs.no_indices.elim] at hm
  let msect : Raw.ContextSection hA (σ ≫ RawCtx.toCtx.map h.recrHom)
      ((Tm E₂ ℓ).map (σ ≫ RawCtx.toCtx.map h.recrHom).op
        (Tm.label (CtxCat.recr hd ls s).as hvar)) :=
    (Raw.ContextSection.ofTerm hA hvar).pullbackId (σ ≫ RawCtx.toCtx.map h.recrHom)
  let sect := CtorSection.ofMajor (h := gen.toRecData) hs msect
  have hp := CtorSection.ofMajor_projectsFrom (h := gen.toRecData) hs msect
  have hpayload : (recursorPayload (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) hd ls
      (recursor (piLimit E₂ ℓ) hd ls) s).app _ (σ ≫ RawCtx.toCtx.map h.recrHom).op
        (RawValuation.pushFin (fun _ => ⊥) fun v =>
          (rawInterpret (piLimit E₂ ℓ) Γ₁ (Inductive.recrSubst ps ms mins hs.indices maj v)).app _ σ.op ρ) =
      rawApps ((rawInterpret (piLimit E₂ ℓ) Γ₁ (mins s c)).app _ σ.op ρ)
        (Fin.append (fun f => (Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as
            (hs.projTerm_hasTypeStrong h.block f Γ₁.as.wf h.param h.major))) hs.no_recursive.elim)
        fun i => RawValue.proj ⟨η, s, c⟩ i ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ.op ρ) := by
    unfold recursorPayload
    rw [RawActionFamily.apply_app, rawRecCaseFamily_value]
    have hX : (recoverMajor gen.toRecData s (𝟙 (CtxCat.recr hd ls s))
        (fun i => Tm.varLabel (CtxCat.recr hd ls s) (RecrBinder.index i).resolve)
        (fun i => RawFamily.lookup (Var.db (RecrBinder.index i).resolve))
        (RawFamily.lookup (Var.db (RecrBinder.major (s := s)).resolve))).app _
          (σ ≫ RawCtx.toCtx.map h.recrHom).op
          (RawValuation.pushFin (fun _ => ⊥) fun v =>
            (rawInterpret (piLimit E₂ ℓ) Γ₁ (Inductive.recrSubst ps ms mins hs.indices maj v)).app _ σ.op ρ) =
        (rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ.op ρ := by
      simp only [recoverMajor, hcarrier, ↓reduceIte]
      change (RawValuation.pushFin (fun _ => ⊥) fun v =>
        (rawInterpret (piLimit E₂ ℓ) Γ₁ (Inductive.recrSubst ps ms mins hs.indices maj v)).app _ σ.op ρ)
          (Var.db (RecrBinder.major (s := s)).resolve) = _
      rw [RawValuation.pushFin_variable, Inductive.recrSubst_resolve_major]
    rw [hX, ← Tm.label_eq_var hvar rfl, rawRecCase_of_structural hs _ _ _ _ _ _ sect hp]
    congr 1
    · change (RawValuation.pushFin (fun _ => ⊥) fun v =>
        (rawInterpret (piLimit E₂ ℓ) Γ₁ (Inductive.recrSubst ps ms mins hs.indices maj v)).app _ σ.op ρ)
          (Var.db (RecrBinder.case (s := s) s c).resolve) = _
      rw [RawValuation.pushFin_variable, Inductive.recrSubst_resolve_case]
    · funext i
      cases i using Fin.addCases with
      | left f =>
        rw [Fin.append_left, sect.proj_name hs hvar hp f, op_comp, Functor.map_comp_apply, Tm.map_label]
        refine congrArg _ (Tm.label_eq_iff.mpr ⟨?_, ?_⟩)
        · simp only [Inductive.IsStructure.projType_subst, RecTyping.recrHom, Expr.subst,
            Inductive.recrSubst_resolve_param, Inductive.recrSubst_resolve_major]
          exact IsTypeStrong.isTypeEq
            (hs.projTerm_hasTypeStrong h.block f Γ₁.as.wf h.param h.major).regular
        · simp only [Inductive.IsStructure.projType_subst, Inductive.IsStructure.projTerm_subst,
            RecTyping.recrHom, Expr.subst, Inductive.recrSubst_resolve_param, Inductive.recrSubst_resolve_major]
          exact hs.projTerm_hasTypeStrong h.block f Γ₁.as.wf h.param h.major
      | right f => exact hs.no_recursive.elim f
  rw [hsound.recr_value hI hblock h pargs fargs hrel hr σ ρ hρ, hpayload]

theorem rawInterpret_structure_projection_beta (hsound : RawSound E₂ ℓ pre) (hI : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hs : (E₂.get η).block.IsStructure s c)
    (hB : (E₂.get η).block.WFStrong E₂)
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (pmaj : RawJudgment Γ₁ maj maj (.ind η s ls ps hs.indices))
    (f : Fin (ι.ctors s c).nfields)
    (hrel : Level.rel ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls) = true)
    (pargs : ∀ v, RawInterpretationProperties Γ₁ (Inductive.recrSubst ps (hs.projectionMotives η ls ps f)
      (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f)) hs.indices maj v))
    (fargs : ∀ v, HasFixedness Γ₁ (Inductive.recrSubst ps (hs.projectionMotives η ls ps f)
        (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f)) hs.indices maj v)
      ((Ctx.get v ((E₂.get η).block.recrTele η s ls ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls))).subst
        (Inductive.recrSubst ps (hs.projectionMotives η ls ps f)
          (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f)) hs.indices maj)))
    (pbodyI : HasIdeality (CtxCat.extension Γ₁ (hs.indTypeStrong hps))
      (hs.projType η ls (fun p => (ps p).wk) f (.var (Fin.last Γ₁.as.len))))
    (pbodyS : HasSubstitution (CtxCat.extension Γ₁ (hs.indTypeStrong hps))
      (hs.projType η ls (fun p => (ps p).wk) f (.var (Fin.last Γ₁.as.len))))
    (hΔ : WFTeleStrong E₂ (fun _ => True) Γ₁.as.ctx
      (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps))
    (pfields : RawTeleProperties E₂ Γ₁.as.ctx
      (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps))
    (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ)
    (σ₂ : Γ₂ ⟶ CtxCat.extendTele Γ₁
      (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) hΔ)
    (hσ₂ : σ₂ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection (Γ := Γ₁.as) hΔ) = σ₁)
    (hnames : ∀ i, (Tm E₂ ℓ).map σ₂.op
      (Tm.varLabel (CtxCat.extendTele Γ₁
        (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) hΔ) (Fin.natAdd Γ₁.as.len i)) =
      (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as
        (hs.projTerm_hasTypeStrong hB i Γ₁.as.wf hps pmaj.syntactic.left)))
    (hfields : SourceAdmissible σ₂ (ρ.pushFin fun i =>
      (projIdeal ⟨η, s, c⟩ (Fin.castAdd _ i) (hρ.eval pmaj.left.ideal)).val)) :
    (rawInterpret (piLimit E₂ ℓ) Γ₁ (hs.projTerm η ls ps f maj)).app _ σ₁.op ρ =
      (piLimit E₂ ℓ).rawExtend
        ((rawInterpret (piLimit E₂ ℓ) Γ₁ (hs.projType η ls ps f maj)).app _ σ₁.op ρ)
        ((Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as
          (hs.projTerm_hasTypeStrong hB f Γ₁.as.wf hps pmaj.syntactic.left)))
        (RawValue.proj ⟨η, s, c⟩ (Fin.castAdd _ f)
          ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ₁.op ρ)) := by
  let h := RecTyping.structure_projection hs hB hps pmaj.syntactic.left f
  have hpr := hs.projectionStrong hB Γ₁.as.wf hps pmaj.syntactic.left f
  have hr : E₂[Γ₁.as.ctx] ⊢ₛ hs.projTerm η ls ps f maj :
      Inductive.motiveResult (hs.projectionMotives η ls ps f s) hs.indices maj :=
    DefeqStrong.defeqDF hpr.result.symm hpr.term
  rw [hs.projTerm_eq_recr] at hr
  have hn : Tm.label Γ₁.as hr = Tm.label Γ₁.as hpr.term := by
    refine Tm.label_eq_iff.mpr ⟨.ofDefEq hpr.result, ?_⟩
    simpa only [hs.projTerm_eq_recr] using hr
  let args : Fin (ι.ctors s c).nfields → Domain Γ₂ := fun i => projIdeal ⟨η, s, c⟩ (Fin.castAdd _ i) (hρ.eval pmaj.left.ideal)
  let ns : Fin (ι.ctors s c).nfields → Tm_ Γ₂ := fun i => (Tm E₂ ℓ).map σ₂.op
    (Tm.varLabel (CtxCat.extendTele Γ₁
      (((E₂.get η).block.ctors s c).ordinaryFieldTele η ls ps) hΔ) (Fin.natAdd Γ₁.as.len i))
  have hns : (fun i => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as
      (hs.projTerm_hasTypeStrong h.block i Γ₁.as.wf h.param h.major))) = ns :=
    funext fun i => (hnames i).symm
  have hargs : (fun i => RawValue.proj (CtorHead.mk η s c) i
      ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ₁.op ρ)) =
      Fin.append (fun i => (args i).val) hs.no_recursive.elim := by
    funext i
    cases i using Fin.addCases with
    | left i =>
      change Fin (ι.ctors s c).nfields at i
      rw [Fin.append_left]
      rfl
    | right i => exact hs.no_recursive.elim i
  have hb := rawInterpret_structure_case_beta (ms := hs.projectionMotives η ls ps f)
    hs hΔ pfields σ₂ ρ args hfields f
  rw [hσ₂] at hb
  have he := RawSound.recr_structural hsound hI hblock hs h hrel (structure_carrier_relevant hs f hrel) pargs fargs hr
    σ₁ ρ hρ
  rw [HasEquality.structure_projection_motive_beta hs hps pmaj f pbodyI pbodyS σ₁ ρ hρ, hn, hns,
    hargs, rawApps_append_no_recursive hs, hb] at he
  simp only [hs.projTerm_eq_recr] at he ⊢
  exact he

end Metalean.CoherentShape
