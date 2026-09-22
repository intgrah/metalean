/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Typing.Structure
public import Metalean.Semantics.Soundness.Recursor.Typing
public import Metalean.Semantics.Soundness.Structure.Case

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Presheaf CodeAssignment IndSig

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
    (hB : InductiveWF E₂ (E₂.get η).block)
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ ps p : (E₂.get η).block.paramType ls ps p)
    (hmaj : E₂[Γ₁.as.ctx] ⊢ maj : .ind η s ls ps hs.indices)
    (f : Fin (ι.ctors s c).nfields) :
    RecTyping Γ₁ η s ls ((((E₂.get η).block.ctors s c).ordinary f).level.inst ls)
      ps (hs.projectionMotives η ls ps f)
      (hs.projectionCases η ls ps f (hs.projectionMotives η ls ps f)) hs.indices maj := by
  have hp := hs.projection_spec hB Γ₁.as.wf hps hmaj f
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
        · simpa using congrArg CtorSection.names (CtorSection.eq_of_projectsFrom sect' (sect.pullback σ₂) hp' (hp.pullback σ₂))
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

theorem RawSound.recr_structural (hsound : RawSound E₂ ℓ pre) (hI : InductiveWF E₁ I)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hs : (E₂.get η).block.IsStructure s c)
    (h : RecTyping Γ₁ η s ls l ps ms mins hs.indices maj) (hrel : l.rel = true)
    (hcarrier : Level.rel ((E₂.get η).block.level.inst ls) = true)
    (pargs : ∀ v, RawInterpretationProperties Γ₁ (Inductive.recrSubst ps ms mins hs.indices maj v))
    (fargs : ∀ v, HasFixedness Γ₁ (Inductive.recrSubst ps ms mins hs.indices maj v)
      ((Ctx.get v ((E₂.get η).block.recrTele η s ls l)).subst (Inductive.recrSubst ps ms mins hs.indices maj)))
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E₂ ℓ) Γ₁ (.recr η s ls l ps ms mins hs.indices maj)).app _ σ.op ρ =
      (piLimit E₂ ℓ).rawExtend
        ((rawInterpret (piLimit E₂ ℓ) Γ₁ (Inductive.motiveResult (ms s) hs.indices maj)).app _ σ.op ρ)
        ((Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as h.typed))
        (rawApps ((rawInterpret (piLimit E₂ ℓ) Γ₁ (mins s c)).app _ σ.op ρ)
          (Fin.append (fun f => (Tm E₂ ℓ).map σ.op (Tm.label Γ₁.as
              (hs.projTerm_hasType h.block f Γ₁.as.wf h.param h.major)))
            hs.no_recursive.elim)
          fun i => RawValue.proj ⟨η, s, c⟩ i ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ.op ρ)) := by
  let hd := h.toRecDecl
  let gen := RecTyping.generic hd ls s
  have hA := hs.indType gen.param
  have hvar : E₂[(CtxCat.recr hd ls s).as.ctx] ⊢ .var (RecrBinder.major (s := s)).resolve :
      .ind η s ls (fun p => .var (RecrBinder.param p).resolve) hs.indices := by
    have hm := gen.major
    rwa [show (fun i => (Expr.var (RecrBinder.index (s := s) i).resolve :
      Expr ζ₂ ℓ (CtxCat.recr hd ls s).as.len)) = hs.indices from funext hs.no_indices.elim] at hm
  let msect : Raw.ContextSection hA (σ ≫ RawCtx.toCtx.map h.recrHom)
      ((Tm E₂ ℓ).map (σ ≫ RawCtx.toCtx.map h.recrHom).op
        (Tm.label (CtxCat.recr hd ls s).as hvar)) :=
    (Raw.ContextSection.ofTerm hA hvar).pullbackId (σ ≫ RawCtx.toCtx.map h.recrHom)
  let sect := CtorSection.ofMajor (h := gen.toRecData) hs msect
  have hp : sect.ProjectsFrom hs _ := ⟨msect, rfl⟩
  rw [hsound.recr_value hI hblock h pargs fargs hrel σ ρ hρ]
  congr 1
  unfold recursorPayload
  rw [RawActionFamily.apply_app, rawRecCaseFamily_value]
  simp only [recoverMajor, hcarrier, ite_true]
  rw [← Tm.label_eq_var hvar rfl, rawRecCase_of_structural hs _ _ _ _ _ _ sect hp]
  congr 1
  · change (RawValuation.pushFin (fun _ => ⊥) fun v =>
      (rawInterpret (piLimit E₂ ℓ) Γ₁ (Inductive.recrSubst ps ms mins hs.indices maj v)).app _ σ.op ρ)
        (Var.db (RecrBinder.case (s := s) s c).resolve) = _
    rw [RawValuation.pushFin_variable, Inductive.recrSubst_case]
  · funext i
    cases i using Fin.addCases with
    | left f =>
      rw [Fin.append_left, sect.proj_name hs hvar hp f, op_comp, Functor.map_comp_apply, Tm.map_label]
      refine congrArg _ (Quotient.sound ⟨?_, ?_⟩) <;> dsimp only [Tm.Repr.ty, Tm.Repr.val]
      · simp only [Inductive.IsStructure.projType_subst, RecTyping.recrHom, Expr.subst,
          Inductive.recrSubst_param, Inductive.recrSubst_major]
        exact IsType.typeEq (hs.projTerm_hasType h.block f Γ₁.as.wf h.param h.major).regular
      · simp only [Inductive.IsStructure.projType_subst, Inductive.IsStructure.projTerm_subst,
          RecTyping.recrHom, Expr.subst, Inductive.recrSubst_param, Inductive.recrSubst_major]
        exact hs.projTerm_hasType h.block f Γ₁.as.wf h.param h.major
    | right f => exact hs.no_recursive.elim f
  · simp [RawFamily.lookup, RawValuation.pushFin]
    rfl

end Metalean.CoherentShape
