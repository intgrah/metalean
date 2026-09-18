/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Recursor.MotiveApplication
public import Metalean.Semantics.Soundness.Function.Application
public import Metalean.Semantics.Soundness.Rules.Inductive
public import Metalean.Semantics.Soundness.Telescope.Transport
import Metalean.Strong.InstLevel
import Metalean.Semantics.Soundness.Rules.Core
import Metalean.Semantics.Soundness.Rules.Function

@[expose] public section

namespace Metalean

open CategoryTheory Presheaf CoherentShape CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)}
  {s : Fin ι.nsorts} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {Γ₁ Γ₂ : CtxCat E₂ ℓ} {ps : Fin ι.nparams → Expr ζ₂ ℓ Γ₁.as.len}
  {is : Fin (ι.nindices s) → Expr ζ₂ ℓ Γ₁.as.len} {maj m : Expr ζ₂ ℓ Γ₁.as.len}

namespace CoherentShape

theorem RawInterpretationProperties.motiveResult (ht' : (E₂.get η).block.WFStrong E₂)
    (h : IndTyping Γ₁ η s ls ps is) (hmaj : E₂[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is)
    (hm : E₂[Γ₁.as.ctx] ⊢ₛ m : (E₂.get η).block.motiveType η ls ps l s)
    (pΔ : RawTeleProperties E₂ Γ₁.as.ctx ((E₂.get η).block.motiveTele η ls ps s))
    (pm : RawInterpretationProperties Γ₁ m) (fm : HasFixedness Γ₁ m ((E₂.get η).block.motiveType η ls ps l s))
    (pis : ∀ i, RawInterpretationProperties Γ₁ (is i))
    (fis : ∀ i, HasFixedness Γ₁ (is i) ((E₂.get η).block.indexType ls s ps is i))
    (pmaj : RawInterpretationProperties Γ₁ maj) :
    RawInterpretationProperties Γ₁ (Inductive.motiveResult m is maj) := by
  let Δ := (E₂.get η).block.indexTele ls s ps
  have hΔ := ht'.indexTele (s := s) h.param
  let T := CtxCat.extendTele Γ₁ Δ hΔ
  let t : Expr ζ₂ ℓ T.as.len := .ind η s ls (fun p => (ps p).wkN (ι.nindices s))
    fun i => .var (Fin.natAdd Γ₁.as.len i)
  let u := (ht'.motiveTele (s := s) Γ₁.as.wf h.param).last.choose
  have ht : E₂[T.as.ctx] ⊢ₛ t : .sort u :=
    (ht'.motiveTele (s := s) Γ₁.as.wf h.param).last.choose_spec.2
  have pt : RawInterpretationProperties T t := pΔ.last T.as.wf
  let t' := Expr.forallE t (.sort l)
  have hcode : E₂[T.as.ctx] ⊢ₛ t' : .sort (.imax u (.succ l)) :=
    .forallEDF ht .sortDF .sortDF
  have pcode : RawInterpretationProperties T t' :=
    .forallE ht .sortDF pt (RawInterpretationProperties.sort (T.extension ht) l)
  let σ₁ := h.indexHom ht'
  have hover : σ₁ ≫ RawCtx.Hom.teleProjection (Γ := Γ₁.as) hΔ = 𝟙 Γ₁.as :=
    RawCtx.Hom.ext (funext fun _ => Fin.append_left _ _ _)
  have hx (i : Fin (ι.nindices s)) : σ₁.subst (Fin.natAdd Γ₁.as.len i) = is i :=
    Fin.append_right _ _ _
  have hps : (fun p => ((ps p).wkN (ι.nindices s)).subst σ₁.subst) = ps :=
    funext fun p => Expr.wkN_subst_id_append (ps p) is
  have htype (i : Fin (ι.nindices s)) :
      (Ctx.get (Fin.natAdd Γ₁.as.len i) (Γ₁.as.ctx ++ Δ)).subst σ₁.subst =
        (E₂.get η).block.indexType ls s ps is i := by
    erw [Inductive.indexTele_get, Inductive.indexType_subst]
    change (E₂.get η).block.indexType ls s
      (fun p => ((ps p).wkN (ι.nindices s)).subst σ₁.subst)
      (fun j => σ₁.subst (Fin.natAdd Γ₁.as.len j)) i = _
    rw [hps, funext hx]
  have pσ₁ (i) : RawInterpretationProperties Γ₁ (σ₁.subst (Fin.natAdd Γ₁.as.len i)) := by
    rw [hx]
    exact pis i
  have fσ₁ (i) : HasFixedness Γ₁ (σ₁.subst (Fin.natAdd Γ₁.as.len i))
      ((Ctx.get (Fin.natAdd Γ₁.as.len i) (Γ₁.as.ctx ++ Δ)).subst σ₁.subst) := by
    rw [hx, htype]
    exact fis i
  have hadm ⦃Γ₂ : CtxCat E₂ ℓ⦄ (σ₂ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₂ ρ) :
      ∃ ρs, SemanticSubstitution σ₁ σ₂ ρs ρ ∧ SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁) ρs :=
    ⟨_, RawTeleProperties.extend_admissible_over Δ hΔ pΔ.init σ₁ hover pσ₁ fσ₁ σ₂ ρ hρ⟩
  have pimages (v) : HasSubstitution Γ₁ (σ₁.subst v) := by
    cases v using Fin.addCases with
    | left v =>
      change HasSubstitution Γ₁ ((Fin.append Subst.id is) (v.castAdd (ι.nindices s)))
      rw [Fin.append_left]
      exact (RawInterpretationProperties.var Γ₁ v).subst
    | right i =>
      rw [hx]
      exact (pis i).subst
  have hb : E₂[T.as.ctx] ⊢ₛ m.applyBound (ι.nindices s) : t' :=
    Ctx.pi_applyBoundStrong T.as.wf hcode hm
  have hbound := applyBound_ideal_fixed hΔ pΔ.init hcode pcode hm pm fm
  have pbound : RawInterpretationProperties T (m.applyBound (ι.nindices s)) :=
    ⟨hbound.1, HasSubstitution.applyBound hΔ pΔ.init hcode pcode hm pm fm⟩
  have hσ₁ : SemanticHom σ₁ := ⟨pimages, hadm⟩
  have papp := hσ₁.props pbound
  have fapp : HasFixedness Γ₁ ((m.applyBound (ι.nindices s)).subst σ₁.subst) (t'.subst σ₁.subst) :=
    hσ₁.fixed hb pcode.subst pbound.subst hbound.2.1
  have he : (m.applyBound (ι.nindices s)).subst σ₁.subst = m.apps is := by
    rw [Expr.applyBound_eq_apps, Expr.subst_apps]
    erw [Expr.wkN_subst_id_append]
    congr 1
    exact funext hx
  have hcarrier : t.subst σ₁.subst = .ind η s ls ps is := by
    change Expr.ind η s ls (fun p => ((ps p).wkN (ι.nindices s)).subst σ₁.subst)
      (fun i => σ₁.subst (Fin.natAdd Γ₁.as.len i)) = _
    rw [hps, funext hx]
  have hcodomain : t'.subst σ₁.subst = .forallE (.ind η s ls ps is) (.sort l) := by
    change Expr.forallE (t.subst σ₁.subst) (.sort l) = _
    rw [hcarrier]
  have hc := ht.substitution σ₁.typed
  rw [hcarrier] at hc
  have hfun := hb.substitution σ₁.typed
  rw [he, hcodomain] at hfun
  have pai : HasIdeality Γ₁ (.ind η s ls ps is) := by
    have hp : HasIdeality Γ₁ (t.subst σ₁.subst) := hσ₁.ideal pt
    rwa [hcarrier] at hp
  rw [he] at papp
  rw [he, hcodomain] at fapp
  exact .app hc .sortDF pai (HasIdeality.sort _ l) hmaj hfun papp pmaj fapp

theorem RawJudgment.motiveResult (hB : (E₂.get η).block.WFStrong E₂)
    (h : IndTyping Γ₁ η s ls ps is) (hmaj : E₂[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps is)
    (hm : E₂[Γ₁.as.ctx] ⊢ₛ m : (E₂.get η).block.motiveType η ls ps l s)
    (pΔ : RawTeleProperties E₂ Γ₁.as.ctx ((E₂.get η).block.motiveTele η ls ps s))
    (pm : RawInterpretationProperties Γ₁ m) (pmf : HasFixedness Γ₁ m ((E₂.get η).block.motiveType η ls ps l s))
    (pis : ∀ i, RawInterpretationProperties Γ₁ (is i))
    (hif : ∀ i, HasFixedness Γ₁ (is i) ((E₂.get η).block.indexType ls s ps is i))
    (pmaj : RawInterpretationProperties Γ₁ maj) (hmajf : HasFixedness Γ₁ maj (.ind η s ls ps is)) :
    RawJudgment Γ₁ (Inductive.motiveResult m is maj) (Inductive.motiveResult m is maj) (.sort l) ∧
      ∀ {Γ₂ : CtxCat E₂ ℓ} (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂), SourceAdmissible σ₁ ρ →
        (rawInterpret (piLimit E₂ ℓ) Γ₁ (Inductive.motiveResult m is maj)).app _ σ₁.op ρ =
          rawApps ((rawInterpret (piLimit E₂ ℓ) Γ₁ m).app _ σ₁.op ρ)
            (Fin.snoc (fun i => (Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as (h.index i)))
              ((Tm E₂ ℓ).map σ₁.op (Tm.label Γ₁.as hmaj)))
            (Fin.snoc (fun i => (rawInterpret (piLimit E₂ ℓ) Γ₁ (is i)).app _ σ₁.op ρ)
              ((rawInterpret (piLimit E₂ ℓ) Γ₁ maj).app _ σ₁.op ρ)) := by
  let Δ := (E₂.get η).block.motiveTele η ls ps s
  have hΔ := hB.motiveTele (s := s) Γ₁.as.wf h.param
  let σ₂ := h.motiveHom hB hmaj
  have hp (i : Fin (ι.nindices s + 1)) :
      RawInterpretationProperties Γ₁ (σ₂.subst (Fin.natAdd Γ₁.as.len i)) := by
    cases i using Fin.lastCases with
    | last =>
      rw [h.motiveHom_major hB hmaj]
      exact pmaj
    | cast i =>
      rw [h.motiveHom_index hB hmaj i]
      exact pis i
  have hf (i : Fin (ι.nindices s + 1)) :
      HasFixedness Γ₁ (σ₂.subst (Fin.natAdd Γ₁.as.len i))
        ((Ctx.get (Fin.natAdd Γ₁.as.len i) (Γ₁.as.ctx ++ Δ)).subst σ₂.subst) := by
    cases i using Fin.lastCases with
    | last =>
      change HasFixedness Γ₁ ((h.motiveHom hB hmaj).subst _)
        ((Ctx.get _ (Γ₁.as.ctx ++ (E₂.get η).block.motiveTele η ls ps s)).subst (h.motiveHom hB hmaj).subst)
      rw [h.motiveHom_major_type hB hmaj, h.motiveHom_major hB hmaj]
      exact hmajf
    | cast i =>
      change HasFixedness Γ₁ ((h.motiveHom hB hmaj).subst _)
        ((Ctx.get _ (Γ₁.as.ctx ++ (E₂.get η).block.motiveTele η ls ps s)).subst (h.motiveHom hB hmaj).subst)
      rw [h.motiveHom_index_type hB hmaj i, h.motiveHom_index hB hmaj i]
      exact hif i
  have he : m.apps (fun i : Fin (ι.nindices s + 1) => σ₂.subst (Fin.natAdd Γ₁.as.len i)) = Inductive.motiveResult m is maj := by
    rw [Expr.apps_last]
    change (m.apps fun i => (h.motiveHom hB hmaj).subst (Fin.natAdd Γ₁.as.len i.castSucc)).app
      ((h.motiveHom hB hmaj).subst (Fin.natAdd Γ₁.as.len (Fin.last _))) = _
    simpa [Inductive.motiveResult] using h.motiveHom_major hB hmaj
  have happ : E₂[Γ₁.as.ctx] ⊢ₛ m.apps (fun i : Fin (ι.nindices s + 1) => σ₂.subst (Fin.natAdd Γ₁.as.len i)) :
      (Expr.sort l).subst σ₂.subst :=
    RawCtx.Hom.applyTele_typed (Γ₁ := Γ₁.as) (k := ι.nindices s + 1) (Δ := Δ) hΔ σ₂ (h.motiveHom_over hB hmaj) .sortDF
      (by
        change E₂[Γ₁.as.ctx] ⊢ₛ m : ((E₂.get η).block.motiveType η ls ps l s).subst Subst.id
        rwa [Expr.subst_id])
  have hresult : E₂[Γ₁.as.ctx] ⊢ₛ Inductive.motiveResult m is maj : .sort l := by
    simpa [he] using happ
  have pinterp := RawInterpretationProperties.motiveResult hB h hmaj hm pΔ pm pmf pis hif pmaj
  have hcompute {Γ₂ : CtxCat E₂ ℓ} (σ₁ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ₁ ρ) :=
    rawInterpret_applyTele (k := ι.nindices s + 1) Δ hΔ pΔ (.sort l) .sortDF (HasIdeality.sort _ l) m hm
      pm.ideal pmf σ₂ (h.motiveHom_over hB hmaj) hp hf happ σ₁ ρ hρ
  have hfixed : HasFixedness Γ₁ (Inductive.motiveResult m is maj) (.sort l) := by
    intro Γ₂ ht σ₁ ρ hρ
    have hfix := (hcompute σ₁ ρ hρ).2.2
    have hlabel : Tm.label Γ₁.as happ = Tm.label Γ₁.as ht := by
      apply Tm.label_eq
      · exact IsTypeStrong.isTypeEq ht.regular
      · rwa [he]
    rw [hlabel, he, rawInterpret_sort] at hfix
    rwa [rawInterpret_sort]
  refine ⟨{
    syntactic := hresult
    type := RawInterpretationProperties.sort Γ₁ l
    left := pinterp
    right := pinterp
    equal := HasEquality.refl Γ₁ _
    fixed := hfixed }, ?_⟩
  intro Γ₂ σ₁ ρ hρ
  have hv := (hcompute σ₁ ρ hρ).1
  rw [he] at hv
  rw [hv]
  congr 1
  · funext i
    cases i using Fin.lastCases with
    | last =>
      simpa using congrArg ((Tm E₂ ℓ).map σ₁.op) (h.motiveHom_major_label hB hmaj)
    | cast i =>
      simpa only [Fin.snoc_castSucc] using congrArg ((Tm E₂ ℓ).map σ₁.op) (h.motiveHom_index_label hB hmaj i)
  · funext i
    cases i using Fin.lastCases with
    | last =>
      simpa using congrArg (fun e => (rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ₁.op ρ)
        (h.motiveHom_major hB hmaj)
    | cast i =>
      simpa only [Fin.snoc_castSucc] using congrArg (fun e => (rawInterpret (piLimit E₂ ℓ) Γ₁ e).app _ σ₁.op ρ)
        (h.motiveHom_index hB hmaj i)

end CoherentShape

theorem RawSound.indexTeleProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hI : (E₂.get η).block.WFStrong E₂)
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ₁ (ps p))
    (fps : ∀ p, HasFixedness Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (s : Fin ι.nsorts) :
    RawTeleProperties E₂ Γ₁.as.ctx ((E₂.get η).block.indexTele ls s ps) := by
  let Src : CtxCat E₂ ℓ := ⟨Ctx.instL ls (E₂.get η).block.params, hI.paramClosedWF ls⟩
  have pctx : RawTeleProperties E₂ .nil Src.as.ctx := by
    simpa using hsound.paramTeleProperties hB hblock ls
  have hindices := (hI.indices s).instLevel (Q := fun _ => True) ls fun _ => trivial
  have pindices : RawTeleProperties E₂ Src.as.ctx (Ctx.instL ls ((E₂.get η).block.indices s)) := by
    have hctx := hB.paramClosedWF ls
    have hp := hsound.teleProperties hctx
      ((hB.indices s).instLevel (Q := fun _ => True) ls fun _ => trivial)
    exact ((congrArg₂ (RawTeleProperties E₂)
      (Ctx.map_instL pre.sigs ls I.params)
      (Ctx.map_instL pre.sigs ls (I.indices s))).trans
        (congrArg (fun I => RawTeleProperties E₂ (Ctx.instL ls (Inductive.params I))
          (Ctx.instL ls (I.indices s))) hblock.symm)).mp hp
  let σ : Γ₁.as ⟶ Src.as := ⟨ps, (Inductive.paramSubstEqStrong hps).left⟩
  have pf (v : Fin ι.nparams) :
      HasFixedness Γ₁ (σ.subst v) ((Src.as.ctx.get v).subst σ.subst) := by
    rw [← Ctx.get_instL, Inductive.paramType_eq_get_subst]
    exact fps v
  exact pctx.substitution (Ctx.instL ls ((E₂.get η).block.indices s)) hindices pindices σ pps pf

theorem RawSound.motiveTeleProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (hI : (E₂.get η).block.WFStrong E₂)
    (hps : ∀ p, E₂[Γ₁.as.ctx] ⊢ₛ ps p : (E₂.get η).block.paramType ls ps p)
    (pps : ∀ p, RawInterpretationProperties Γ₁ (ps p))
    (fps : ∀ p, HasFixedness Γ₁ (ps p) ((E₂.get η).block.paramType ls ps p))
    (s : Fin ι.nsorts) :
    RawTeleProperties E₂ Γ₁.as.ctx ((E₂.get η).block.motiveTele η ls ps s) := by
  have hΔ := hI.indexTele (s := s) hps
  let T := CtxCat.extendTele Γ₁ ((E₂.get η).block.indexTele ls s ps) hΔ
  have ht : IndTyping T η s ls (fun p => (ps p).wkN (ι.nindices s))
      fun i => .var (Fin.natAdd Γ₁.as.len i) :=
    IndTyping.ofTyping hI
      (hI.motiveTele (s := s) Γ₁.as.wf hps).last.choose_spec.2
  have pfn (c : Fin (ι.nctors s)) := hsound.blockCtorTypeFnProperties η hB hblock s c ls
  refine .snoc (hsound.indexTeleProperties hB hblock hI hps pps fps s) ?_
  intro wf
  exact {
    ideal := HasIdeality.ind ht hI (fun c => (pfn c).ideal) fun p =>
      ((pps p).wkN _ hΔ).ideal
    subst := HasSubstitution.ind ht hI fun p =>
      ((pps p).wkN _ hΔ).subst }

end Metalean
