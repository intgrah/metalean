/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Soundness.Judgment
import Metalean.Semantics.Interpretation.Binder.Ideality
import Metalean.Semantics.Interpretation
import Metalean.Semantics.Interpretation.Telescope
import Metalean.TypeTheory.Syntactic.Substitution

@[expose] public section

namespace Metalean

open CategoryTheory CoherentShape CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ n : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)} {Γ₁ Γ₂ : CtxCat E₂ ℓ}

namespace CoherentShape

namespace RawTeleProperties

theorem admissible_of_images {ctx : Ctx ζ₂ ℓ 0 n}
    (hctx : E₂[ctx] ⊢ₛ ok) (hprops : RawTeleProperties E₂ .nil ctx)
    (σ₁ : Γ₁.as ⟶ (⟨ctx, hctx⟩ : CtxCat E₂ ℓ).as) (σ₂ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (htarget : SourceAdmissible σ₂ ρ)
    (hi : ∀ v, HasIdeality Γ₁ (σ₁.subst v))
    (hr : ∀ v, HasSubstitution Γ₁ (σ₁.subst v))
    (hf : ∀ v, HasFixedness Γ₁ (σ₁.subst v) ((ctx.get v).subst σ₁.subst)) :
    SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁)
      (RawValuation.pushFin (fun _ => ⊥)
        fun v => (rawInterpret (piLimit E₂ ℓ) Γ₁ (σ₁.subst v)).app _ σ₂.op ρ) := by
  induction hctx with
  | nil => exact .nil _ _
  | @snoc n ctx t hctx ht ih =>
    have ⟨u, ht⟩ := ht
    let σ₃ : Γ₁.as ⟶ (⟨ctx, hctx⟩ : CtxCat E₂ ℓ).as :=
      σ₁ ≫ CtxCat.projectionRaw ⟨ctx, hctx⟩ ht
    have hfixed (v : Var n) :
        HasFixedness Γ₁ (σ₃.subst v) ((Ctx.get v ctx).subst σ₃.subst) := by
      have q : HasFixedness Γ₁ (σ₁.subst v.castSucc)
          ((Ctx.get v.castSucc (ctx.snoc t)).subst σ₁.subst) := hf v.castSucc
      rwa [Ctx.get_snoc ctx t v.castSucc (Nat.ne_of_lt v.isLt), Expr.wk_subst] at q
    have he : E₂[Γ₁.as.ctx] ⊢ₛ σ₁.subst (Fin.last n) : t.subst σ₃.subst := by
      have q := σ₁.typed (Fin.last n)
      rwa [Ctx.get_last, Expr.wk_subst] at q
    have hfa : HasFixedness Γ₁ (σ₁.subst (Fin.last n)) (t.subst σ₃.subst) := by
      have q : HasFixedness Γ₁ (σ₁.subst (Fin.last n))
          ((Ctx.get (Fin.last n) (ctx.snoc t)).subst σ₁.subst) := hf (Fin.last n)
      rwa [Ctx.get_last, Expr.wk_subst] at q
    have heq : σ₃.snoc ⟨u, ht⟩ he = σ₁ :=
      RawCtx.Hom.ext (Fin.snoc_init_self σ₁.subst)
    have htail := ih hprops.init σ₃ (fun v => hi v.castSucc) (fun v => hr v.castSucc) hfixed
    have pt : RawInterpretationProperties (⟨ctx, hctx⟩ : CtxCat E₂ ℓ) t := hprops.entry (by simp) hctx
    have hsub := SemanticSubstitution.ofHom hctx σ₃ σ₂ ρ (fun v => hr v.castSucc) htarget
    have htype := pt.subst σ₃ σ₂ _ ρ hsub htail
    have hfixed := hfa he σ₂ ρ htarget
    rw [htype] at hfixed
    have hresult := htail.push ht ((Raw.ContextSection.ofTyping ht σ₃ he).pullback σ₂)
      (pt.ideal _ _ htail) (hi (Fin.last n) _ _ htarget) hfixed
    change SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map (σ₃.snoc ⟨u, ht⟩ he)) _ at hresult
    rwa [heq] at hresult

theorem admissible {ctx : Ctx ζ₂ ℓ 0 n} (hctx : E₂[ctx] ⊢ₛ ok)
    (hprops : RawTeleProperties E₂ .nil ctx)
    (σ₁ : Γ₁.as ⟶ (⟨ctx, hctx⟩ : CtxCat E₂ ℓ).as) (σ₂ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (htarget : SourceAdmissible σ₂ ρ)
    (hargs : ∀ v, RawJudgment Γ₁ (σ₁.subst v) (σ₁.subst v) ((ctx.get v).subst σ₁.subst)) :
    SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁)
      (RawValuation.pushFin (fun _ => ⊥)
        fun v => (rawInterpret (piLimit E₂ ℓ) Γ₁ (σ₁.subst v)).app _ σ₂.op ρ) :=
  hprops.admissible_of_images hctx σ₁ σ₂ ρ htarget (fun v => (hargs v).left.ideal)
    (fun v => (hargs v).left.subst) fun v => (hargs v).fixed

end RawTeleProperties

theorem RawFamily.bodyAction_isIdealValued {t : Expr ζ₂ ℓ Γ₁.as.len}
    {u : Level ℓ} (ht : E₂[Γ₁.as.ctx] ⊢ₛ t : .sort u) (pt : HasIdeality Γ₁ t)
    {B : RawFamily (Γ₁.extension ht)}
    (hB : ∀ ⦃Γ₃ : CtxCat E₂ ℓ⦄ (σ : Γ₃ ⟶ Γ₁.extension ht) (ρ : RawValuation Γ₃),
      SourceAdmissible σ ρ → (B.app _ σ.op ρ).IsDirected)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    (RawFamily.normalizedBodyAction (piLimit E₂ ℓ) (CtxCat.rawComprehension ht)
      (rawInterpret (piLimit E₂ ℓ) Γ₁ t) B σ ρ).IsIdealValued :=
  RawFamily.normalizedBodyAction_isIdealValued (CtxCat.rawComprehension ht) _ _ σ ρ (pt σ ρ hρ)
    fun σ₂ _ s J hJ =>
      hB s.hom _ ((hρ.pullback σ₂).push ht s (pt _ _ (hρ.pullback σ₂)) J.property hJ)

theorem RawFamily.abstraction_isDirected_of {t : Expr ζ₂ ℓ Γ₁.as.len}
    {u : Level ℓ} (ht : E₂[Γ₁.as.ctx] ⊢ₛ t : .sort u) (pt : HasIdeality Γ₁ t)
    {B : RawFamily (Γ₁.extension ht)}
    (hB : ∀ ⦃Γ₃ : CtxCat E₂ ℓ⦄ (σ : Γ₃ ⟶ Γ₁.extension ht) (ρ : RawValuation Γ₃),
      SourceAdmissible σ ρ → (B.app _ σ.op ρ).IsDirected)
    ⦃Γ₂ : CtxCat E₂ ℓ⦄ (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    ((RawFamily.abstraction (piLimit E₂ ℓ) (CtxCat.rawComprehension ht)
      (rawInterpret (piLimit E₂ ℓ) Γ₁ t) B).app _ σ.op ρ).IsDirected := by
  rw [RawFamily.abstraction_value]
  exact RawAction.abstraction_isDirected _ (RawFamily.bodyAction_isIdealValued ht pt hB σ ρ hρ)

theorem RawFamily.ctxLam_isDirected {b m : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ₂ ℓ Γ₁.as.len m) (hΔ : WFTeleStrong E₂ P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E₂ Γ₁.as.ctx Δ) (hb : Δ.headRank < b)
    {B : RawFamily (CtxCat.extendTele Γ₁ Δ hΔ)}
    (hB : ∀ ⦃Γ₂ : CtxCat E₂ ℓ⦄ (σ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ : RawValuation Γ₂),
      SourceAdmissible σ ρ → (B.app _ σ.op ρ).IsDirected)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) (hρ : SourceAdmissible σ ρ) :
    ((RawFamily.ctxLam (piLimit E₂ ℓ) (fun Γ e _ => rawInterpret (piLimit E₂ ℓ) Γ e) Γ₁ Δ hΔ hb
      B).app _ σ.op ρ).IsDirected := by
  induction Δ with
  | nil => exact hB σ ρ hρ
  | snoc Δ t ih =>
    exact ih hΔ.init pΔ.init _
      (RawFamily.abstraction_isDirected_of hΔ.last.choose_spec.2
        (pΔ.last (hΔ.init.appendCtxWFStrong Γ₁.as.wf)).ideal hB)

theorem Tm.map_teleSnoc_varLabel {k : Nat} {P : Level ℓ → Prop}
    {Δ : Ctx ζ₂ ℓ Γ₁.as.len (Γ₁.as.len + k)} {t : Expr ζ₂ ℓ (Γ₁.as.len + k)}
    (hΔ : WFTeleStrong E₂ P Γ₁.as.ctx (Δ.snoc t))
    (ht : E₂[(CtxCat.extendTele Γ₁ Δ hΔ.init).as.ctx] ⊢ₛ t : .sort hΔ.last.choose)
    (σ₁ : Γ₂ ⟶ CtxCat.extendTele Γ₁ (Δ.snoc t) hΔ) :
    (fun i : Fin k => (Tm E₂ ℓ).map σ₁.op
        (Tm.varLabel (CtxCat.extendTele Γ₁ (Δ.snoc t) hΔ) (Fin.natAdd Γ₁.as.len i.castSucc))) =
      fun i : Fin k => (Tm E₂ ℓ).map (σ₁ ≫ CtxCat.rawProjection _ ht).op
        (Tm.varLabel (CtxCat.extendTele Γ₁ Δ hΔ.init) (Fin.natAdd Γ₁.as.len i)) :=
  funext fun i => Tm.map_extension_varLabel ht σ₁ (Fin.natAdd Γ₁.as.len i)

theorem Tm.map_teleSnoc_last_varLabel {k : Nat} {P : Level ℓ → Prop}
    {Δ : Ctx ζ₂ ℓ Γ₁.as.len (Γ₁.as.len + k)} {t : Expr ζ₂ ℓ (Γ₁.as.len + k)}
    (hΔ : WFTeleStrong E₂ P Γ₁.as.ctx (Δ.snoc t))
    (ht : E₂[(CtxCat.extendTele Γ₁ Δ hΔ.init).as.ctx] ⊢ₛ t : .sort hΔ.last.choose)
    (σ₁ : Γ₂ ⟶ CtxCat.extendTele Γ₁ (Δ.snoc t) hΔ) :
    (Tm E₂ ℓ).map σ₁.op
        (Tm.varLabel (CtxCat.extendTele Γ₁ (Δ.snoc t) hΔ) (Fin.natAdd Γ₁.as.len (Fin.last k))) =
      (Tm E₂ ℓ).map σ₁.op (CtxCat.rawComprehension ht).generic := by
  rw [CtxCat.rawComprehension_generic ht]
  rfl

end CoherentShape

theorem RawSound.teleProperties (hsound : RawSound E₂ ℓ pre) {Δ : Ctx ζ₁ ℓ 0 n} (hΔ : E₁[Δ] ⊢ₛ ok)
    {P : Level ℓ → Prop} {m : Nat} {Θ : Ctx ζ₁ ℓ n m}
    (hΘ : WFTeleStrong E₁ P Δ Θ) :
    RawTeleProperties E₂ (Δ.map pre.sigs) (Θ.map pre.sigs) := by
  induction hΘ with
  | nil => exact .nil
  | @snoc m Θ t hΘ ht ih =>
    have ⟨u, _, ht⟩ := ht
    have hok : E₁[Δ ++ Θ] ⊢ₛ ok := WFTeleStrong.appendCtxWFStrong hΘ hΔ
    exact .snoc ih fun wf =>
      (hsound.properties hok (Ctx.map_append pre.sigs Δ Θ) wf ht).left

theorem RawSound.paramTeleProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (hblock : (E₂.get η).block = I.map pre.sigs) (ls : Fin ι.nlevels → Level ℓ) :
    RawTeleProperties E₂ .nil (Ctx.instL ls (E₂.get η).block.params) := by
  have hp := hsound.teleProperties (.nil : E₁[(#t[] : Ctx ζ₁ ℓ 0 0)] ⊢ₛ ok)
    (hB.params.instLevel (Q := fun _ => True) ls fun _ => trivial)
  rw [hblock]
  exact congr(RawTeleProperties E₂ _ $(Ctx.map_instL pre.sigs ls I.params)).mp hp

theorem RawSound.ordinaryTeleProperties (hsound : RawSound E₂ ℓ pre) (hB : I.WFStrong E₁)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ) :
    RawTeleProperties E₂ (Ctx.instL ls (I.map pre.sigs).params)
      (Ctx.instL ls ((I.map pre.sigs).ctors s c).ordinaryTele) := by
  have hΔ := hB.paramClosedWF ls
  have hordinary : WFTeleStrong E₁ (fun _ => True) I.params (I.ctors s c).ordinaryTele := by
    simpa [Ctor.ordinaryTele] using
      (hB.ctors s c).ordinaryTeleAuxStrong (ι.ctors s c).nfields le_rfl
  have hΘ := hordinary.instLevel (Q := fun _ => True) ls fun _ => trivial
  exact congr(RawTeleProperties E₂ $(Ctx.map_instL pre.sigs ls I.params)
    $((Ctx.map_instL pre.sigs ls (I.ctors s c).ordinaryTele).trans
      (congrArg (Ctx.instL ls) (Ctor.ordinaryTele_map pre.sigs (I.ctors s c))))).mp
    (hsound.teleProperties hΔ hΘ)

end Metalean
