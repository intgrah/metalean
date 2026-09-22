/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Semantics.Soundness.Judgment
public import Metalean.TypeTheory.Syntactic.Telescope
import Metalean.Semantics.Interpretation.Binder.Ideality
import Metalean.Semantics.Interpretation
import Metalean.Semantics.Interpretation.Telescope
import Metalean.TypeTheory.Syntactic.Substitution

@[expose] public section

namespace Metalean

open CategoryTheory CoherentShape CodeAssignment

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {pre : E₁.as ⟶ E₂.as} {ℓ n : Nat}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₂ (.inductive ι)} {Γ₁ Γ₂ : CtxCat E₂ ℓ}

namespace CoherentShape

variable {Src Tgt Γ : CtxCat E₂ ℓ}

theorem RawTeleProperties.extend_admissible {m k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ₂ ℓ Src.as.len m) (hk : Src.as.len + k = m) (hΔ : TeleWF E₂ P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E₂ Src.as.ctx Δ) (σ₁ : Tgt.as ⟶ (CtxCat.extendTele Src Δ hΔ).as)
    (pσ₁ : ∀ i : Fin k, RawInterpretationProperties Tgt
      (σ₁.subst ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩))
    (hfixed : ∀ i : Fin k, HasFixedness Tgt
      (σ₁.subst ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩)
      ((Ctx.get ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩ (Src.as.ctx ++ Δ)).subst σ₁.subst))
    (σ₂ : Γ ⟶ Tgt) (ρs ρt : RawValuation Γ)
    (hsub : SemanticSubstitution (σ₁ ≫ RawCtx.Hom.teleProjection hΔ) σ₂ ρs ρt)
    (hsource : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map (σ₁ ≫ RawCtx.Hom.teleProjection hΔ)) ρs)
    (htarget : SourceAdmissible σ₂ ρt) :
    SemanticSubstitution σ₁ σ₂
        (ρs.pushFin fun i : Fin k => (rawInterpret (piLimit E₂ ℓ) Tgt
          (σ₁.subst ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩)).app _ σ₂.op ρt) ρt ∧
      SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁)
        (ρs.pushFin fun i : Fin k => (rawInterpret (piLimit E₂ ℓ) Tgt
          (σ₁.subst ⟨Src.as.len + i.val, show Src.as.len + i.val < m by omega⟩)).app _ σ₂.op ρt) := by
  subst hk
  change ∀ i, RawInterpretationProperties Tgt (σ₁.subst (Fin.natAdd Src.as.len i)) at pσ₁
  change ∀ i, HasFixedness Tgt (σ₁.subst (Fin.natAdd Src.as.len i))
    ((Ctx.get (Fin.natAdd Src.as.len i) (Src.as.ctx ++ Δ)).subst σ₁.subst) at hfixed
  induction Δ using Tele.addInduction with
  | nil => exact ⟨hsub, hsource⟩
  | snoc k Δ t ih =>
    let S := CtxCat.extendTele Src Δ hΔ.init
    have ht : E₂[S.as.ctx] ⊢ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    obtain ⟨σ₃, arg, harg, rfl⟩ := RawCtx.Hom.exists_snoc (Γ₂ := S.as) ⟨_, ht⟩ σ₁
    have hbase : σ₃.snoc ⟨_, ht⟩ harg ≫ RawCtx.Hom.teleProjection hΔ =
        σ₃ ≫ RawCtx.Hom.teleProjection hΔ.init :=
      RawCtx.Hom.ext (funext fun v => Subst.extend_castSucc σ₃.subst arg (v.castLE Δ.le))
    have hsub := congr(SemanticSubstitution $hbase σ₂ ρs ρt).mp hsub
    have hsource := congr(SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map $hbase) ρs).mp hsource
    have ⟨hsubInit, hadmInit⟩ := ih hΔ.init pΔ.init σ₃
      (pσ₁ := fun i => by simpa only [S, CtxCat.extendTele, RawCtx.Hom.snoc_subst,
        Fin.natAdd_castSucc, Subst.extend_castSucc] using pσ₁ i.castSucc)
      (hfixed := fun i => by simpa only [S, CtxCat.extendTele, RawCtx.Hom.snoc_subst,
        Fin.natAdd_castSucc, Subst.extend_castSucc, Tele.append_snoc, Ctx.get_castSucc,
        Expr.wk_subst_extend] using hfixed i.castSucc)
      hsub hsource
    have parg : RawInterpretationProperties Tgt arg := by
      simpa [S, CtxCat.extendTele] using pσ₁ (Fin.last k)
    have hargf : HasFixedness Tgt arg (t.subst σ₃.subst) := by
      simpa [S, CtxCat.extendTele, Expr.wk_subst_extend] using hfixed (Fin.last k)
    have pt : RawInterpretationProperties S t := pΔ.last S.as.wf
    have he := pt.subst σ₃ σ₂ _ ρt hsubInit hadmInit
    have hfix := hargf harg σ₂ ρt htarget
    rw [he] at hfix
    have hadm := hadmInit.push ht ((Raw.ContextSection.ofTyping ht σ₃ harg).pullback σ₂)
      (pt.ideal _ _ hadmInit) (parg.ideal σ₂ ρt htarget) hfix
    have hs := SemanticSubstitution.snoc ht σ₃ harg parg.subst
      σ₂ _ ρt htarget hsubInit
    change SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map (σ₃.snoc ⟨_, ht⟩ harg)) _ at hadm
    change SemanticSubstitution _ _ (ρs.pushFin fun i : Fin (k + 1) =>
      (rawInterpret (piLimit E₂ ℓ) Tgt (σ₃.subst.extend arg (Fin.natAdd Src.as.len i))).app _ σ₂.op ρt) _ ∧
      SourceAdmissible _ (ρs.pushFin fun i : Fin (k + 1) =>
        (rawInterpret (piLimit E₂ ℓ) Tgt (σ₃.subst.extend arg (Fin.natAdd Src.as.len i))).app _ σ₂.op ρt)
    simp only [RawValuation.pushFin, Fin.natAdd_castSucc, Fin.natAdd_last,
      Subst.extend_castSucc, Subst.extend_last, S, CtxCat.extendTele]
    exact ⟨hs, hadm⟩

namespace RawTeleProperties

theorem fixed_image {ctx : Ctx ζ₂ ℓ 0 n}
    (hctx : E₂[ctx] ⊢ ok) (pctx : RawTeleProperties E₂ .nil ctx)
    (σ₁ : Γ₁.as ⟶ (⟨ctx, hctx⟩ : CtxCat E₂ ℓ).as) (v : Fin n)
    (pσ₁ : ∀ w < v, HasSubstitution Γ₁ (σ₁.subst w))
    (σ₂ : Γ₂ ⟶ Γ₁) (ρs ρt : RawValuation Γ₂)
    (hsource : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁) ρs)
    (htarget : SourceAdmissible σ₂ ρt)
    (hvals : ∀ w < v,
      (rawInterpret (piLimit E₂ ℓ) Γ₁ (σ₁.subst w)).app _ σ₂.op ρt = ρs (Var.db w)) :
    (piLimit E₂ ℓ).rawExtend
      ((rawInterpret (piLimit E₂ ℓ) Γ₁ ((ctx.get v).subst σ₁.subst)).app _ σ₂.op ρt)
      ((Tm E₂ ℓ).map σ₂.op (Tm.label Γ₁.as (σ₁.typed v))) (ρs (Var.db v)) = ρs (Var.db v) := by
  induction ctx generalizing ρs with
  | nil => exact v.elim0
  | @snoc n ctx t ih =>
    have ht := hctx.last.choose_spec
    have hctx : E₂[ctx] ⊢ ok := hctx.init
    let σ₃ := σ₁ ≫ CtxCat.projectionRaw ⟨ctx, hctx⟩ ht
    have htail := SourceAdmissible.tail (Γ₁ := ⟨ctx, hctx⟩) ht hsource
    rw [Category.assoc] at htail
    change SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₃) ρs.tail at htail
    cases v using Fin.lastCases with
    | cast v =>
      have h := ih hctx pctx.init σ₃ v
        (fun w hw => pσ₁ w.castSucc hw) ρs.tail htail
        (fun w hw => by
          have h := hvals w.castSucc hw
          rw [Var.db_castSucc] at h
          exact h)
      simp only [Ctx.get_castSucc, Expr.wk_subst, Var.db_castSucc]
      exact h
    | last =>
      have pt := pctx.last
      rw [Tele.nil_append] at pt
      have pt := pt hctx
      have hs : SemanticSubstitution σ₃ σ₂ ρs.tail ρt := by
        intro Γ₃ Γ₄ τ r hr υ ρ hυ hag hadm w
        change (rawInterpret (piLimit E₂ ℓ) Γ₄
          ((σ₁.subst w.castSucc).subst r.subst)).app _ υ.op ρ = _
        rw [pσ₁ w.castSucc (Fin.castSucc_lt_last w) r υ _ _ (.ren hr hag)
          (by rw [hυ]; exact htarget.pullback τ), hυ, op_comp, ← RawFamily.app_pullback,
          hvals w.castSucc (Fin.castSucc_lt_last w)]
        rw [Var.db_castSucc]
        rfl
      have he := pt.subst σ₃ σ₂ ρs.tail ρt hs htail
      conv_lhs =>
        arg 2
        rw [Ctx.get_last, Expr.wk_subst]
        change (rawInterpret (piLimit E₂ ℓ) Γ₁ (t.subst σ₃.subst)).app _ σ₂.op ρt
        rw [he]
      rw [← Tm.map_varLabel σ₁ (Fin.last n), ← Functor.map_comp_apply, ← op_comp]
      have .cons _ _ _ _ _ _ hf := hsource
      simp only [σ₃, Functor.map_comp, Category.assoc, Var.db_last] at hf ⊢
      exact hf

theorem admissible_of_images {ctx : Ctx ζ₂ ℓ 0 n}
    (hctx : E₂[ctx] ⊢ ok) (hprops : RawTeleProperties E₂ .nil ctx)
    (σ₁ : Γ₁.as ⟶ (⟨ctx, hctx⟩ : CtxCat E₂ ℓ).as) (σ₂ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂)
    (htarget : SourceAdmissible σ₂ ρ)
    (pσ₁ : ∀ v, RawInterpretationProperties Γ₁ (σ₁.subst v))
    (hf : ∀ v, HasFixedness Γ₁ (σ₁.subst v) ((ctx.get v).subst σ₁.subst)) :
    SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁)
      (RawValuation.pushFin (fun _ => ⊥)
        fun v => (rawInterpret (piLimit E₂ ℓ) Γ₁ (σ₁.subst v)).app _ σ₂.op ρ) := by
  have hΔ := hctx.teleWF
  generalize hc : ctx = ctx' at hctx σ₁ pσ₁ hf ⊢
  rw [← Tele.nil_append ctx] at hc
  subst ctx'
  simpa using (hprops.extend_admissible ctx (Nat.zero_add n)
    hΔ σ₁ (by simpa using pσ₁) (by simpa using hf)
    σ₂ (fun _ => ⊥) ρ (.nil _ _ _ _) (.nil _ _) htarget).2

end RawTeleProperties

theorem RawFamily.ctxLam_isDirected {b m : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ₂ ℓ Γ₁.as.len m) (hΔ : TeleWF E₂ P Γ₁.as.ctx Δ)
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
      (fun _ _ _ hρ => RawAction.abstraction_isDirected _
        (RawFamily.bodyAction_isIdealValued hΔ.last.choose_spec.2 (pΔ.last _).ideal hB _ _ hρ))

end CoherentShape

theorem RawSound.teleProperties (hsound : RawSound E₂ ℓ pre) {Δ : Ctx ζ₁ ℓ 0 n} (hΔ : E₁[Δ] ⊢ ok)
    {P : Level ℓ → Prop} {m : Nat} {Θ : Ctx ζ₁ ℓ n m} (hΘ : TeleWF E₁ P Δ Θ) :
    RawTeleProperties E₂ (Δ.map pre.sigs) (Θ.map pre.sigs) := by
  induction hΘ with
  | nil => exact .nil
  | @snoc m Θ t hΘ ht ih =>
    have ⟨u, _, ht⟩ := ht
    exact .snoc ih fun wf => by
      revert wf
      rw [← Ctx.map_append]
      exact fun _ => (hsound.properties (TeleWF.appendCtxWF hΘ hΔ) ht).left

theorem RawSound.paramTeleProperties (hsound : RawSound E₂ ℓ pre) (hB : InductiveWF E₁ I)
    (hblock : (E₂.get η).block = I.map pre.sigs) (ls : Fin ι.nlevels → Level ℓ) :
    RawTeleProperties E₂ .nil (Ctx.instL ls (E₂.get η).block.params) := by
  have hp := hsound.teleProperties (.nil : E₁[(#t[] : Ctx ζ₁ ℓ 0 0)] ⊢ ok)
    (hB.params.instLevel (Q := fun _ => True) ls fun _ => trivial)
  rw [hblock]
  exact congr(RawTeleProperties E₂ _ $(Ctx.map_instL pre.sigs ls I.params)).mp hp

end Metalean
