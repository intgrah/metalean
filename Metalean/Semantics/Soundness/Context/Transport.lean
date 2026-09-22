/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Telescope.Basic

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Src Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}
  {σ₁ : Γ₂.as ⟶ Γ₁.as} {e t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}

structure SemanticHom (σ₁ : Γ₂.as ⟶ Γ₁.as) : Prop where
  image : ∀ v, HasSubstitution Γ₂ (σ₁.subst v)
  admissible : ∀ ⦃Γ₃ : CtxCat E ℓ⦄ (σ₂ : Γ₃ ⟶ Γ₂) (ρ : RawValuation Γ₃),
    SourceAdmissible σ₂ ρ →
    ∃ ρ₁, SemanticSubstitution σ₁ σ₂ ρ₁ ρ ∧ SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁) ρ₁

namespace SemanticHom

theorem id (Γ₁ : CtxCat E ℓ) : SemanticHom (𝟙 Γ₁.as) where
  image v := HasSubstitution.var Γ₁ v
  admissible _ σ ρ hρ := ⟨ρ, .id σ ρ, by
    change SourceAdmissible (σ ≫ 𝟙 Γ₁) ρ
    simpa using hρ⟩

theorem ofImages {n : Nat} {ctx : Ctx ζ ℓ 0 n} (hctx : E[ctx] ⊢ ok)
    (pctx : RawTeleProperties E .nil ctx) (σ₁ : Γ₂.as ⟶ (⟨ctx, hctx⟩ : CtxCat E ℓ).as)
    (pσ₁ : ∀ v, RawInterpretationProperties Γ₂ (σ₁.subst v))
    (fσ₁ : ∀ v, HasFixedness Γ₂ (σ₁.subst v) ((ctx.get v).subst σ₁.subst)) :
    SemanticHom σ₁ where
  image v := (pσ₁ v).subst
  admissible _ σ₂ ρ hρ := ⟨_, .ofHom hctx σ₁ σ₂ ρ (fun v => (pσ₁ v).subst) hρ,
    pctx.admissible_of_images hctx σ₁ σ₂ ρ hρ pσ₁ fσ₁⟩

theorem projection (ht : E[Γ₁.as.ctx] ⊢ t : .sort u) :
    SemanticHom (CtxCat.projectionRaw Γ₁ ht) where
  image v := HasSubstitution.var (Γ₁.extension ht) v.castSucc
  admissible _ _ ρ hρ := ⟨ρ.tail, .ren (fun _ => ⟨_, rfl⟩)
    (.of_var Fin.castSucc (fun _ => rfl) fun v => congrArg ρ (Var.db_castSucc v)), hρ.tail ht⟩

theorem ideal (h : SemanticHom σ₁) (pe : RawInterpretationProperties Γ₁ e) :
    HasIdeality Γ₂ (e.subst σ₁.subst) := by
  intro Γ₃ σ₂ ρ hρ
  have ⟨ρ₁, hs, hadm⟩ := h.admissible σ₂ ρ hρ
  rw [pe.subst σ₁ σ₂ ρ₁ ρ hs hadm]
  exact @pe.ideal Γ₃ _ _ hadm

theorem subst (h : SemanticHom σ₁) (pe : HasSubstitution Γ₁ e) :
    HasSubstitution Γ₂ (e.subst σ₁.subst) := by
  let := Subst.category ζ ℓ
  intro Γ₃ Γ₄ σ₂ σ₃ ρ₂ ρ₃ h₂ hadm₂
  have ⟨ρ₁, h₁, hadm₁⟩ := h.admissible (σ₃ ≫ RawCtx.toCtx.map σ₂) ρ₂ hadm₂
  have he₂ := pe (σ₂ ≫ σ₁) σ₃ ρ₁ ρ₃ (SemanticSubstitution.comp h₁ h₂ hadm₂ h.image)
    (by simpa using hadm₁)
  have he₁ := pe σ₁ (σ₃ ≫ RawCtx.toCtx.map σ₂) ρ₁ ρ₂ h₁ hadm₁
  rw [Functor.map_comp, ← Category.assoc] at he₂
  exact (congrArg (fun e => (rawInterpret (piLimit E ℓ) Γ₃ e).app _ σ₃.op ρ₃)
    ((Subst.functor _ _).map_comp_apply σ₁.subst σ₂.subst e)).symm.trans (he₂.trans he₁.symm)

theorem props (h : SemanticHom σ₁) (pe : RawInterpretationProperties Γ₁ e) :
    RawInterpretationProperties Γ₂ (e.subst σ₁.subst) :=
  ⟨h.ideal pe, h.subst pe.subst⟩

theorem fixed (h : SemanticHom σ₁) (he : E[Γ₁.as.ctx] ⊢ e : t) (pt : HasSubstitution Γ₁ t)
    (pe : HasSubstitution Γ₁ e) (hf : HasFixedness Γ₁ e t) :
    HasFixedness Γ₂ (e.subst σ₁.subst) (t.subst σ₁.subst) := by
  intro Γ₃ heσ σ₂ ρ hρ
  have ⟨ρ₁, hs, hadm⟩ := h.admissible σ₂ ρ hρ
  rw [show Tm.label Γ₂.as heσ = _ from (Tm.map_label he σ₁).symm, ← Functor.map_comp_apply,
    pt σ₁ σ₂ ρ₁ ρ hs hadm, pe σ₁ σ₂ ρ₁ ρ hs hadm]
  exact hf he _ _ hadm

theorem comp {σ₂ : Γ₃.as ⟶ Γ₂.as} (h₁ : SemanticHom σ₁) (h₂ : SemanticHom σ₂) :
    SemanticHom (σ₂ ≫ σ₁) where
  image v := h₂.subst (h₁.image v)
  admissible _ σ₃ ρ₃ hρ₃ := by
    have ⟨ρ₂, hs₂, ha₂⟩ := h₂.admissible σ₃ ρ₃ hρ₃
    have ⟨ρ₁, hs₁, ha₁⟩ := h₁.admissible _ ρ₂ ha₂
    exact ⟨ρ₁, hs₁.comp hs₂ ha₂ h₁.image, by simpa using ha₁⟩

theorem lift (h : SemanticHom σ₁) (ht : E[Γ₁.as.ctx] ⊢ t : .sort u)
    (pt : RawInterpretationProperties Γ₁ t) : SemanticHom (σ₁.lift ⟨u, ht⟩) where
  image v := by
    change HasSubstitution (Γ₂.extension (ht.substitution σ₁.typed)) (σ₁.subst.lift v)
    cases v using Fin.lastCases with
    | last => rw [Subst.lift_last]; exact HasSubstitution.var _ _
    | cast v =>
      rw [Subst.lift_castSucc, ← Expr.subst_wk]
      exact (projection (ht.substitution σ₁.typed)).subst (h.image v)
  admissible _ σ₂ ρ₂ hρ₂ := by
    have ⟨ρ₁, hs, ha⟩ := h.admissible _ ρ₂.tail (hρ₂.tail (ht.substitution σ₁.typed))
    refine ⟨ρ₁.push (ρ₂ 0), .lift ht σ₁ σ₂ ρ₁ ρ₂ hs, ?_⟩
    let s : Raw.ContextSection (ht.substitution σ₁.typed)
        (σ₂ ≫ Γ₂.rawProjection (ht.substitution σ₁.typed))
        ((Tm _ _).map σ₂.op (CtxCat.rawComprehension (ht.substitution σ₁.typed)).generic) := ⟨σ₂, rfl, rfl⟩
    have .cons _ _ _ _ _ hi hf := hρ₂
    refine ha.push ht (s.mapExtension ht σ₁) (pt.ideal _ _ ha) hi ?_
    rw [← pt.subst σ₁ _ ρ₁ ρ₂.tail hs ha]
    exact hf

theorem typed (h : SemanticHom σ₁) (p : RawTyped Γ₁ e t) :
    RawTyped Γ₂ (e.subst σ₁.subst) (t.subst σ₁.subst) :=
  ⟨p.typed.substitution σ₁.typed, h.props p.type, h.props p.term,
    h.fixed p.typed p.type.subst p.term.subst p.fixed⟩

theorem judgment {e₁ e₂ t : Expr ζ ℓ Γ₁.as.len} (h : SemanticHom σ₁) (p : RawJudgment Γ₁ e₁ e₂ t) :
    RawJudgment Γ₂ (e₁.subst σ₁.subst) (e₂.subst σ₁.subst) (t.subst σ₁.subst) where
  syntactic := p.syntactic.substitution σ₁.typed
  type := h.props p.type
  left := h.props p.left
  right := h.props p.right
  equal _ σ₂ ρ hρ := by
    have ⟨ρ₁, hs, ha⟩ := h.admissible σ₂ ρ hρ
    rw [p.left.subst σ₁ σ₂ ρ₁ ρ hs ha, p.right.subst σ₁ σ₂ ρ₁ ρ hs ha]
    exact p.equal _ _ ha
  fixed := h.fixed p.syntactic.left p.type.subst p.left.subst p.fixed

end SemanticHom

theorem HasSubstitution.wk_value (ht : E[Γ₁.as.ctx] ⊢ t : .sort u) (pe : HasSubstitution Γ₁ e)
    (σ : Γ₂ ⟶ Γ₁.extension ht) (ρ : RawValuation Γ₂)
    (hadm : SourceAdmissible (σ ≫ Γ₁.rawProjection ht) ρ.tail) :
    (rawInterpret (piLimit E ℓ) (Γ₁.extension ht) e.wk).app _ σ.op ρ =
      (rawInterpret (piLimit E ℓ) Γ₁ e).app _ (σ ≫ Γ₁.rawProjection ht).op ρ.tail := by
  rw [← Expr.subst_wk]
  exact pe _ σ ρ.tail ρ (.ren (fun v => ⟨_, rfl⟩)
    (.of_var Fin.castSucc (fun _ => rfl) fun v => congrArg ρ (Var.db_castSucc v))) hadm

theorem RawInterpretationProperties.wk (ht : E[Γ₁.as.ctx] ⊢ t : .sort u)
    (pe : RawInterpretationProperties Γ₁ e) :
    RawInterpretationProperties (Γ₁.extension ht) e.wk := by
  have h : RawInterpretationProperties (Γ₁.extension ht) (e.subst Subst.wk) :=
    (SemanticHom.projection ht).props pe
  rwa [Expr.subst_wk] at h

theorem RawInterpretationProperties.var (Γ₁ : CtxCat E ℓ) (v : Var Γ₁.as.len) :
    RawInterpretationProperties Γ₁ (.var v) where
  ideal := by
    intro Γ₂ σ ρ hadm
    rw [rawInterpret_var]
    exact SourceAdmissible.variable_isDirected hadm v
  subst := HasSubstitution.var Γ₁ v

theorem HasFixedness.varLast (ht : E[Γ₁.as.ctx] ⊢ t : .sort u) (pt : HasSubstitution Γ₁ t) :
    HasFixedness (Γ₁.extension ht) (.var (Fin.last Γ₁.as.len)) t.wk := by
  intro Γ₂ hterm σ ρ hadm
  have hname : Tm.label (Γ₁.extension ht).as hterm = (CtxCat.rawComprehension ht).generic :=
    Tm.label_eq_var hterm rfl
  rw [HasSubstitution.wk_value ht pt σ ρ (hadm.tail ht), hname]
  cases hadm with
  | cons _ _ _ _ _ _ hf =>
    simp only [rawInterpret_var, Var.db_last]
    exact hf

theorem RawTeleProperties.var {m : Nat} {P : Level ℓ → Prop} {Δ : Ctx ζ ℓ Γ₁.as.len m}
    (hΔ : TeleWF E P Γ₁.as.ctx Δ) (pΔ : RawTeleProperties E Γ₁.as.ctx Δ)
    (i : Fin m) (hi : Γ₁.as.len ≤ i.val) :
    RawTyped (CtxCat.extendTele Γ₁ Δ hΔ) (.var i) (Ctx.get i (Γ₁.as.ctx ++ Δ)) := by
  induction Δ with
  | nil => omega
  | snoc Δ t ih =>
    let T := CtxCat.extendTele Γ₁ Δ hΔ.init
    have ht : E[T.as.ctx] ⊢ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have pt : RawInterpretationProperties T t := pΔ.last _
    cases i using Fin.lastCases with
    | last =>
      simpa [T, CtxCat.extendTele] using
        (show RawTyped (T.extension ht) (.var (Fin.last T.as.len)) t.wk from
          ⟨CtxWF.varLast (T.as.wf.snoc ⟨_, ht⟩), pt.wk ht, .var _ _, .varLast ht pt.subst⟩)
    | cast i =>
      have p := (SemanticHom.projection ht).typed (ih hΔ.init pΔ.init i hi)
      simpa [T, CtxCat.extendTele, CtxCat.projectionRaw, Expr.subst_wk, Expr.var_wk] using p

theorem RawInterpretationProperties.wkN {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Γ₁.as.len (Γ₁.as.len + k)) (hΔ : TeleWF E P Γ₁.as.ctx Δ)
    (pe : RawInterpretationProperties Γ₁ e) :
    RawInterpretationProperties (CtxCat.extendTele Γ₁ Δ hΔ) (e.wkN k) := by
  induction Δ using Tele.addInduction with
  | nil => exact pe
  | snoc k Δ t ih => exact (ih hΔ.init).wk hΔ.last.choose_spec.2

theorem RawTeleProperties.ofTypes {k : Nat} {P : Level ℓ → Prop}
    {types : Fin k → Expr ζ ℓ Γ₁.as.len} (hΘ : TeleWF E P Γ₁.as.ctx (Ctx.ofTypes types))
    (ptypes : ∀ i, RawInterpretationProperties Γ₁ (types i)) :
    RawTeleProperties E Γ₁.as.ctx (Ctx.ofTypes types) := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    exact .snoc (ih hΘ.init fun i => ptypes i.castSucc)
      fun _ => (ptypes (Fin.last k)).wkN _ hΘ.init

theorem HasSubstitution.congrImages {e : Expr ζ ℓ Src.as.len}
    (pe : HasSubstitution Src e) (pctx : RawTeleProperties E .nil Src.as.ctx)
    (σ₁ σ₁' : Γ₁.as ⟶ Src.as) (hσ₁ : RawCtx.toCtx.map σ₁ = RawCtx.toCtx.map σ₁')
    (hi : ∀ v, HasIdeality Γ₁ (σ₁.subst v))
    (hr : ∀ v, HasSubstitution Γ₁ (σ₁.subst v))
    (hr' : ∀ v, HasSubstitution Γ₁ (σ₁'.subst v))
    (hf : ∀ v, HasFixedness Γ₁ (σ₁.subst v) ((Src.as.ctx.get v).subst σ₁.subst))
    (he : ∀ v, HasEquality Γ₁ (σ₁.subst v) (σ₁'.subst v)) :
    HasEquality Γ₁ (e.subst σ₁.subst) (e.subst σ₁'.subst) := by
  intro Γ₂ σ₂ ρ hρ
  have hadm := pctx.admissible_of_images Src.as.wf σ₁ σ₂ ρ hρ (fun v => ⟨hi v, hr v⟩) hf
  have hvalues : (RawValuation.pushFin (fun _ => ⊥) fun v =>
      (rawInterpret (piLimit E ℓ) Γ₁ (σ₁.subst v)).app _ σ₂.op ρ) =
      RawValuation.pushFin (fun _ => ⊥) fun v =>
        (rawInterpret (piLimit E ℓ) Γ₁ (σ₁'.subst v)).app _ σ₂.op ρ :=
    congrArg (RawValuation.pushFin fun _ => ⊥) (funext fun v => he v σ₂ ρ hρ)
  have hadm' := hadm
  rw [hσ₁, hvalues] at hadm'
  rw [pe σ₁ σ₂ _ ρ (SemanticSubstitution.ofHom Src.as.wf σ₁ σ₂ ρ hr hρ) hadm,
    pe σ₁' σ₂ _ ρ (SemanticSubstitution.ofHom Src.as.wf σ₁' σ₂ ρ hr' hρ) hadm',
    hσ₁, hvalues]

end Metalean.CoherentShape
