module

public import Metalean.Semantics.Soundness.Context.Admissible
public import Metalean.TypeTheory.Syntactic.Substitution

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ : CtxCat E ℓ}
  {σ₁ : Γ₂.as ⟶ Γ₁.as} {σ₂ : Γ₃ ⟶ Γ₂} {ρ₁ ρ₂ : RawValuation Γ₃}

def Agrees (σ₁ : Γ₂.as ⟶ Γ₁.as) (σ₂ : Γ₃ ⟶ Γ₂) (ρ₁ ρ₂ : RawValuation Γ₃) : Prop :=
  ∀ v, (rawInterpret (piLimit E ℓ) Γ₂ (σ₁.subst v)).app _ σ₂.op ρ₂ = ρ₁ v.db

def SemanticSubstitution (σ₁ : Γ₂.as ⟶ Γ₁.as) (σ₂ : Γ₃ ⟶ Γ₂) (ρ₁ ρ₂ : RawValuation Γ₃) : Prop :=
  ∀ ⦃Γ₄ Γ₅ : CtxCat E ℓ⦄ (σ₃ : Γ₄ ⟶ Γ₃) (r : Γ₅.as ⟶ Γ₂.as),
  RawCtx.Hom.IsRenaming r →
  ∀ (σ₄ : Γ₄ ⟶ Γ₅) (ρ₃ : RawValuation Γ₄),
  σ₄ ≫ RawCtx.toCtx.map r = σ₃ ≫ σ₂ →
  Agrees r σ₄ (ρ₂.pullback σ₃) ρ₃ →
  SourceAdmissible ((σ₃ ≫ σ₂) ≫ RawCtx.toCtx.map σ₁) (ρ₁.pullback σ₃) →
  Agrees (r ≫ σ₁) σ₄ (ρ₁.pullback σ₃) ρ₃

namespace Agrees

theorem of_var {r : Γ₂.as ⟶ Γ₁.as} {σ : Γ₃ ⟶ Γ₂} {ρ₁ ρ₂ : RawValuation Γ₃}
    (f : Var Γ₁.as.len → Var Γ₂.as.len) (hr : ∀ v, r.subst v = .var (f v))
    (h : ∀ v, ρ₂ (f v).db = ρ₁ v.db) : Agrees r σ ρ₁ ρ₂ := fun v => by
  rw [hr, rawInterpret_var]
  exact h v

theorem id (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) : Agrees (𝟙 Γ₁.as) σ ρ ρ :=
  of_var _ (fun _ => rfl) fun _ => rfl

theorem comp {r₁ : Γ₂.as ⟶ Γ₁.as} {σ₁ : Γ₃ ⟶ Γ₂}
    {ρ₁ ρ₂ : RawValuation Γ₃} (hr₁ : RawCtx.Hom.IsRenaming r₁) (h₁ : Agrees r₁ σ₁ ρ₁ ρ₂)
    {r₂ : Γ₅.as ⟶ Γ₂.as} {σ₂ : Γ₄ ⟶ Γ₅} {σ₃ : Γ₄ ⟶ Γ₃} {ρ₃ : RawValuation Γ₄}
    (h₂ : Agrees r₂ σ₂ (ρ₂.pullback σ₃) ρ₃) : Agrees (r₂ ≫ r₁) σ₂ (ρ₁.pullback σ₃) ρ₃ := fun v => by
  have ⟨w, hw⟩ := hr₁ v
  have h := h₁ v
  rw [hw, rawInterpret_var] at h
  change (rawInterpret (piLimit E ℓ) Γ₅ ((r₁.subst v).subst r₂.subst)).app _ σ₂.op ρ₃ = _
  rw [hw]
  exact (h₂ w).trans (congrArg (·.pullback σ₃) h)

end Agrees

namespace SemanticSubstitution

theorem pullback (h : SemanticSubstitution σ₁ σ₂ ρ₁ ρ₂) (σ₃ : Γ₄ ⟶ Γ₃) :
    SemanticSubstitution σ₁ (σ₃ ≫ σ₂) (ρ₁.pullback σ₃) (ρ₂.pullback σ₃) := by
  intro Γ₅ Γ₆ σ₄ r hr σ₅ ρ₃ hσ hag hadm
  rw [RawValuation.pullback_comp] at hag hadm ⊢
  exact h (σ₄ ≫ σ₃) r hr σ₅ ρ₃ (by rw [hσ, Category.assoc]) hag
    (by simpa only [Category.assoc] using hadm)

theorem variable_eq (h : SemanticSubstitution σ₁ σ₂ ρ₁ ρ₂)
    (hadm : SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁) ρ₁) : Agrees σ₁ σ₂ ρ₁ ρ₂ := by
  simpa using h (𝟙 Γ₃) (𝟙 Γ₂.as) .id σ₂ ρ₂
    (by simp; exact Category.comp_id σ₂)
    (by simpa using Agrees.id σ₂ ρ₂) (by simpa using hadm)

theorem ren (hr : RawCtx.Hom.IsRenaming σ₁) (h : Agrees σ₁ σ₂ ρ₁ ρ₂) :
    SemanticSubstitution σ₁ σ₂ ρ₁ ρ₂ :=
  fun _ _ _ _ _ _ _ _ hag _ => h.comp hr hag

theorem id (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) : SemanticSubstitution (𝟙 Γ₁.as) σ ρ ρ :=
  ren .id (Agrees.id σ ρ)

theorem reindex (h : SemanticSubstitution σ₁ σ₂ ρ₁ ρ₂) {r : Γ₄.as ⟶ Γ₂.as}
    (hr : RawCtx.Hom.IsRenaming r) (σ₃ : Γ₃ ⟶ Γ₄) (hσ : σ₃ ≫ RawCtx.toCtx.map r = σ₂) {ρ₃ : RawValuation Γ₃}
    (hag : Agrees r σ₃ ρ₂ ρ₃) : SemanticSubstitution (r ≫ σ₁) σ₃ ρ₁ ρ₃ := by
  intro Γ₅ Γ₆ σ₄ r₁ hr₁ σ₅ ρ₄ hσ₅ hag₁ hadm
  rw [← Category.assoc]
  refine h σ₄ (r₁ ≫ r) (hr₁.comp hr) σ₅ ρ₄
    (by rw [Functor.map_comp, ← Category.assoc, hσ₅, Category.assoc, hσ]) (hag.comp hr hag₁) ?_
  simpa only [Functor.map_comp, Category.assoc, ← Category.assoc σ₃, hσ] using hadm

theorem nil (σ₁ : Γ₂.as ⟶ (CtxCat.nil E ℓ).as) (σ₂ : Γ₃ ⟶ Γ₂) (ρ₁ ρ₂ : RawValuation Γ₃) :
    SemanticSubstitution σ₁ σ₂ ρ₁ ρ₂ :=
  fun _ _ _ _ _ _ _ _ _ _ v => v.elim0

end SemanticSubstitution

def HasSubstitution (Γ₁ : CtxCat E ℓ) (e : Expr ζ ℓ Γ₁.as.len) : Prop :=
  ∀ ⦃Γ₂ Γ₃ : CtxCat E ℓ⦄ (σ₁ : Γ₂.as ⟶ Γ₁.as) (σ₂ : Γ₃ ⟶ Γ₂) (ρ₁ ρ₂ : RawValuation Γ₃),
    SemanticSubstitution σ₁ σ₂ ρ₁ ρ₂ → SourceAdmissible (σ₂ ≫ RawCtx.toCtx.map σ₁) ρ₁ →
      (rawInterpret (piLimit E ℓ) Γ₂ (e.subst σ₁.subst)).app _ σ₂.op ρ₂ =
        (rawInterpret (piLimit E ℓ) Γ₁ e).app _ (σ₂ ≫ RawCtx.toCtx.map σ₁).op ρ₁

namespace HasSubstitution

theorem rename {e : Expr ζ ℓ Γ₁.as.len} (h : HasSubstitution Γ₁ e) {r : Γ₂.as ⟶ Γ₁.as}
    (hr : RawCtx.Hom.IsRenaming r) (σ : Γ₃ ⟶ Γ₂) {ρ₁ ρ₂ : RawValuation Γ₃} (hag : Agrees r σ ρ₁ ρ₂)
    (hadm : SourceAdmissible (σ ≫ RawCtx.toCtx.map r) ρ₁) :
    (rawInterpret (piLimit E ℓ) Γ₂ (e.subst r.subst)).app _ σ.op ρ₂ =
      (rawInterpret (piLimit E ℓ) Γ₁ e).app _ (σ ≫ RawCtx.toCtx.map r).op ρ₁ :=
  h r σ ρ₁ ρ₂ (.ren hr hag) hadm

theorem closed_valuation {e : Expr ζ ℓ 0} (h : HasSubstitution (CtxCat.nil E ℓ) e)
    (σ : Γ₁ ⟶ CtxCat.nil E ℓ) (ρ₁ ρ₂ : RawValuation Γ₁) :
    (rawInterpret (piLimit E ℓ) (CtxCat.nil E ℓ) e).app _ σ.op ρ₁ =
      (rawInterpret (piLimit E ℓ) (CtxCat.nil E ℓ) e).app _ σ.op ρ₂ := by
  have h' := h (𝟙 (CtxCat.nil E ℓ).as) σ ρ₂ ρ₁ (.nil _ _ _ _) (.nil _ _)
  rwa [RawCtx.Hom.id_subst, Expr.subst_id,
    CtxCat.hom_nil_eq (σ ≫ RawCtx.toCtx.map (𝟙 (CtxCat.nil E ℓ).as)) σ] at h'

theorem var (Γ₁ : CtxCat E ℓ) (v : Var Γ₁.as.len) : HasSubstitution Γ₁ (.var v) := by
  intro Γ₂ Γ₃ σ₁ σ₂ ρ₁ ρ₂ hσ₁ hρ
  rw [rawInterpret_var]
  exact hσ₁.variable_eq hρ v

theorem sort (Γ₁ : CtxCat E ℓ) (u : Level ℓ) : HasSubstitution Γ₁ (.sort u) := by
  intro Γ₂ Γ₃ σ₁ σ₂ ρ₁ ρ₂ hσ₁ hρ
  simp only [Expr.subst_sort, rawInterpret_sort, RawFamily.sort_value]

end HasSubstitution

namespace SemanticSubstitution

theorem snoc {t : Expr ζ ℓ Γ₁.as.len} {e : Expr ζ ℓ Γ₂.as.len} {u : Level ℓ}
    (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u) (σ₁ : Γ₂.as ⟶ Γ₁.as)
    (he : E[Γ₂.as.ctx] ⊢ₛ e : t.subst σ₁.subst) (pe : HasSubstitution Γ₂ e)
    (σ₂ : Γ₃ ⟶ Γ₂) (ρ₁ ρ₂ : RawValuation Γ₃) (htarget : SourceAdmissible σ₂ ρ₂)
    (htail : SemanticSubstitution σ₁ σ₂ ρ₁ ρ₂) :
    SemanticSubstitution (σ₁.snoc ⟨u, ht⟩ he) σ₂
      (ρ₁.push ((rawInterpret (piLimit E ℓ) Γ₂ e).app _ σ₂.op ρ₂)) ρ₂ := by
  intro Γ₄ Γ₅ σ₃ r hr σ₄ ρ₃ hσ hag hadm v
  rw [RawValuation.pullback_push, RawFamily.app_pullback] at hadm ⊢
  cases v using Fin.lastCases with
  | last =>
    change (rawInterpret (piLimit E ℓ) Γ₅ ((σ₁.subst.extend e (Fin.last _)).subst r.subst)).app _
      σ₄.op ρ₃ = _
    rw [Subst.extend_last, Var.db_last, pe.rename hr σ₄ hag (by rw [hσ]; exact htarget.pullback σ₃),
      hσ]
    rfl
  | cast v =>
    have hadm' := SourceAdmissible.tail ht hadm
    rw [Category.assoc, CtxCat.snoc_projection, RawValuation.tail_push] at hadm'
    change (rawInterpret (piLimit E ℓ) Γ₅ ((σ₁.subst.extend e v.castSucc).subst r.subst)).app _
      σ₄.op ρ₃ = _
    rw [Subst.extend_castSucc, Var.db_castSucc]
    exact htail σ₃ r hr σ₄ ρ₃ hσ hag hadm' v

theorem lift {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ} (ht : E[Γ₁.as.ctx] ⊢ₛ t : .sort u)
    (σ₁ : Γ₂.as ⟶ Γ₁.as) (σ₂ : Γ₃ ⟶ Γ₂.extension (ht.substitution σ₁.typed))
    (ρ₁ ρ₂ : RawValuation Γ₃)
    (htail : SemanticSubstitution σ₁ (σ₂ ≫ Γ₂.rawProjection (ht.substitution σ₁.typed)) ρ₁
      ρ₂.tail) :
    SemanticSubstitution (σ₁.lift ⟨u, ht⟩) σ₂ (ρ₁.push (ρ₂ 0)) ρ₂ := by
  intro Γ₄ Γ₅ σ₃ r hr σ₄ ρ₃ hσ hag hadm v
  rw [RawValuation.pullback_push] at hadm ⊢
  cases v using Fin.lastCases with
  | last =>
    change (rawInterpret (piLimit E ℓ) Γ₅ ((σ₁.subst.lift (Fin.last _)).subst r.subst)).app _
      σ₄.op ρ₃ = _
    have h := hag (Fin.last _)
    rw [Var.db_last] at h
    rw [Subst.lift_last, Var.db_last]
    exact h
  | cast v =>
    have hadm' := SourceAdmissible.tail ht hadm
    change SourceAdmissible (((σ₃ ≫ σ₂) ≫ CtxCat.extensionMap ht σ₁) ≫ CtxCat.rawProjection Γ₁ ht)
      ((ρ₁.pullback σ₃).push ((ρ₂.pullback σ₃) 0)).tail at hadm'
    rw [Category.assoc, CtxCat.extensionMap_projection ht σ₁, ← Category.assoc,
      RawValuation.tail_push] at hadm'
    change (rawInterpret (piLimit E ℓ) Γ₅ ((σ₁.subst.lift v.castSucc).subst r.subst)).app _
      σ₄.op ρ₃ = _
    rw [Subst.lift_castSucc, Expr.wk_subst, Var.db_castSucc]
    exact htail σ₃ (r ≫ CtxCat.projectionRaw Γ₂ (ht.substitution σ₁.typed))
      (hr.comp fun w => ⟨_, rfl⟩) σ₄ ρ₃
      (by rw [Functor.map_comp, ← Category.assoc, hσ, Category.assoc]; rfl)
      (fun w => by
        have h := hag w.castSucc
        rw [Var.db_castSucc] at h
        exact h)
      (by simpa only [Category.assoc] using hadm') v

theorem comp {σ₁ : Γ₂.as ⟶ Γ₁.as} {σ₂ : Γ₃.as ⟶ Γ₂.as} {σ₃ : Γ₄ ⟶ Γ₃}
    {ρ₁ ρ₂ ρ₃ : RawValuation Γ₄}
    (h₁ : SemanticSubstitution σ₁ (σ₃ ≫ RawCtx.toCtx.map σ₂) ρ₁ ρ₂)
    (h₂ : SemanticSubstitution σ₂ σ₃ ρ₂ ρ₃)
    (hadm : SourceAdmissible (σ₃ ≫ RawCtx.toCtx.map σ₂) ρ₂)
    (himages : ∀ v, HasSubstitution Γ₂ (σ₁.subst v)) :
    SemanticSubstitution (σ₂ ≫ σ₁) σ₃ ρ₁ ρ₃ := by
  intro Γ₅ Γ₆ σ₄ r hr σ₅ ρ₄ hσ hag hadm₁ v
  have hover : σ₅ ≫ RawCtx.toCtx.map (r ≫ σ₂) = σ₄ ≫ σ₃ ≫ RawCtx.toCtx.map σ₂ := by
    rw [Functor.map_comp, ← Category.assoc, hσ, Category.assoc]
  have hvalue := himages v (r ≫ σ₂) σ₅ (ρ₂.pullback σ₄) ρ₄
    ((h₂.pullback σ₄).reindex hr σ₅ hσ hag) (by rw [hover]; exact hadm.pullback σ₄)
  rw [hover] at hvalue
  have hvar := (h₁.pullback σ₄).variable_eq
    (by simpa only [Functor.map_comp, Category.assoc] using hadm₁) v
  rw [← Category.assoc]
  exact hvalue.trans hvar

theorem ofHom {n : Nat} {ctx : Ctx ζ ℓ 0 n} (hctx : E[ctx] ⊢ₛ ok)
    (σ₁ : Γ₂.as ⟶ (⟨ctx, hctx⟩ : CtxCat E ℓ).as) (σ₂ : Γ₃ ⟶ Γ₂) (ρ : RawValuation Γ₃)
    (pσ₁ : ∀ v, HasSubstitution Γ₂ (σ₁.subst v)) (htarget : SourceAdmissible σ₂ ρ) :
    SemanticSubstitution σ₁ σ₂
      (RawValuation.pushFin (fun _ => ⊥)
        fun v => (rawInterpret (piLimit E ℓ) Γ₂ (σ₁.subst v)).app _ σ₂.op ρ) ρ := by
  induction hctx with
  | nil => exact SemanticSubstitution.nil _ _ _ _
  | @snoc n ctx t hctx ht ih =>
    have ⟨u, ht⟩ := ht
    let σ₃ : Γ₂.as ⟶ (⟨ctx, hctx⟩ : CtxCat E ℓ).as := σ₁ ≫ CtxCat.projectionRaw ⟨ctx, hctx⟩ ht
    have he : E[Γ₂.as.ctx] ⊢ₛ σ₁.subst (Fin.last n) : t.subst σ₃.subst := by
      have he := σ₁.typed (Fin.last n)
      rwa [Ctx.get_last, Expr.wk_subst] at he
    have hsub := SemanticSubstitution.snoc ht σ₃ he (pσ₁ (Fin.last n)) σ₂ _ ρ htarget
      (ih σ₃ fun v => pσ₁ v.castSucc)
    rwa [show σ₃.snoc ⟨u, ht⟩ he = σ₁ from RawCtx.Hom.ext (Fin.snoc_init_self σ₁.subst)] at hsub

end SemanticSubstitution

end Metalean.CoherentShape
