module

public import Metalean.Semantics.Soundness.Context.Transport
public import Metalean.Semantics.Soundness.Rules.Function
public import Metalean.TypeTheory.Syntactic.Telescope
import Metalean.Semantics.Soundness.Rules.Core

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Src Tgt Γ₁ Γ₂ : CtxCat E ℓ}
  {k : Nat} {P : Level ℓ → Prop} {Δ : Ctx ζ ℓ Γ₁.as.len (Γ₁.as.len + k)}

theorem RawTeleProperties.substitution_images {k : Nat} {P : Level ℓ → Prop}
    (pctx : RawTeleProperties E .nil Src.as.ctx)
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (σ : Tgt.as ⟶ Src.as)
    (pi : ∀ v, RawInterpretationProperties Tgt (σ.subst v))
    (pf : ∀ v, HasFixedness Tgt (σ.subst v) ((Src.as.ctx.get v).subst σ.subst)) :
    (∀ v, RawInterpretationProperties
        (CtxCat.extendTele Tgt (Ctx.substN σ.subst k Δ) (hΔ.substitution σ.typed))
        ((σ.liftTele hΔ).subst v)) ∧
      ∀ v, HasFixedness
        (CtxCat.extendTele Tgt (Ctx.substN σ.subst k Δ) (hΔ.substitution σ.typed))
        ((σ.liftTele hΔ).subst v)
        (((CtxCat.extendTele Src Δ hΔ).as.ctx.get v).subst (σ.liftTele hΔ).subst) := by
  induction Δ using Tele.addInduction with
  | nil => exact ⟨pi, pf⟩
  | snoc k Δ t ih =>
    let S := CtxCat.extendTele Src Δ hΔ.init
    let T := CtxCat.extendTele Tgt (Ctx.substN σ.subst k Δ) (hΔ.init.substitution σ.typed)
    let g : T.as ⟶ S.as := σ.liftTele hΔ.init
    have ht : E[S.as.ctx] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have htσ : E[T.as.ctx] ⊢ₛ t.subst g.subst : .sort hΔ.last.choose := ht.substitution g.typed
    have ⟨pi', pf'⟩ := ih hΔ.init pΔ.init
    have pS : RawTeleProperties E .nil S.as.ctx := pctx.append (by simpa using pΔ.init)
    have hg := SemanticHom.ofImages S.as.wf pS g pi' pf'
    have ptσ : RawInterpretationProperties T (t.subst g.subst) := hg.props (pΔ.last S.as.wf)
    refine ⟨fun v => ?_, fun v => ?_⟩
    · cases v using Fin.lastCases with
      | last =>
        change RawInterpretationProperties (T.extension htσ) (g.subst.lift (Fin.last S.as.len))
        erw [Subst.lift_last]
        exact RawInterpretationProperties.var (T.extension htσ) _
      | cast v =>
        change RawInterpretationProperties (T.extension htσ) (g.subst.lift v.castSucc)
        erw [Subst.lift_castSucc]
        exact (pi' v).wk htσ
    · cases v using Fin.lastCases with
      | last =>
        change HasFixedness (T.extension htσ) (g.subst.lift (Fin.last S.as.len))
          ((Ctx.get (Fin.last S.as.len) (S.as.ctx.snoc t)).subst g.subst.lift)
        erw [Subst.lift_last, Ctx.get_last, Expr.wk_subst_lift]
        exact HasFixedness.varLast htσ ptσ.subst
      | cast v =>
        change HasFixedness (T.extension htσ) (g.subst.lift v.castSucc)
          ((Ctx.get v.castSucc (S.as.ctx.snoc t)).subst g.subst.lift)
        erw [Subst.lift_castSucc, Ctx.get_snoc S.as.ctx t v.castSucc (Nat.ne_of_lt v.isLt),
          Fin.castLT_castSucc, Expr.wk_subst_lift]
        have pget : RawInterpretationProperties T ((S.as.ctx.get v).subst g.subst) :=
          hg.props (pS.get S.as.wf v)
        exact HasFixedness.wk htσ (g.typed v) pget.subst (pi' v).subst (pf' v)

theorem RawTeleProperties.substitution {k : Nat} {P : Level ℓ → Prop}
    (pctx : RawTeleProperties E .nil Src.as.ctx)
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (σ : Tgt.as ⟶ Src.as)
    (pi : ∀ v, RawInterpretationProperties Tgt (σ.subst v))
    (pf : ∀ v, HasFixedness Tgt (σ.subst v) ((Src.as.ctx.get v).subst σ.subst)) :
    RawTeleProperties E Tgt.as.ctx (Ctx.substN σ.subst k Δ) := by
  induction Δ using Tele.addInduction with
  | nil => exact .nil
  | snoc k Δ t ih =>
    let S := CtxCat.extendTele Src Δ hΔ.init
    have ⟨pi', pf'⟩ := pctx.substitution_images Δ hΔ.init pΔ.init σ pi pf
    have pS : RawTeleProperties E .nil S.as.ctx := pctx.append (by simpa using pΔ.init)
    have hg := SemanticHom.ofImages S.as.wf pS (σ.liftTele hΔ.init) pi' pf'
    exact .snoc (ih hΔ.init pΔ.init) fun _ => hg.props (pΔ.last S.as.wf)

theorem RawInterpretationProperties.pi {k : Nat} {P : Level ℓ → Prop} {v : Level ℓ}
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (body : Expr ζ ℓ (Src.as.len + k))
    (hbody : E[Src.as.ctx ++ Δ] ⊢ₛ body : .sort v)
    (pbody : RawInterpretationProperties (CtxCat.extendTele Src Δ hΔ) body) :
    RawInterpretationProperties Src (Ctx.pi body Δ) := by
  induction Δ using Tele.addInduction generalizing v with
  | nil => exact pbody
  | snoc k Δ t ih =>
    have ht : E[Src.as.ctx ++ Δ] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    exact ih hΔ.init pΔ.init (.forallE t body) (.forallEDF ht hbody hbody)
      (RawInterpretationProperties.forallE ht hbody (pΔ.last _) pbody)

theorem HasFixedness.pi_prop {k : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (body : Expr ζ ℓ (Src.as.len + k))
    (hbody : E[Src.as.ctx ++ Δ] ⊢ₛ body : .prop)
    (pbody : HasFixedness (CtxCat.extendTele Src Δ hΔ) body .prop) :
    HasFixedness Src (Ctx.pi body Δ) .prop := by
  induction Δ using Tele.addInduction with
  | nil => exact pbody
  | snoc k Δ t ih =>
    have ht : E[Src.as.ctx ++ Δ] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have hp : HasFixedness (CtxCat.extendTele Src Δ hΔ.init) (.forallE t body)
        (.sort (.imax hΔ.last.choose .zero)) :=
      HasFixedness.forallE ht hbody (pΔ.last _).ideal pbody
    have hty := DefeqStrong.forallEDF ht hbody hbody
    rw [Level.imax_zero] at hp hty
    exact ih hΔ.init pΔ.init (.forallE t body) hty hp

theorem SemanticSubstitution.tailTele {m : Nat} {Δ : Ctx ζ ℓ Γ₁.as.len m}
    (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (σ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ : RawValuation Γ₂) :
    SemanticSubstitution (RawCtx.Hom.teleProjection hΔ) σ
      (ρ.tailN (m - Γ₁.as.len)) ρ :=
  .ren (fun v => ⟨_, rfl⟩) (.of_var (Fin.castLE Δ.le) (fun _ => rfl) fun v => by
    rw [Var.db_castLE, RawValuation.tailN_apply])

theorem SourceAdmissible.tailTele {m : Nat} {Δ : Ctx ζ ℓ Γ₁.as.len m}
    (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    {σ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ} {ρ : RawValuation Γ₂}
    (hρ : SourceAdmissible σ ρ) :
    SourceAdmissible (σ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ))
      (ρ.tailN (m - Γ₁.as.len)) := by
  have ⟨k, hk⟩ := Nat.exists_eq_add_of_le Δ.le
  subst m
  simp only [Nat.add_sub_cancel_left]
  induction Δ using Tele.addInduction generalizing ρ with
  | nil =>
    have hp : RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ) = 𝟙 Γ₁ :=
      congrArg RawCtx.toCtx.map (RawCtx.Hom.ext rfl)
    erw [hp, Category.comp_id]
    exact hρ
  | snoc k Δ A ih =>
    have hA := hΔ.last.choose_spec.2
    have hρtail := SourceAdmissible.tail (Γ₁ := CtxCat.extendTele Γ₁ Δ hΔ.init) hA hρ
    have htail := ih hΔ.init hρtail
    rw [RawCtx.Hom.teleProjection_snoc hΔ.init hΔ.last.choose_spec.1 hA]
    have hcoords : ρ.tail.tailN k = ρ.tailN (k + 1) :=
      (RawValuation.tailN_tailN ρ 1 k).trans (congrArg ρ.tailN (Nat.add_comm 1 k))
    erw [hcoords, Category.assoc] at htail
    exact htail

theorem HasSubstitution.wkN_value {e : Expr ζ ℓ Γ₁.as.len}
    (pe : HasSubstitution Γ₁ e) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (σ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ : RawValuation Γ₂)
    (hρ : SourceAdmissible
      (σ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)) (ρ.tailN k)) :
    (rawInterpret (piLimit E ℓ) (CtxCat.extendTele Γ₁ Δ hΔ) (e.wkN k)).app _ σ.op ρ =
      (rawInterpret (piLimit E ℓ) Γ₁ e).app _
        (σ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)).op (ρ.tailN k) := by
  have hx : e.wkN k = e.subst (RawCtx.Hom.teleProjection hΔ).subst := by
    rw [Expr.wkN_eq_subst]
    rfl
  rw [hx]
  exact pe.rename (fun v => ⟨_, rfl⟩) σ
    (.of_var (Fin.castLE Δ.le) (fun _ => rfl) fun v => by
      rw [Var.db_castLE, RawValuation.tailN_apply, Nat.add_sub_cancel_left]) hρ

theorem RawInterpretationProperties.wkN_value {e : Expr ζ ℓ Γ₁.as.len}
    (pe : RawInterpretationProperties Γ₁ e) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (σ : Γ₂ ⟶ CtxCat.extendTele Γ₁ Δ hΔ) (ρ : RawValuation Γ₂)
    (hρ : SourceAdmissible σ ρ) :
    (rawInterpret (piLimit E ℓ) (CtxCat.extendTele Γ₁ Δ hΔ) (e.wkN k)).app _ σ.op ρ =
      (rawInterpret (piLimit E ℓ) Γ₁ e).app _
        (σ ≫ RawCtx.toCtx.map (RawCtx.Hom.teleProjection hΔ)).op (ρ.tailN k) :=
  HasSubstitution.wkN_value pe.subst hΔ σ ρ (by simpa using hρ.tailTele hΔ)

end Metalean.CoherentShape
