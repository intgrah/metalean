/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Soundness.Context.Transport
public import Metalean.Semantics.Soundness.Rules.Function
public import Metalean.TypeTheory.Syntactic.Telescope
import Metalean.Semantics.Soundness.Rules.Core

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory CodeAssignment

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Src Tgt Γ₁ Γ₂ : CtxCat E ℓ}
  {k : Nat} {P : Level ℓ → Prop} {Δ : Ctx ζ ℓ Γ₁.as.len (Γ₁.as.len + k)}

theorem SemanticHom.extendTele {m k : Nat} {Δ : Ctx ζ ℓ Γ₁.as.len m}
    (hk : Γ₁.as.len + k = m) (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ)
    (pΔ : RawTeleProperties E Γ₁.as.ctx Δ)
    (σ : Γ₂.as ⟶ (CtxCat.extendTele Γ₁ Δ hΔ).as)
    (hσ : SemanticHom (σ ≫ RawCtx.Hom.teleProjection hΔ))
    (pσ : ∀ i : Fin k, RawInterpretationProperties Γ₂ (σ.subst ((Fin.natAdd Γ₁.as.len i).cast hk)))
    (fσ : ∀ i : Fin k, HasFixedness Γ₂ (σ.subst ((Fin.natAdd Γ₁.as.len i).cast hk))
      ((Ctx.get ((Fin.natAdd Γ₁.as.len i).cast hk) (Γ₁.as.ctx ++ Δ)).subst σ.subst)) :
    SemanticHom σ := by
  subst m
  simp only [Fin.cast_refl, id_eq] at pσ fσ
  exact {
    image v := Fin.addCases (fun v => hσ.image v) (fun i => (pσ i).subst) v
    admissible _ τ ρ hρ := by
      have ⟨ρ₁, hs, ha⟩ := hσ.admissible τ ρ hρ
      exact ⟨_, pΔ.extend_admissible Δ rfl hΔ σ pσ fσ τ ρ₁ ρ hs ha hρ⟩ }

theorem SemanticHom.liftTele {σ : Tgt.as ⟶ Src.as} (h : SemanticHom σ)
    {k : Nat} {P : Level ℓ → Prop} {Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)}
    (hΔ : WFTeleStrong E P Src.as.ctx Δ) (pΔ : RawTeleProperties E Src.as.ctx Δ) :
    SemanticHom (σ.liftTele hΔ) := by
  induction Δ using Tele.addInduction with
  | nil => exact h
  | snoc k Δ t ih => exact (ih hΔ.init pΔ.init).lift hΔ.last.choose_spec.2 (pΔ.last _)

theorem SemanticHom.tele {σ : Tgt.as ⟶ Src.as} (h : SemanticHom σ)
    {k : Nat} {P : Level ℓ → Prop} {Δ : Ctx ζ ℓ Src.as.len (Src.as.len + k)}
    (hΔ : WFTeleStrong E P Src.as.ctx Δ) (pΔ : RawTeleProperties E Src.as.ctx Δ) :
    RawTeleProperties E Tgt.as.ctx (Ctx.substN σ.subst k Δ) := by
  induction Δ using Tele.addInduction with
  | nil => exact .nil
  | snoc k Δ t ih =>
    exact .snoc (ih hΔ.init pΔ.init) fun _ => (h.liftTele hΔ.init pΔ.init).props (pΔ.last _)

theorem RawInterpretationProperties.pi {m : Nat} {P : Level ℓ → Prop} {v : Level ℓ}
    (Δ : Ctx ζ ℓ Src.as.len m) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (body : Expr ζ ℓ m)
    (hbody : E[Src.as.ctx ++ Δ] ⊢ₛ body : .sort v)
    (pbody : RawInterpretationProperties (CtxCat.extendTele Src Δ hΔ) body) :
    RawInterpretationProperties Src (Ctx.pi body Δ) := by
  induction Δ generalizing v with
  | nil => exact pbody
  | snoc Δ t ih =>
    have ht : E[Src.as.ctx ++ Δ] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    exact ih hΔ.init pΔ.init (.forallE t body) (.forallEDF ht hbody hbody)
      (RawInterpretationProperties.forallE ht hbody (pΔ.last _) pbody)

theorem HasFixedness.pi_prop {m : Nat} {P : Level ℓ → Prop}
    (Δ : Ctx ζ ℓ Src.as.len m) (hΔ : WFTeleStrong E P Src.as.ctx Δ)
    (pΔ : RawTeleProperties E Src.as.ctx Δ) (body : Expr ζ ℓ m)
    (hbody : E[Src.as.ctx ++ Δ] ⊢ₛ body : .prop)
    (pbody : HasFixedness (CtxCat.extendTele Src Δ hΔ) body .prop) :
    HasFixedness Src (Ctx.pi body Δ) .prop := by
  induction Δ with
  | nil => exact pbody
  | snoc Δ t ih =>
    have ht : E[Src.as.ctx ++ Δ] ⊢ₛ t : .sort hΔ.last.choose := hΔ.last.choose_spec.2
    have hp : HasFixedness (CtxCat.extendTele Src Δ hΔ.init) (.forallE t body)
        (.sort (.imax hΔ.last.choose .zero)) :=
      HasFixedness.forallE ht hbody (pΔ.last _).ideal pbody
    have hty := DefeqStrong.forallEDF ht hbody hbody
    rw [Level.imax_zero] at hp hty
    exact ih hΔ.init pΔ.init (.forallE t body) hty hp

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
    have hcoords : ρ.tail.tailN k = ρ.tailN (k + 1) :=
      (RawValuation.tailN_tailN ρ 1 k).trans (congrArg ρ.tailN (Nat.add_comm 1 k))
    erw [hcoords, Category.assoc] at htail
    exact htail

theorem SemanticHom.teleProjection {m : Nat} {Δ : Ctx ζ ℓ Γ₁.as.len m}
    (hΔ : WFTeleStrong E P Γ₁.as.ctx Δ) : SemanticHom (RawCtx.Hom.teleProjection hΔ) where
  image v := HasSubstitution.var (CtxCat.extendTele Γ₁ Δ hΔ) (v.castLE Δ.le)
  admissible _ σ ρ hρ := ⟨ρ.tailN (m - Γ₁.as.len),
    .ren (fun v => ⟨_, rfl⟩) (.of_var (Fin.castLE Δ.le) (fun _ => rfl) fun v => by
      rw [Var.db_castLE, RawValuation.tailN_apply]), hρ.tailTele hΔ⟩

end Metalean.CoherentShape
