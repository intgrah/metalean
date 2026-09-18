/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Telescope
public import Metalean.Semantics.Interpretation.Binder.Abstraction
public import Metalean.Semantics.Syntax.Rank

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ b : Nat} {P : Level ℓ → Prop}

abbrev CtxCat.extendTele {m : Nat} (Γ : CtxCat E ℓ) (Δ : Ctx ζ ℓ Γ.as.len m)
    (hΔ : WFTeleStrong E P Γ.as.ctx Δ) : CtxCat E ℓ :=
  ⟨Γ.as.ctx ++ Δ, hΔ.appendCtxWFStrong Γ.as.wf⟩

namespace RawFamily

variable (D : CodeAssignment E ℓ)
  (interp : (Γ : CtxCat E ℓ) → (e : Expr ζ ℓ Γ.as.len) → e.headRank < b → RawFamily Γ)

noncomputable def ctxLam (Γ : CtxCat E ℓ) {m : Nat} :
    (Δ : Ctx ζ ℓ Γ.as.len m) → (hΔ : WFTeleStrong E P Γ.as.ctx Δ) → Δ.headRank < b →
      RawFamily (CtxCat.extendTele Γ Δ hΔ) → RawFamily Γ
  | .nil => fun _ _ B => B
  | .snoc Δ t => fun hΔ hb B =>
    ctxLam Γ Δ hΔ.init (lt_of_le_of_lt (le_max_left _ _) hb)
      (abstraction D (CtxCat.rawComprehension hΔ.last.choose_spec.2)
        (interp _ t (lt_of_le_of_lt (le_max_right _ _) hb)) B)

variable {D interp} {Γ : CtxCat E ℓ} {m : Nat} {Δ : Ctx ζ ℓ Γ.as.len m} {hΔ : WFTeleStrong E P Γ.as.ctx Δ}
  {hb : Δ.headRank < b}

theorem ctxLam_mono {B₁ B₂ : RawFamily (CtxCat.extendTele Γ Δ hΔ)} (hB : B₁ ≤ B₂) :
    ctxLam D interp Γ Δ hΔ hb B₁ ≤ ctxLam D interp Γ Δ hΔ hb B₂ := by
  induction Δ with
  | nil => exact hB
  | snoc Δ t ih => exact ih (abstraction_mono D _ le_rfl hB)

theorem IsFinitary.ctxLam (hinterp : ∀ Γ e he, (interp Γ e he).IsFinitary)
    {B : RawFamily (CtxCat.extendTele Γ Δ hΔ)} (hB : B.IsFinitary) :
    (ctxLam D interp Γ Δ hΔ hb B).IsFinitary := by
  induction Δ with
  | nil => exact hB
  | snoc Δ t ih => exact ih (IsFinitary.abstraction D _ (hinterp _ _ _) hB)

theorem ctxLam_iSup_le {B : Nat → RawFamily (CtxCat.extendTele Γ Δ hΔ)} (hB : Monotone B) :
    ctxLam D interp Γ Δ hΔ hb (⨆ n, B n) ≤ ⨆ n, ctxLam D interp Γ Δ hΔ hb (B n) := by
  induction Δ with
  | nil => exact le_rfl
  | snoc Δ t ih =>
    exact (ctxLam_mono (abstraction_iSup_le D _ _ hB)).trans
      (ih fun _ _ hab => abstraction_mono D _ le_rfl (hB hab))

end RawFamily

end Metalean.CoherentShape
