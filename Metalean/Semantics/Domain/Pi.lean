/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Domain.Action

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

def BasisAction.pi (label : Ty.Pair Γ₁) (A : ΩLower (pointedOrder E ℓ) Γ₁)
    (B : BasisAction Γ₁) : ΩLower (pointedOrder E ℓ) Γ₁ where
  mem σ q := ∃ (a : CoherentShape _) (f : CoherentGraph _),
    A.mem σ a ∧ B.GraphValid σ f ∧ q ≤ piGenerator ((Ty.pairPresheaf E ℓ).map σ.op label) a f
  natural σ₁ σ₂ q := fun ⟨a, f, ha, hf, hqf⟩ =>
    ⟨reindex σ₂ a, f.reindex σ₂, A.natural σ₁ σ₂ a ha, hf.reindex σ₂, by
      simp
      exact Le.reindex σ₂ hqf⟩
  bottom σ := ⟨⊥, CoherentGraph.nil _, A.bottom σ, fun i => i.elim0, bot_le⟩
  lower _ hqr := fun ⟨a, f, ha, hf, hrf⟩ => ⟨a, f, ha, hf, hqr.trans hrf⟩

@[simp] theorem BasisAction.mem_pi {Γ₁ Γ₂ : CtxCat E ℓ} (label : Ty.Pair Γ₂)
    (A : ΩLower (pointedOrder E ℓ) Γ₂) (B : BasisAction Γ₂) (σ : Γ₁ ⟶ Γ₂)
    (q : CoherentShape Γ₁) :
    (BasisAction.pi label A B).mem σ q ↔
      ∃ (a : CoherentShape Γ₁) (f : CoherentGraph Γ₁),
        A.mem σ a ∧ B.GraphValid σ f ∧ q ≤ piGenerator ((Ty.pairPresheaf E ℓ).map σ.op label) a f :=
  Iff.rfl

theorem BasisAction.pullback_pi (label : Ty.Pair Γ₁) (A : ΩLower (pointedOrder E ℓ) Γ₁)
    (B : BasisAction Γ₁) (σ₁ : Γ₂ ⟶ Γ₁) :
    (BasisAction.pi label A B).pullback σ₁ =
      BasisAction.pi ((Ty.pairPresheaf E ℓ).map σ₁.op label) (A.pullback σ₁)
        ((BasisAction.presheaf E ℓ).map σ₁.op B) := by
  ext Γ₃ σ₂ q
  change _ ↔ ∃ (a : CoherentShape Γ₃) (f : CoherentGraph Γ₃),
    A.mem (σ₂ ≫ σ₁) a ∧ B.GraphValid (σ₂ ≫ σ₁) f ∧
      q ≤ piGenerator ((Ty.pairPresheaf E ℓ).map σ₂.op ((Ty.pairPresheaf E ℓ).map σ₁.op label)) a f
  simp

@[simp]
theorem BasisAction.mem_piAtom_pi_iff (label : Ty.Pair Γ₁)
    (A : ΩLower (pointedOrder E ℓ) Γ₁) (B : BasisAction Γ₁) (σ : Γ₂ ⟶ Γ₁)
    (label' : Ty.Pair Γ₂) :
    (BasisAction.pi label A B).mem σ (piAtom label') ↔ label' = (Ty.pairPresheaf E ℓ).map σ.op label := by
  constructor
  · intro ⟨a, f, _, _, hle⟩
    exact (Basis.Le.forallE_inv hle).1
  · intro rfl
    exact ⟨⊥, CoherentGraph.nil Γ₂, A.bottom σ, fun i => i.elim0, le_rfl⟩

theorem BasisAction.pi_isDirected (label : Ty.Pair Γ₁) (A : ΩLower (pointedOrder E ℓ) Γ₁)
    (B : BasisAction Γ₁) (hA : A.IsDirected) (hB : B.IsIdealValued) :
    (BasisAction.pi label A B).IsDirected := by
  intro Γ₂ σ q r ⟨a, f, ha, hf, hqf⟩ ⟨b, g, hb, hg, hrg⟩
  have ⟨c, hc, hac, hbc⟩ := hA σ ha hb
  have hfg := hf.internallyCompatible hB hg
  exact ⟨piGenerator ((Ty.pairPresheaf E ℓ).map σ.op label) c (f.append g hfg),
    ⟨c, f.append g hfg, hc, hf.append hg hfg, le_rfl⟩,
    hqf.trans (Basis.Le.forallE hac (Graph.Le.append_left f.1 g.1)),
    hrg.trans (Basis.Le.forallE hbc (Graph.Le.append_right f.1 g.1))⟩

noncomputable def pi (label : Ty.Pair Γ₁) (A : Domain Γ₁) (B : IdealAction Γ₁) : Domain Γ₁ :=
  (BasisAction.pi label A.val B.onBasis).toIdeal
    (BasisAction.pi_isDirected label A.val B.onBasis A.property B.onBasis_isIdealValued)

theorem pullback_pi (label : Ty.Pair Γ₁) (A : Domain Γ₁) (B : IdealAction Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (pi label A B).pullback σ =
      pi ((Ty.pairPresheaf E ℓ).map σ.op label) (A.pullback σ) (B.pullback σ) :=
  Subtype.val_injective (BasisAction.pullback_pi label A.val B.onBasis σ)

@[simp]
theorem mem_piAtom_pi_iff (label : Ty.Pair Γ₁) (A : Domain Γ₁) (B : IdealAction Γ₁)
    (σ : Γ₂ ⟶ Γ₁) (label' : Ty.Pair Γ₂) :
    (pi label A B).mem σ (piAtom label') ↔ label' = (Ty.pairPresheaf E ℓ).map σ.op label :=
  BasisAction.mem_piAtom_pi_iff label A.val B.onBasis σ label'

end Metalean.CoherentShape
