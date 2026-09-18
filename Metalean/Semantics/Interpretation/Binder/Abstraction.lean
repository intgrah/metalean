/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation.Binder.Basic

@[expose] public section

namespace Metalean.CoherentShape.RawFamily

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ ΓA : CtxCat E ℓ}
  (D : CodeAssignment E ℓ)

noncomputable def abstraction (hA : Comprehension (Ty E ℓ) Γ₁ ΓA)
    (C : RawFamily Γ₁) (B : RawFamily ΓA) : RawFamily Γ₁ :=
  (RawActionFamily.normalizedBody D hA C B).comp (.ofNatTrans (RawAction.abstractionHom E ℓ))

@[simp]
theorem abstraction_value (hA : Comprehension (Ty E ℓ) Γ₁ ΓA)
    (C : RawFamily Γ₁) (B : RawFamily ΓA)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    (abstraction D hA C B).app _ σ.op ρ =
      (normalizedBodyAction D hA C B σ ρ).abstraction := rfl

theorem abstraction_mono (hA : Comprehension (Ty E ℓ) Γ₁ ΓA)
    {C C' : RawFamily Γ₁} (hC : C ≤ C') {B B' : RawFamily ΓA} (hB : B ≤ B') :
    abstraction D hA C B ≤ abstraction D hA C' B' :=
  fun _ σ ρ => RawAction.abstraction_mono (normalizedBodyAction_mono D hA hC hB σ.unop ρ)

theorem IsFinitary.abstraction (hA : Comprehension (Ty E ℓ) Γ₁ ΓA)
    {C : RawFamily Γ₁} (hC : C.IsFinitary)
    {B : RawFamily ΓA} (hB : B.IsFinitary) :
    (abstraction D hA C B).IsFinitary := by
  intro Γ₂ σ i ρ
  apply ΩLower.IsFinitary.of_eventually
  intro I y ⟨f, hf, hyf⟩
  filter_upwards
    [RawActionFamily.IsFinitary.graph_eventually
      (RawActionFamily.IsFinitary.normalizedBody D hA hC hB) σ i ρ I f hf]
    with J hf
  exact ⟨f, hf, hyf⟩

theorem abstraction_iSup_le (hA : Comprehension (Ty E ℓ) Γ₁ ΓA) (C : RawFamily Γ₁)
    {B : Nat → RawFamily ΓA} (hB : Monotone B) :
    abstraction D hA C (⨆ n, B n) ≤ ⨆ n, abstraction D hA C (B n) := by
  intro X σ₁ ρ Γ₃ σ₂ q hq
  have hq' : ((normalizedBodyAction D hA C (⨆ n, B n) σ₁.unop ρ).abstraction).mem σ₂ q := hq
  have ⟨f, hf, hqf⟩ := hq'
  have hmem : ∀ i, ∃ n,
      (((normalizedBodyAction D hA C (B n) σ₁.unop ρ).onBasis).app _
        (σ₂.op, f.1.names i) (f.input i)).mem (𝟙 Γ₃) (f.output i) := by
    intro i
    have h : (sectionValue hA (⨆ n, B n) (σ₂ ≫ σ₁.unop) (ρ.pullback σ₂) (f.1.names i)
        (D.rawExtend (C.app _ (σ₂ ≫ σ₁.unop).op (ρ.pullback σ₂)) (f.1.names i)
          (ΩLower.principal (pointedOrder E ℓ) (f.input i)))).mem (𝟙 Γ₃) (f.output i) := hf i
    exact (ΩLower.mem_iSup_of_nonempty ..).mp
      (sectionValue_iSup_le hA B (σ₂ ≫ σ₁.unop) (ρ.pullback σ₂)
        (f.1.names i) _ (𝟙 Γ₃) (f.output i) h)
  choose m hm using hmem
  have hn : ((normalizedBodyAction D hA C (B (Finset.univ.sup m)) σ₁.unop ρ).onBasis).GraphValid σ₂ f :=
    fun i => normalizedBodyAction_mono D hA le_rfl (hB (Finset.le_sup (Finset.mem_univ i)))
      σ₁.unop ρ _ (σ₂.op, f.1.names i) _ (𝟙 Γ₃) _ (hm i)
  change ((⨆ n, abstraction D hA C (B n)).app X σ₁ ρ).mem σ₂ q
  rw [iSup_app]
  exact (ΩLower.mem_iSup_of_nonempty ..).mpr ⟨_, ⟨f, hn, hqf⟩⟩

end Metalean.CoherentShape.RawFamily
