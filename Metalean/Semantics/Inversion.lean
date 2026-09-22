/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Interpretation
import Metalean.Typing.Env
import Metalean.Semantics.Soundness

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Δ : Ctx ζ ℓ 0 n}

open CategoryTheory CoherentShape CodeAssignment Presheaf

theorem Defeq.ind_model_inv (ho : E.Ordered) {ι : IndSig}
    {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {ls₁ ls₂ : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n} {is₁ is₂ : Fin (ι.nindices s) → Expr ζ ℓ n}
    {X : Expr ζ ℓ n} :
    E[Δ] ⊢ ok →
    E[Δ] ⊢ .ind η s ls₁ ps₁ is₁ ≡ .ind η s ls₂ ps₂ is₂ : X →
    ls₁ = ls₂ ∧
      (∀ p, ∃ t : Expr ζ ℓ n, E[Δ] ⊢ ps₁ p ≡ ps₂ p : t) ∧
      ∀ i, ∃ t : Expr ζ ℓ n, E[Δ] ⊢ is₁ i ≡ is₂ i : t := by
  intro hΔ h
  have hB := (ho.entryWF η).block
  have hI₁ := IndTyping.ofTyping (Γ₁ := ⟨Δ, hΔ⟩) hB h.left
  have hI₂ := IndTyping.ofTyping (Γ₁ := ⟨Δ, hΔ⟩) hB h.right
  have heq := (h.rawSoundness ho hΔ).equal (𝟙 _) (fun _ ↦ ⊥) (hΔ.bottom_admissible ho (𝟙 _))
  rw [rawInterpret_ind_typed _ hI₁ hB, rawInterpret_ind_typed _ hI₂ hB] at heq
  have hcode := RawValue.code_eq_of_ind_eq heq
  simp [IndTyping.code] at hcode
  exact ⟨hcode.1,
    fun p => ⟨_, (Quotient.exact (congrFun hcode.2.1 p)).2⟩,
    fun i => ⟨_, (Quotient.exact (congrFun hcode.2.2 i)).2⟩⟩

theorem TypeEq.rawInterpret_eq (ho : E.Ordered) (hΔ : E[Δ] ⊢ ok)
    {t t' : Expr ζ ℓ n} :
    E[Δ] ⊢ t ≡ t' typ →
    (rawInterpret (piLimit E ℓ) (⟨Δ, hΔ⟩ : CtxCat E ℓ) t).app _ (𝟙 _).op (fun _ ↦ ⊥) =
      (rawInterpret (piLimit E ℓ) (⟨Δ, hΔ⟩ : CtxCat E ℓ) t').app _ (𝟙 _).op fun _ ↦ ⊥ := by
  intro h
  induction h using Relation.TransGen.trans_induction_on with
  | single h =>
    have ⟨_, h⟩ := h
    exact (h.rawSoundness ho hΔ).equal (𝟙 _) (fun _ ↦ ⊥)
      (hΔ.bottom_admissible ho (𝟙 _))
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem TypeEq.sort_model_inj (ho : E.Ordered) (hΔ : E[Δ] ⊢ ok) {l₁ l₂ : Level ℓ}
    (h : E[Δ] ⊢ .sort l₁ ≡ .sort l₂ typ) : l₁ = l₂ := by
  have heq := h.rawInterpret_eq ho hΔ
  rw [rawInterpret_sort, rawInterpret_sort, RawFamily.sort_value, RawFamily.sort_value] at heq
  have hmem : (principalIdeal (sortAtom l₂ : CoherentShape (⟨Δ, hΔ⟩ : CtxCat E ℓ))).mem
      (𝟙 _) (sortAtom l₁) := by
    rw [← ΩIdeal.val_mem, ← heq]
    exact (ΩLower.mem_principal_id _ _).mpr le_rfl
  exact sortAtom_le_iff.mp hmem

theorem TypeEq.forallE_model_inj (ho : E.Ordered)
    {t₁ t₂ : Expr ζ ℓ n} {t₁' t₂' : Expr ζ ℓ (n + 1)} :
    E[Δ] ⊢ ok →
    E[Δ] ⊢ .forallE t₁ t₁' ≡ .forallE t₂ t₂' typ →
    E[Δ] ⊢ t₁ ≡ t₂ typ ∧ E[Δ.snoc t₁] ⊢ t₁' ≡ t₂' typ ∧ E[Δ.snoc t₂] ⊢ t₁' ≡ t₂' typ := by
  intro hΔ h
  have ⟨_, hl⟩ := h.left
  have ⟨_, hr⟩ := h.right
  have ⟨⟨_, ht₁⟩, ⟨_, ht₁'⟩⟩ := hl.forallE_inv
  have ⟨⟨_, ht₂⟩, ⟨_, ht₂'⟩⟩ := hr.forallE_inv
  have hp : ((rawInterpret (piLimit E ℓ) (⟨Δ, hΔ⟩ : CtxCat E ℓ) (.forallE t₁ t₁')).app _ (𝟙 _).op
      fun _ ↦ ⊥).mem (𝟙 _) (piAtom (Ty.pairOfTyping (⟨Δ, hΔ⟩ : CtxCat E ℓ).as ht₁ ht₁')) := by
    rw [rawInterpret_forallE _ ht₁ ht₁', RawFamily.mem_piAtom_pi_value_iff]
    simp
  rw [h.rawInterpret_eq ho hΔ, rawInterpret_forallE _ ht₂ ht₂',
    RawFamily.mem_piAtom_pi_value_iff] at hp
  simp at hp
  exact (Ty.pairOfTyping_eq_iff _ ht₁ ht₁' ht₂ ht₂').mp hp

theorem TypeEq.quot_model_inj (ho : E.Ordered)
    {η : Head ζ .quot} {u u' : Level ℓ} {α α' r r' : Expr ζ ℓ n} :
    E[Δ] ⊢ ok →
    E[Δ] ⊢ .quot η u α r ≡ .quot η u' α' r' typ →
    u = u' ∧ E[Δ] ⊢ α ≡ α' : .sort u ∧ E[Δ] ⊢ r ≡ r' : Quot.relType α := by
  intro hΔ h
  have ⟨_, hl⟩ := h.left
  have ⟨_, hr⟩ := h.right
  have h₁ := QuotTyping.ofTyping ⟨Δ, hΔ⟩ hl
  have h₂ := QuotTyping.ofTyping ⟨Δ, hΔ⟩ hr
  have heq := h.rawInterpret_eq ho hΔ
  rw [rawInterpret_quot _ h₁, rawInterpret_quot _ h₂, RawFamily.quot_value,
    RawFamily.quot_value, QuotCode.map_hom_id, QuotCode.map_hom_id] at heq
  have hcode : h₁.code η = h₂.code η := quotAtom_le_iff.mp (by simpa using heq.le)
  exact ⟨congrArg QuotCode.level hcode, (Quotient.exact (congrArg QuotCode.carrier hcode)).2,
    (Quotient.exact (congrArg QuotCode.relation hcode)).2⟩

end Metalean
