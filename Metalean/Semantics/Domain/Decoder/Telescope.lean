/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Domain.Inductive.Fields

@[expose] public section

namespace Metalean.CoherentShape.CodeAssignment

open CategoryTheory Presheaf TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}

noncomputable def telescope (F : CodeAssignment E ℓ) : {n : Nat} → Domain Γ₁ →
    (Fin n → Tm_ Γ₁) → (Fin n → Domain Γ₁) →
    (Fin n → Domain Γ₁) × Domain Γ₁
  | 0, T, _, _ => ⟨Fin.elim0, T⟩
  | _ + 1, T, names, args =>
    let X := F.extend (ctorTypeDomIdeal T) (names 0) (args 0)
    let rest := F.telescope (ctorTypeFibreIdeal T (names 0) X) (Fin.tail names) (Fin.tail args)
    ⟨Fin.cons X rest.1, rest.2⟩

theorem telescope_mono (F : CodeAssignment E ℓ) {n : Nat} {T T' : Domain Γ₁}
    (names : Fin n → Tm_ Γ₁) {args args' : Fin n → Domain Γ₁}
    (hT : T ≤ T') (hargs : ∀ i, args i ≤ args' i) :
    F.telescope T names args ≤ F.telescope T' names args' := by
  induction n generalizing T T' with
  | zero => exact ⟨fun i => i.elim0, hT⟩
  | succ n ih =>
    have hx : F.extend (ctorTypeDomIdeal T) (names 0) (args 0) ≤
        F.extend (ctorTypeDomIdeal T') (names 0) (args' 0) :=
      F.extend_mono (ctorTypeDomIdeal_mono hT) (hargs 0)
    have hrest := ih (Fin.tail names)
      (ctorTypeFibreIdeal_mono hT (names 0) hx) fun i => hargs i.succ
    exact ⟨Fin.cases hx hrest.1, hrest.2⟩

theorem pullback_telescope (F : CodeAssignment E ℓ) {n : Nat} (T : Domain Γ₁)
    (names : Fin n → Tm_ Γ₁) (args : Fin n → Domain Γ₁) (σ : Γ₂ ⟶ Γ₁) :
    (fun i => ((F.telescope T names args).1 i).pullback σ,
      (F.telescope T names args).2.pullback σ) =
      F.telescope (T.pullback σ) (fun j => (Tm E ℓ).map σ.op (names j))
        fun j => (args j).pullback σ := by
  induction n generalizing T with
  | zero => exact Prod.ext (funext fun i => i.elim0) rfl
  | succ n ih =>
    have hrest := ih
      (ctorTypeFibreIdeal T (names 0) (F.extend (ctorTypeDomIdeal T) (names 0) (args 0)))
      (Fin.tail names) (Fin.tail args)
    rw [pullback_ctorTypeFibreIdeal, F.pullback_extend, pullback_ctorTypeDomIdeal] at hrest
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (F.pullback_extend _ _ _ σ).trans
          (congrArg (fun A => F.extend A _ _) (pullback_ctorTypeDomIdeal T σ))
      · exact congrArg (fun result : (Fin n → Domain Γ₂) × Domain Γ₂ => result.1 j) hrest
    · exact congrArg (fun result : (Fin n → Domain Γ₂) × Domain Γ₂ => result.2) hrest

theorem telescope_idempotent {F : CodeAssignment E ℓ} (hF : F.IsIdempotent) {n : Nat}
    (T : Domain Γ₁) (names : Fin n → Tm_ Γ₁) (args : Fin n → Domain Γ₁) :
    F.telescope T names (F.telescope T names args).1 = F.telescope T names args := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih =>
    simp [telescope, extend_idempotent hF, ih]

theorem telescope_finitary (F : CodeAssignment E ℓ) {n : Nat}
    (names : Fin n → Tm_ Γ₁)
    (T : Domain Γ₁ → Domain Γ₁) (args : Fin n → Domain Γ₁ → Domain Γ₁)
    (hT : ΩIdeal.IsFinitary T) (hargs : ∀ i, ΩIdeal.IsFinitary (args i))
    (hmT : Monotone T) (hmargs : ∀ i, Monotone (args i)) :
    (∀ i, ΩIdeal.IsFinitary fun X => (F.telescope (T X) names fun j => args j X).1 i) ∧
      ΩIdeal.IsFinitary fun X => (F.telescope (T X) names fun j => args j X).2 := by
  induction n generalizing T with
  | zero => exact ⟨fun i => i.elim0, hT⟩
  | succ n ih =>
    let first := fun X => F.extend (ctorTypeDomIdeal (T X)) (names 0) (args 0 X)
    have hmfirst : Monotone first := fun _ _ h =>
      F.extend_mono (ctorTypeDomIdeal_mono (hmT h)) (hmargs 0 h)
    have hfirst : ΩIdeal.IsFinitary first := ΩIdeal.IsFinitary.comp₂
      (fun _ _ h => F.extend_mono h.1 h.2)
      (F.extend_finitary_left (names 0)) (fun A => F.extend_finitary_right A (names 0))
      (ctorTypeDomIdeal_finitary.comp hT fun _ _ h => ctorTypeDomIdeal_mono h)
      (hargs 0) (fun _ _ h => ctorTypeDomIdeal_mono (hmT h)) (hmargs 0)
    have hrest : ΩIdeal.IsFinitary fun X => ctorTypeFibreIdeal (T X) (names 0) (first X) :=
      ΩIdeal.IsFinitary.comp₂
        (fun _ _ h => ctorTypeFibreIdeal_mono h.1 _ h.2)
        (ctorTypeFibreIdeal_finitary_left (names 0))
        (fun A => ctorTypeFibreIdeal_finitary_right A (names 0))
        hT hfirst hmT hmfirst
    have hresult := ih (Fin.tail names) _ (Fin.tail args) hrest
      (fun i => hargs i.succ) (fun _ _ h => ctorTypeFibreIdeal_mono (hmT h) _ (hmfirst h))
      fun i => hmargs i.succ
    exact ⟨Fin.cases hfirst hresult.1, hresult.2⟩

theorem telescope_snoc (F : CodeAssignment E ℓ) {n : Nat} (T : Domain Γ₁)
    (names : Fin (n + 1) → Tm_ Γ₁) (args : Fin (n + 1) → Domain Γ₁) :
    F.telescope T names args =
      let result := F.telescope T (fun i => names i.castSucc) fun i => args i.castSucc
      let X := F.extend (ctorTypeDomIdeal result.2) (names (Fin.last n)) (args (Fin.last n))
      (Fin.snoc result.1 X, ctorTypeFibreIdeal result.2 (names (Fin.last n)) X) := by
  induction n generalizing T with
  | zero =>
    apply Prod.ext
    · funext i
      obtain rfl := Fin.eq_zero i
      rfl
    · rfl
  | succ n ih =>
    rw [telescope, ih]
    simp [telescope, Fin.tail, Fin.cons_snoc_eq_snoc_cons]
    exact ⟨⟨rfl, rfl⟩, rfl⟩

variable {F G : CodeAssignment E ℓ} {n : Nat}

theorem telescope_eq_of_rank
    (h : ∀ {Γ₂ : CtxCat E ℓ} (a : CoherentShape Γ₂), a.1.rank < n → F.app _ a = G.app _ a)
    {k : Nat} (T : Domain Γ₁) (hT : T.CofinalIn (·.1.rank < n))
    (names : Fin k → Tm_ Γ₁) (args : Fin k → Domain Γ₁) :
    F.telescope T names args = G.telescope T names args := by
  induction k generalizing T with
  | zero => rfl
  | succ k ih =>
    simp only [telescope]
    rw [extend_eq_of h hT.domain, ih _ (hT.fibre _ _) (Fin.tail names) (Fin.tail args)]

end Metalean.CoherentShape.CodeAssignment
