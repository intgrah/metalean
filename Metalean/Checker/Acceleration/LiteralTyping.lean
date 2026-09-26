/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Acceleration.Literal
public import Metalean.Typing.Defs

@[expose] public section

namespace Metalean.Expr

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
  {η : Head ζ (.inductive Nat.sig)}

theorem natTypeIndexDF (is : Fin 0 → Expr ζ ℓ n) :
    E[Γ] ⊢ (.ind η 0 ![] ![] is : Expr ζ ℓ n) ≡ .ind η 0 ![] ![] is :
      .sort (E.get η).block.level{(![] : Param 0 → Level ℓ)} :=
  .indDF nofun nofun

theorem nat_typed :
    E[Γ] ⊢ (Expr.nat η : Expr ζ ℓ n) ≡ Expr.nat η :
      .sort (E.get η).block.level{(![] : Param 0 → Level ℓ)} :=
  natTypeIndexDF ![]

theorem zero_typed :
    E[Γ] ⊢ (Expr.zero η : Expr ζ ℓ n) : Expr.nat η := by
  have h := @Defeq.ctorDF ζ E ℓ n Γ Nat.sig η 0 0 ![] ![] ![] ![] ![] ![] ![] ![] ![]
    nofun nofun nofun nofun nofun (natTypeIndexDF _)
  rwa [Fin.emptyFun (((E.get η).block.ctors 0 0).targetIndex ![] ![] ![]) ![]] at h

theorem succ_congr {e₁ e₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ e₁ ≡ e₂ : Expr.nat η →
    E[Γ] ⊢ Expr.succ η e₁ ≡ Expr.succ η e₂ : Expr.nat η := by
  intro he
  have hty : ∀ f : Fin (Nat.sig.ctors 0 1).nrecFields,
      (((E.get η).block.ctors 0 1).recursive f).instantiatedType η ![] ![] (Fin.append ![] ![]) =
        (Expr.nat η : Expr ζ ℓ n) := fun ⟨0, _⟩ => by
    simp [RecField.instantiatedType, RecField.instantiatedTelescope, Matrix.empty_eq, Expr.nat]
  have h := @Defeq.ctorDF ζ E ℓ n Γ Nat.sig η 0 1 ![] ![] ![] ![] ![] ![e₁] ![e₂] ![]
      ![(E.get η).block.level{(![] : Param 0 → Level ℓ)}]
    nofun nofun
    (fun ⟨0, _⟩ => by rw [hty]; exact he)
    nofun
    (fun ⟨0, _⟩ => by
      change E[Γ] ⊢ (((E.get η).block.ctors 0 1).recursive ⟨0, _⟩).instantiatedType η ![] ![]
          (Fin.append ![] ![]) : _
      rw [hty]
      exact Expr.nat_typed)
    (natTypeIndexDF _)
  rwa [Fin.emptyFun (((E.get η).block.ctors 0 1).targetIndex ![] ![] ![]) ![]] at h

theorem natLit_typed (η : Head ζ (.inductive Nat.sig)) (num : Nat) :
    E[Γ] ⊢ (natLit η num : Expr ζ ℓ n) : Expr.nat η := by
  induction num with
  | zero => exact Expr.zero_typed
  | succ num ih => exact Expr.succ_congr ih

end Metalean.Expr
