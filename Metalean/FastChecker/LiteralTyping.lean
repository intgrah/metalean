/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Literal
public import Metalean.Strong.Defs

@[expose] public section

namespace Metalean.FastChecker.Literals

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}
  {η : Head ζ (.inductive Nat.sig)}

theorem natTypeIndexDF (is : Fin 0 → Expr ζ ℓ n) :
    E[Γ] ⊢ₛ (.ind η 0 ![] ![] is : Expr ζ ℓ n) ≡ .ind η 0 ![] ![] is :
      .sort ((E.get η).block.level.inst ![]) :=
  .indDF nofun nofun

theorem natTypeDF :
    E[Γ] ⊢ₛ (natType η : Expr ζ ℓ n) ≡ natType η :
      .sort ((E.get η).block.level.inst ![]) :=
  natTypeIndexDF ![]

theorem natZeroTyped :
    E[Γ] ⊢ₛ (natZero η : Expr ζ ℓ n) : natType η := by
  have h := @DefeqStrong.ctorDF ζ E ℓ n Γ Nat.sig η 0 0 ![] ![] ![] ![] ![] ![] ![] ![] ![]
    nofun nofun nofun nofun nofun (natTypeIndexDF _)
  rwa [Fin.emptyFun (((E.get η).block.ctors 0 0).targetIndex ![] ![] ![]) ![]] at h

theorem natSuccDF {e₁ e₂ : Expr ζ ℓ n} :
    E[Γ] ⊢ₛ e₁ ≡ e₂ : natType η →
    E[Γ] ⊢ₛ natSucc η e₁ ≡ natSucc η e₂ : natType η := by
  intro he
  have hty : ∀ f : Fin (Nat.sig.ctors 0 1).nrecFields,
      (((E.get η).block.ctors 0 1).recursive f).instantiatedType η ![] ![] (Fin.append ![] ![]) =
        (natType η : Expr ζ ℓ n) := fun ⟨0, _⟩ => by
    simp [RecField.instantiatedType, RecField.instantiatedTelescope, Matrix.empty_eq, natType]
  have h := @DefeqStrong.ctorDF ζ E ℓ n Γ Nat.sig η 0 1 ![] ![] ![] ![] ![] ![e₁] ![e₂] ![]
      ![(E.get η).block.level.inst ![]]
    nofun nofun
    (fun ⟨0, _⟩ => by rw [hty]; exact he)
    nofun
    (fun ⟨0, _⟩ => by
      change E[Γ] ⊢ₛ
        (((E.get η).block.ctors 0 1).recursive ⟨0, _⟩).instantiatedType η ![] ![]
          (Fin.append ![] ![]) : _
      rw [hty]
      exact natTypeDF)
    (natTypeIndexDF _)
  rwa [Fin.emptyFun (((E.get η).block.ctors 0 1).targetIndex ![] ![] ![]) ![]] at h

theorem natLit_typed (η : Head ζ (.inductive Nat.sig)) (num : Nat) :
    E[Γ] ⊢ₛ (natLit η num : Expr ζ ℓ n) : natType η := by
  induction num with
  | zero => exact natZeroTyped
  | succ num ih => exact natSuccDF ih

variable (L : Literals)

def NatAxiom (E : Env ζ) (pos : Nat) (f : Nat → Nat → Nat) : Prop :=
  ∀ ⦃ℓ n : Nat⦄ ⦃Γ : Ctx ζ ℓ 0 n⦄ ⦃ηNat : Head ζ (.inductive Nat.sig)⦄ ⦃kind : ConstKind⦄
    ⦃ηOp : Head ζ (.const kind 0)⦄ (num₁ num₂ : Nat),
  ζ.lookup L.nat = some ⟨.inductive Nat.sig, ηNat⟩ →
  ζ.lookup pos = some ⟨.const kind 0, ηOp⟩ →
  E[Γ] ⊢ₛ natOp₂ ηOp (natLit ηNat num₁) (natLit ηNat num₂) ≡
    natLit ηNat (f num₁ num₂) : natType ηNat

structure NatAxioms (E : Env ζ) : Prop where
  div : L.NatAxiom E L.div (· / ·)
  mod : L.NatAxiom E L.mod (· % ·)
  gcd : L.NatAxiom E L.gcd Nat.gcd
  land : L.NatAxiom E L.land (· &&& ·)
  lor : L.NatAxiom E L.lor (· ||| ·)
  xor : L.NatAxiom E L.xor (· ^^^ ·)

def NatTrust (E : Env ζ) : Prop :=
  ∀ ⦃ζ₀ : Sigs⦄ ⦃E₀ : Env ζ₀⦄, Env.Prefix E₀ E → L.NatAxioms E₀

variable {L}

theorem NatTrust.restrict {ζ₀ : Sigs} {E₀ : Env ζ₀} (pre : Env.Prefix E₀ E) :
    L.NatTrust E →
    L.NatTrust E₀ :=
  fun h _ _ pre₀ => h (pre₀.trans pre)

end Metalean.FastChecker.Literals
