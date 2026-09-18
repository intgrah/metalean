/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.CategoryTheory.Functor.FunctorHom
public import Metalean.Semantics.Interpretation.Family.Basic

@[expose] public section

namespace Metalean.CoherentShape

open CategoryTheory Opposite TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

abbrev ValuationMap (Γ₁ : CtxCat E ℓ) :=
  Functor.HomObj (RawValuation.presheaf E ℓ) (RawValuation.presheaf E ℓ)
    (coyoneda.obj (op (op Γ₁)))

namespace ValuationMap

noncomputable def ofFin {n : Nat} (args : Fin n → RawFamily Γ₁) : ValuationMap Γ₁ where
  app _ σ₁ := Preord.ofHom {
    toFun ρ := RawValuation.pushFin (fun _ => ⊥) fun i => (args i).app _ σ₁ ρ
    monotone' _ _ hρ := RawValuation.pushFin_mono le_rfl
      fun i => (args i).app _ σ₁ |>.hom.monotone hρ }
  naturality σ₂ σ₁ := Preord.ext fun ρ => by
    change RawValuation.pushFin (fun _ => ⊥)
      (fun i => (args i).app _ (σ₁ ≫ σ₂) (ρ.pullback σ₂.unop)) =
        (RawValuation.pushFin (fun _ => ⊥) fun i => (args i).app _ σ₁ ρ).pullback σ₂.unop
    have hbot : RawValuation.pullback (fun _ => ⊥) σ₂.unop = fun _ => ⊥ :=
      funext fun _ => Presheaf.ΩLower.presheaf_map_bot _
    rw [RawValuation.pullback_pushFin]
    exact congrArg (RawValuation.pushFin fun _ => ⊥)
      (funext fun i => (args i).naturality_apply σ₂ σ₁ ρ)

end ValuationMap

section Substitution

open Presheaf

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

namespace RawValuation

def tailN (ρ : RawValuation Γ₁) : Nat → RawValuation Γ₁
  | 0 => ρ
  | k + 1 => (ρ.tailN k).tail

theorem tailN_succ (ρ : RawValuation Γ₁) (k : Nat) : ρ.tailN (k + 1) = (ρ.tailN k).tail := rfl

theorem tailN_apply (ρ : RawValuation Γ₁) (k j : Nat) : ρ.tailN k j = ρ (j + k) := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    change ρ.tailN k (j + 1) = _
    rw [ih]
    congr 1
    omega

@[simp] theorem tailN_tailN (ρ : RawValuation Γ₁) (k j : Nat) :
    (ρ.tailN k).tailN j = ρ.tailN (k + j) := by
  funext i
  simp [tailN_apply, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem tailN_pushFin (ρ : RawValuation Γ₁) {k : Nat} (args : Fin k → RawValue Γ₁) :
    (ρ.pushFin args).tailN k = ρ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext j
    rw [tailN_apply]
    change (ρ.pushFin fun i => args i.castSucc) (j + k) = ρ j
    simpa [tailN_apply] using congrFun (ih fun i => args i.castSucc) j

@[simp] theorem pushFin_tailN (ρ : RawValuation Γ₁) (k : Nat) :
    (ρ.tailN k).pushFin (fun i : Var k => ρ i.db) = ρ := by
  induction k generalizing ρ with
  | zero => rfl
  | succ k ih =>
    have htail : ρ.tail.tailN k = ρ.tailN (k + 1) :=
      (tailN_tailN ρ 1 k).trans (congrArg ρ.tailN (Nat.add_comm 1 k))
    simp [pushFin, ← htail]
    change ((ρ.tail.tailN k).pushFin fun i : Var k => ρ.tail i.db).push (ρ 0) = ρ
    rw [ih]
    funext i
    cases i <;> rfl

end RawValuation

namespace RawFamily

theorem IsFinitary.head {F : RawFamily Γ₁} (hF : F.IsFinitary)
    (σ : Γ₂ ⟶ Γ₁) (ρ : RawValuation Γ₂) :
    ΩLower.IsFinitary fun I => F.app _ σ.op (ρ.push I) := by
  simpa using hF σ 0 (ρ.push ⊥)

theorem IsFinitary.compose_value {Γ₃ : CtxCat E ℓ} {B : RawFamily Γ₃}
    (hB : B.IsFinitary) {X : RawFamily Γ₁} (hX : X.IsFinitary)
    (σ₁ : Γ₂ ⟶ Γ₁) (σ₃ : Γ₂ ⟶ Γ₃) (i : ℕ) (ρ : RawValuation Γ₂) :
    ΩLower.IsFinitary fun I => B.app _ σ₃.op
      ((ρ.replace i I).push (X.app _ σ₁.op (ρ.replace i I))) :=
  ΩLower.IsFinitary.apply
    (fun J => by simpa using hB σ₃ (i + 1) (ρ.push J))
    (fun J => hB.head σ₃ (ρ.replace i J)) (hX σ₁ i ρ)
    (fun _ _ h J => (B.app _ σ₃.op).hom.monotone
      (RawValuation.push_mono (RawValuation.replace_mono i le_rfl h) fun _ _ hx => hx))
    (fun J _ _ h => (B.app _ σ₃.op).hom.monotone (RawValuation.push_mono le_rfl h))
    ((X.app _ σ₁.op).hom.monotone.comp (Function.update_mono (f := ρ)))

end RawFamily

namespace RawValuation

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ}

theorem pushFin_isFinitary {F : RawValuation Γ₁ → RawValue Γ₁} (hF : Monotone F)
    (hf : ∀ (i : Nat) (ρ : RawValuation Γ₁), ΩLower.IsFinitary fun I => F (ρ.replace i I))
    {k : Nat} {args : Fin k → RawValue Γ₁ → RawValue Γ₁}
    (hm : ∀ i, Monotone (args i)) (ha : ∀ i, ΩLower.IsFinitary (args i))
    (ρ : RawValuation Γ₁) :
    ΩLower.IsFinitary fun I => F (ρ.pushFin fun i => args i I) := by
  induction k generalizing F with
  | zero => exact ΩLower.IsFinitary.const (F ρ)
  | succ k ih =>
    exact ΩLower.IsFinitary.apply
      (fun J => ih (F := fun υ => F (υ.push J))
        (fun _ _ h => hF (push_mono h fun _ _ hx => hx))
        (fun i υ => by simpa using hf (i + 1) (υ.push J))
        (fun i => hm i.castSucc) fun i => ha i.castSucc)
      (fun I => by simpa using hf 0 ((ρ.pushFin fun i => args i.castSucc I).push ⊥))
      (ha (Fin.last k))
      (fun _ _ h J => hF (push_mono (pushFin_mono le_rfl fun i => hm i.castSucc h)
        fun _ _ hx => hx))
      (fun _ _ _ h => hF (push_mono le_rfl h)) (hm (Fin.last k))

end RawValuation

namespace RawFamily

variable {Γ₃ Δ : CtxCat E ℓ}

noncomputable def substitute (F : RawFamily Δ) (s : Γ₁ ⟶ Δ)
    (args : ValuationMap Γ₁) : RawFamily Γ₁ :=
  args.comp (F.pullback s)

theorem IsFinitary.substitute {F : RawFamily Δ} (hF : F.IsFinitary) (s : Γ₁ ⟶ Δ)
    {n : Nat} {args : Fin n → RawFamily Γ₁} (ha : ∀ i, (args i).IsFinitary) :
    (F.substitute s (ValuationMap.ofFin args)).IsFinitary := fun _ σ i ρ =>
  RawValuation.pushFin_isFinitary (F.app _ (σ ≫ s).op).hom.monotone
    (hF (σ ≫ s))
    (fun j => (args j).app _ σ.op |>.hom.monotone.comp (Function.update_mono (f := ρ)))
    (fun j => ha j σ i ρ) _

end RawFamily

end Substitution

end Metalean.CoherentShape
