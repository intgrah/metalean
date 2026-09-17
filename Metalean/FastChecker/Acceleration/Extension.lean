/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Acceleration.Operations
import Metalean.Strong.WeakenEnv
import Metalean.Strong.Context

@[expose] public section

namespace Metalean.FastChecker

variable {ζ : Sigs} {F : FEnv} {E : Env ζ} {L : Literals}

theorem FEnv.Denotes.pushInv {F F₀ : FEnv} {fe : FEntry} {ζ : Sigs} {E : Env ζ}
    (h : FEnv.Denotes L F E) (heq : F = F₀.push fe) :
    ∃ (ζ₀ : Sigs) (E₀ : Env ζ₀) (_ : Env.Prefix E₀ E), FEnv.Denotes L F₀ E₀ := by
  induction h with
  | nil => exact absurd (congrArg Array.size heq) (by simp)
  | @snoc F₁ ζ₁ E₁ fe₁ entry h₁ _ _ =>
    have hfes : F₁ = F₀ := by simpa using congrArg Array.pop heq
    exact ⟨ζ₁, E₁, .step .refl, hfes ▸ h₁⟩

theorem FEnv.Denotes.restrict {F : FEnv} {ζ₀ : Sigs} {E₀ : Env ζ₀} {E : Env ζ}
    (hE₀ : FEnv.Denotes L F E₀) (pre : Env.Prefix E₀ E) {pos : Nat} (hpos : pos < F.size)
    {sig : Sig} {η : Head ζ sig} (hη : ζ.lookup pos = some ⟨sig, η⟩) :
    ∃ η₀ : Head ζ₀ sig, ζ₀.lookup pos = some ⟨sig, η₀⟩ ∧ η₀.map pre.sigs = η := by
  have ⟨η₀, hη₀, _⟩ := hE₀.get (getElem?_pos F pos hpos)
  cases hη.symm.trans (Sigs.lookup_map pre.sigs hη₀)
  exact ⟨η₀, hη₀, rfl⟩

theorem NatOpSpec.push {pos : Nat} {f : Nat → Nat → Nat} (h : NatOpSpec L F pos f)
    (fe : FEntry) :
    NatOpSpec L (F.push fe) pos f where
  natBound := by simpa using Nat.lt_succ_of_lt h.natBound
  opBound := by simpa using Nat.lt_succ_of_lt h.opBound
  eq := fun {_ζ _E ℓ' _n _Γ _ηNat _kind _ηOp} num₁ num₂ hE ho htr hη hηOp => by
    have ⟨ζ₀, E₀, pre, hE₀⟩ := hE.pushInv rfl
    have ⟨ηNat₀, hnat₀, hnat⟩ := hE₀.restrict pre h.natBound hη
    have ⟨ηOp₀, hop₀, hop⟩ := hE₀.restrict pre h.opBound hηOp
    have hres := (h.eq (ℓ' := ℓ') (Γ := Ctx.nil) num₁ num₂ hE₀ (Env.Ordered.ofPrefix pre ho)
      (htr.restrict pre) hnat₀ hop₀).envMono pre
    simp only [Literals.natOp₂_map, Literals.map_natLit, Literals.natType_map, hnat, hop,
      Tele.map_nil] at hres
    have hwk := hres.wkClosed (Γ := _Γ)
    simp only [Literals.natOp₂_wkClosed, Literals.natLit_wkClosed, Literals.natType_wkClosed] at hwk
    exact hwk

theorem BoolOpSpec.push {pos : Nat} {f : Nat → Nat → Bool} (h : BoolOpSpec L F pos f)
    (fe : FEntry) :
    BoolOpSpec L (F.push fe) pos f where
  natBound := by simpa using Nat.lt_succ_of_lt h.natBound
  boolBound := by simpa using Nat.lt_succ_of_lt h.boolBound
  boolSig :=
    have ⟨I, hI⟩ := h.boolSig
    ⟨I, by simp [Array.getElem?_push, Nat.ne_of_lt h.boolBound, hI]⟩
  opBound := by simpa using Nat.lt_succ_of_lt h.opBound
  eq := fun {_ζ _E ℓ' _n _Γ _ηNat _ηBool _kind _ηOp} num₁ num₂ hE ho htr hη hηBool hηOp => by
    have ⟨ζ₀, E₀, pre, hE₀⟩ := hE.pushInv rfl
    have ⟨ηNat₀, hnat₀, hnat⟩ := hE₀.restrict pre h.natBound hη
    have ⟨ηBool₀, hbool₀, hbool⟩ := hE₀.restrict pre h.boolBound hηBool
    have ⟨ηOp₀, hop₀, hop⟩ := hE₀.restrict pre h.opBound hηOp
    have hres := (h.eq (ℓ' := ℓ') (Γ := Ctx.nil) num₁ num₂ hE₀ (Env.Ordered.ofPrefix pre ho)
      (htr.restrict pre) hnat₀ hbool₀ hop₀).envMono pre
    simp only [Literals.natOp₂_map, Literals.map_natLit, Literals.boolLit_map,
      Literals.boolType_map, hnat, hbool, hop, Tele.map_nil] at hres
    have hwk := hres.wkClosed (Γ := _Γ)
    simp only [Literals.natOp₂_wkClosed, Literals.natLit_wkClosed, Literals.boolLit_wkClosed,
      Literals.boolType_wkClosed] at hwk
    exact hwk

def Accel.push (accel : Accel L F) (fe : FEntry) : Accel L (F.push fe) where
  add := accel.add.map fun ⟨h⟩ => ⟨h.push fe⟩
  sub := accel.sub.map fun ⟨h⟩ => ⟨h.push fe⟩
  mul := accel.mul.map fun ⟨h⟩ => ⟨h.push fe⟩
  pow := accel.pow.map fun ⟨h⟩ => ⟨h.push fe⟩
  beq := accel.beq.map fun ⟨h⟩ => ⟨h.push fe⟩
  ble := accel.ble.map fun ⟨h⟩ => ⟨h.push fe⟩
  div := accel.div.map fun ⟨h⟩ => ⟨h.push fe⟩
  mod := accel.mod.map fun ⟨h⟩ => ⟨h.push fe⟩
  gcd := accel.gcd.map fun ⟨h⟩ => ⟨h.push fe⟩
  land := accel.land.map fun ⟨h⟩ => ⟨h.push fe⟩
  lor := accel.lor.map fun ⟨h⟩ => ⟨h.push fe⟩
  xor := accel.xor.map fun ⟨h⟩ => ⟨h.push fe⟩
  shiftLeft := accel.shiftLeft.map fun ⟨h⟩ => ⟨h.push fe⟩
  shiftRight := accel.shiftRight.map fun ⟨h⟩ => ⟨h.push fe⟩

end Metalean.FastChecker
