/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Operations
import Metalean.Typing.Map
import Metalean.Typing.Context

@[expose] public section

namespace Metalean.Checker.Fast

open Acceleration

variable {ζ : Sigs} {F : FEnv} {E : Env ζ} 

theorem FEnv.Denotes.pushInv {F F₀ : FEnv} {fe : FEntry} {ζ : Sigs} {E : Env ζ}
    (h : FEnv.Denotes F E) (heq : F = F₀.push fe) :
    ∃ (ζ₀ : Sigs) (E₀ : Env ζ₀) (_ : Env.Prefix E₀ E), FEnv.Denotes F₀ E₀ := by
  induction h with
  | nil => exact absurd (congrArg PArray.size heq) (by simp)
  | @snoc F₁ ζ₁ E₁ fe₁ entry h₁ _ _ =>
    have hfes : F₁ = F₀ := (PArray.push_inj heq).1
    exact ⟨ζ₁, E₁, .step .refl, hfes ▸ h₁⟩

theorem FEnv.Denotes.restrict {F : FEnv} {ζ₀ : Sigs} {E₀ : Env ζ₀} {E : Env ζ}
    (hF₀ : FEnv.Denotes F E₀) (pre : Env.Prefix E₀ E) {pos : Nat} (hpos : pos < F.size)
    {sig : Sig} {η : Head ζ sig} (hη : ζ.lookup pos = some ⟨sig, η⟩) :
    ∃ η₀ : Head ζ₀ sig, ζ₀.lookup pos = some ⟨sig, η₀⟩ ∧ η₀.map pre.sigs = η := by
  have ⟨η₀, hη₀, _⟩ := hF₀.get (getElem?_pos F pos hpos)
  cases hη.symm.trans (Sigs.lookup_map pre.sigs hη₀)
  exact ⟨η₀, hη₀, rfl⟩

theorem FEnv.lt_size_of_getElem? {F : FEnv} {pos : Nat} {fe : FEntry} (h : F[pos]? = some fe) :
    pos < F.size :=
  PArray.lt_size_of_getElem? h

theorem FEnv.getElem?_push_of_getElem? {F : FEnv} {pos : Nat} {fe fe₀ : FEntry}
    (h : F[pos]? = some fe₀) :
    (F.push fe)[pos]? = some fe₀ := by
  simp [PArray.getElem?_push, Nat.ne_of_lt (FEnv.lt_size_of_getElem? h), h]

theorem NatOpSpec.push {nat pos : Nat} {f : Nat → Nat → Nat} (h : NatOpSpec F nat pos f)
    (fe : FEntry) :
    NatOpSpec (F.push fe) nat pos f where
  natSig :=
    have ⟨I, hI⟩ := h.natSig
    ⟨I, FEnv.getElem?_push_of_getElem? hI⟩
  opDef :=
    have ⟨t, v, hop⟩ := h.opDef
    ⟨t, v, FEnv.getElem?_push_of_getElem? hop⟩
  eq := fun hF hE hη hηOp => by
    have ⟨ζ₀, E₀, pre, hF₀⟩ := hF.pushInv rfl
    have ⟨_, hI⟩ := h.natSig
    have ⟨_, _, hop⟩ := h.opDef
    have ⟨ηNat₀, hnat₀, hnat⟩ := hF₀.restrict pre (FEnv.lt_size_of_getElem? hI) hη
    have ⟨ηOp₀, hop₀, hop⟩ := hF₀.restrict pre (FEnv.lt_size_of_getElem? hop) hηOp
    subst hnat hop
    exact (h.eq hF₀ (EnvWF.comap pre hE) hnat₀ hop₀).map pre

theorem BoolOpSpec.push {nat bool pos : Nat} {f : Nat → Nat → Bool}
    (h : BoolOpSpec F nat bool pos f) (fe : FEntry) :
    BoolOpSpec (F.push fe) nat bool pos f where
  natSig :=
    have ⟨I, hI⟩ := h.natSig
    ⟨I, FEnv.getElem?_push_of_getElem? hI⟩
  boolSig :=
    have ⟨I, hI⟩ := h.boolSig
    ⟨I, FEnv.getElem?_push_of_getElem? hI⟩
  opDef :=
    have ⟨t, v, hop⟩ := h.opDef
    ⟨t, v, FEnv.getElem?_push_of_getElem? hop⟩
  eq := fun hF hE hη hηBool hηOp => by
    have ⟨ζ₀, E₀, pre, hF₀⟩ := hF.pushInv rfl
    have ⟨_, hI⟩ := h.natSig
    have ⟨_, hIBool⟩ := h.boolSig
    have ⟨_, _, hop⟩ := h.opDef
    have ⟨ηNat₀, hnat₀, hnat⟩ := hF₀.restrict pre (FEnv.lt_size_of_getElem? hI) hη
    have ⟨ηBool₀, hbool₀, hbool⟩ := hF₀.restrict pre (FEnv.lt_size_of_getElem? hIBool) hηBool
    have ⟨ηOp₀, hop₀, hop⟩ := hF₀.restrict pre (FEnv.lt_size_of_getElem? hop) hηOp
    subst hnat hbool hop
    exact (h.eq hF₀ (EnvWF.comap pre hE) hnat₀ hbool₀ hop₀).map pre

def NatOp.push {f : Nat → Nat → Nat} (op : NatOp F f) (fe : FEntry) : NatOp (F.push fe) f :=
  ⟨op.nat, op.pos, op.spec.push fe⟩

def BoolOp.push {f : Nat → Nat → Bool} (op : BoolOp F f) (fe : FEntry) :
    BoolOp (F.push fe) f :=
  ⟨op.nat, op.bool, op.pos, op.spec.push fe⟩

def Accel.push (accel : Accel F) (fe : FEntry) : Accel (F.push fe) where
  Nat_add? := accel.Nat_add?.map (·.push fe)
  Nat_sub? := accel.Nat_sub?.map (·.push fe)
  Nat_mul? := accel.Nat_mul?.map (·.push fe)
  Nat_pow? := accel.Nat_pow?.map (·.push fe)
  Nat_beq? := accel.Nat_beq?.map (·.push fe)
  Nat_ble? := accel.Nat_ble?.map (·.push fe)
  Nat_div? := accel.Nat_div?.map (·.push fe)
  Nat_mod? := accel.Nat_mod?.map (·.push fe)
  Nat_gcd? := accel.Nat_gcd?.map (·.push fe)
  Nat_land? := accel.Nat_land?.map (·.push fe)
  Nat_lor? := accel.Nat_lor?.map (·.push fe)
  Nat_xor? := accel.Nat_xor?.map (·.push fe)
  Nat_shiftLeft? := accel.Nat_shiftLeft?.map (·.push fe)
  Nat_shiftRight? := accel.Nat_shiftRight?.map (·.push fe)

end Metalean.Checker.Fast
