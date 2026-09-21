/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Acceleration.Operations
public import Metalean.FastChecker.CheckLevel

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

/-- 128 MiB -/
def natMaxSize : Nat := 128 * 1024 * 1024

def natScalarBound : Nat := 2 ^ 63

def natSizeInBytes (num : Nat) : Nat :=
  if num < natScalarBound then 8 else (num.log2 + 64) / 64 * 8

def bounded (num : Nat) : Except Failure Unit :=
  if natSizeInBytes num > natMaxSize then throw (.reject .natSize) else pure ()

def Hints.compare : Export.Hints → Export.Hints → Ordering
  | .regular h₁, .regular h₂ => if h₁ = h₂ then .eq else if h₁ > h₂ then .lt else .gt
  | .opaque, .opaque | .abbrev, .abbrev => .eq
  | .opaque, _ => .gt
  | _, .opaque => .lt
  | .abbrev, _ => .lt
  | _, .abbrev => .gt

variable (L : Literals) (F : FEnv) (ℓ : Nat) (hints : Array Export.Hints)
  (accel : Accel L F) (n : Nat)

def accelOp (pos : Nat) : Bool :=
  (pos == L.add && accel.add.isSome) || (pos == L.sub && accel.sub.isSome) ||
    (pos == L.mul && accel.mul.isSome) || (pos == L.pow && accel.pow.isSome) ||
    (pos == L.beq && accel.beq.isSome) || (pos == L.ble && accel.ble.isSome) ||
    (pos == L.div && accel.div.isSome) || (pos == L.mod && accel.mod.isSome) ||
    (pos == L.gcd && accel.gcd.isSome) || (pos == L.land && accel.land.isSome) ||
    (pos == L.lor && accel.lor.isSome) || (pos == L.xor && accel.xor.isSome) ||
    (pos == L.shiftLeft && accel.shiftLeft.isSome) ||
    (pos == L.shiftRight && accel.shiftRight.isSome)

def powBounded (base exponent : Nat) : Except Failure Unit :=
  if exponent ≥ 2 ^ 32 then throw (.reject .natSize)
  else if base > 1 && exponent ≠ 0 && natSizeInBytes base > natMaxSize / exponent then
    throw (.reject .natSize)
  else pure ()

def shiftLeftBounded (base shift : Nat) : Except Failure Unit :=
  if base ≠ 0 && shift > 8 * natMaxSize then throw (.reject .natSize)
  else bounded (base <<< shift)

def foldOp (G : FCtx) (pos : Nat) (ls : Array FLevel) :
    (x y : FExpr) →
    OptionT (Except Failure)
      {fe₂ : FExpr // RedSpec L F ℓ G (.app (.app (.const pos ls) x) y) fe₂}
  | .natLit num₁, .natLit num₂ => guardProof (#[] = ls) >>= fun ⟨rfl⟩ => do
    if hadd : pos = L.add then
      let some ⟨h⟩ := accel.add | failure
      bounded (num₁ + num₂)
      pure ⟨.natLit (num₁ + num₂), by subst hadd; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hsub : pos = L.sub then
      let some ⟨h⟩ := accel.sub | failure
      pure ⟨.natLit (num₁ - num₂), by subst hsub; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hmul : pos = L.mul then
      let some ⟨h⟩ := accel.mul | failure
      bounded (num₁ * num₂)
      pure ⟨.natLit (num₁ * num₂), by subst hmul; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hpow : pos = L.pow then
      let some ⟨h⟩ := accel.pow | failure
      powBounded num₁ num₂
      pure ⟨.natLit (num₁ ^ num₂), by subst hpow; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hbeq : pos = L.beq then
      let some ⟨h⟩ := accel.beq | failure
      pure ⟨FExpr.boolLit L (Nat.beq num₁ num₂), by subst hbeq; exact RedSpec.boolOp num₁ num₂ h⟩
    else if hble : pos = L.ble then
      let some ⟨h⟩ := accel.ble | failure
      pure ⟨FExpr.boolLit L (Nat.ble num₁ num₂), by subst hble; exact RedSpec.boolOp num₁ num₂ h⟩
    else if hdiv : pos = L.div then
      let some ⟨h⟩ := accel.div | failure
      pure ⟨.natLit (num₁ / num₂), by subst hdiv; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hmod : pos = L.mod then
      let some ⟨h⟩ := accel.mod | failure
      pure ⟨.natLit (num₁ % num₂), by subst hmod; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hgcd : pos = L.gcd then
      let some ⟨h⟩ := accel.gcd | failure
      pure ⟨.natLit (Nat.gcd num₁ num₂), by subst hgcd; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hland : pos = L.land then
      let some ⟨h⟩ := accel.land | failure
      pure ⟨.natLit (num₁ &&& num₂), by subst hland; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hlor : pos = L.lor then
      let some ⟨h⟩ := accel.lor | failure
      pure ⟨.natLit (num₁ ||| num₂), by subst hlor; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hxor : pos = L.xor then
      let some ⟨h⟩ := accel.xor | failure
      pure ⟨.natLit (num₁ ^^^ num₂), by subst hxor; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hshl : pos = L.shiftLeft then
      let some ⟨h⟩ := accel.shiftLeft | failure
      shiftLeftBounded num₁ num₂
      pure ⟨.natLit (num₁ <<< num₂), by subst hshl; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else if hshr : pos = L.shiftRight then
      let some ⟨h⟩ := accel.shiftRight | failure
      pure ⟨.natLit (num₁ >>> num₂), by subst hshr; exact RedSpec.natOp₂ num₁ num₂ h⟩
    else failure
  | _, _ => failure

def natLitExt (G : FCtx) (fe₁ : FExpr) :
    Option {num : Nat // RedSpec L F ℓ G fe₁ (.natLit num)} :=
  match fe₁ with
  | .natLit num => some ⟨num, RedSpec.refl _⟩
  | .ctor pos s c ls ps fds recFds =>
    match hfe : F[L.nat]? with
    | some (.inductive ι _) =>
      if hι : ι = Literals.Nat.sig then
        if hzero : FExpr.ctor pos s c ls ps fds recFds = .ctor L.nat 0 0 #[] #[] #[] #[] then
          some ⟨0, by subst hι; rw [hzero]; exact RedSpec.zeroLit hfe⟩
        else none
      else none
    | _ => none
  | _ => none

def succForm (G : FCtx) : (fe₁ : FExpr) → Option {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂}
  | .natLit (num + 1) =>
    let ⟨fe₂, h⟩ := litToCtor L F G.size (.natLit (num + 1))
    if fe₂ matches .ctor .. then some ⟨fe₂, RedSpec.ofRed h⟩ else none
  | .ctor pos 0 1 ls ps fds recFds =>
    if pos = L.nat ∧ recFds.size = 1 then some ⟨.ctor pos 0 1 ls ps fds recFds, RedSpec.refl _⟩
    else none
  | _ => none

def isDelta : FExpr → Option (Nat × Export.Hints)
  | .const pos ls =>
    match F[pos]? with
    | some (.def nlevels _ _) => if ls.size = nlevels then some (pos, hints.getD pos .opaque) else none
    | _ => none
  | .app f _ => isDelta f
  | _ => none

end Metalean.FastChecker
