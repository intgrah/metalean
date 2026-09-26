/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Operations
public import Metalean.Checker.Fast.CheckLevel

@[expose] public section

namespace Metalean.Checker.Fast

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

variable (F : FEnv) (ℓ : Nat) (hints : Array Export.Hints)
  (accel : Accel F) (n : Nat)

def accelOp (pos : Nat) : Bool :=
  let nat {f : Nat → Nat → Nat} (op? : Option (NatOp F f)) := op?.any (·.pos == pos)
  let bool {f : Nat → Nat → Bool} (op? : Option (BoolOp F f)) := op?.any (·.pos == pos)
  nat accel.Nat_add? || nat accel.Nat_sub? || nat accel.Nat_mul? || nat accel.Nat_pow? ||
    bool accel.Nat_beq? || bool accel.Nat_ble? || nat accel.Nat_div? || nat accel.Nat_mod? ||
    nat accel.Nat_gcd? || nat accel.Nat_land? || nat accel.Nat_lor? || nat accel.Nat_xor? ||
    nat accel.Nat_shiftLeft? || nat accel.Nat_shiftRight?

def isBoolTrue : FExpr → Bool
  | .ctor b 0 1 #[] #[] #[] #[] =>
    match F[b]? with
    | some (.inductive ι _) => decide (ι = Bool.sig)
    | _ => false
  | _ => false

def powBounded (base exponent : Nat) : Except Failure Unit :=
  if exponent ≥ 2 ^ 32 then throw (.reject .natSize)
  else if base > 1 && exponent ≠ 0 && natSizeInBytes base > natMaxSize / exponent then
    throw (.reject .natSize)
  else pure ()

def shiftLeftBounded (base shift : Nat) : Except Failure Unit :=
  if base ≠ 0 && shift > 8 * natMaxSize then throw (.reject .natSize)
  else bounded (base <<< shift)

def natOpAt {f : Nat → Nat → Nat} (G : FCtx) (pos nat₁ num₁ nat₂ num₂ : Nat) :
    Option (NatOp F f) →
    Option (PLift (RedSpec F ℓ G
      (.appList (.const pos #[]) [.natLit nat₁ num₁, .natLit nat₂ num₂])
      (.natLit nat₁ (f num₁ num₂))))
  | some ⟨nat, pos', h⟩ =>
    if hp : pos = pos' ∧ nat₁ = nat ∧ nat₂ = nat then
      some ⟨by obtain ⟨rfl, rfl, rfl⟩ := hp; exact RedSpec.natOp num₁ num₂ h⟩
    else none
  | none => none

def boolOpAt {f : Nat → Nat → Bool} (G : FCtx) (pos nat₁ num₁ nat₂ num₂ : Nat) :
    Option (BoolOp F f) →
    Option ((bool : Nat) × PLift (RedSpec F ℓ G
      (.appList (.const pos #[]) [.natLit nat₁ num₁, .natLit nat₂ num₂])
      (FExpr.boolLit bool (f num₁ num₂))))
  | some ⟨nat, bool, pos', h⟩ =>
    if hp : pos = pos' ∧ nat₁ = nat ∧ nat₂ = nat then
      some ⟨bool, ⟨by obtain ⟨rfl, rfl, rfl⟩ := hp; exact RedSpec.boolOp num₁ num₂ h⟩⟩
    else none
  | none => none

def foldOp (G : FCtx) (pos : Nat) (ls : Array FLevel) :
    (x y : FExpr) →
    OptionT (Except Failure)
      {fe₂ : FExpr // RedSpec F ℓ G (.appList (.const pos ls) [x, y]) fe₂}
  | .natLit nat₁ num₁, .natLit nat₂ num₂ => guardProof (#[] = ls) >>= fun ⟨rfl⟩ => do
    let natOp {f : Nat → Nat → Nat} (op? : Option (NatOp F f)) :=
      natOpAt F ℓ (f := f) G pos nat₁ num₁ nat₂ num₂ op?
    let boolOp {f : Nat → Nat → Bool} (op? : Option (BoolOp F f)) :=
      boolOpAt F ℓ (f := f) G pos nat₁ num₁ nat₂ num₂ op?
    if let some ⟨h⟩ := natOp accel.Nat_add? then
      bounded (Nat.add num₁ num₂)
      return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_sub? then return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_mul? then
      bounded (Nat.mul num₁ num₂)
      return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_pow? then
      powBounded num₁ num₂
      return ⟨_, h⟩
    if let some ⟨_, h⟩ := boolOp accel.Nat_beq? then return ⟨_, h.down⟩
    if let some ⟨_, h⟩ := boolOp accel.Nat_ble? then return ⟨_, h.down⟩
    if let some ⟨h⟩ := natOp accel.Nat_div? then return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_mod? then return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_gcd? then return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_land? then return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_lor? then return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_xor? then return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_shiftLeft? then
      shiftLeftBounded num₁ num₂
      return ⟨_, h⟩
    if let some ⟨h⟩ := natOp accel.Nat_shiftRight? then return ⟨_, h⟩
    failure
  | _, _ => failure

def natLitExt (G : FCtx) (fe₁ : FExpr) :
    Option ((nat num : Nat) × PLift (RedSpec F ℓ G fe₁ (.natLit nat num))) :=
  match fe₁ with
  | .natLit nat num => some ⟨nat, num, ⟨RedSpec.refl _⟩⟩
  | .ctor pos s c ls ps fds recFds =>
    if hzero : FExpr.ctor pos s c ls ps fds recFds = .ctor pos 0 0 #[] #[] #[] #[] then
      match hfe : F[pos]? with
      | some (.inductive ι _) =>
        if hι : ι = Nat.sig then
          some ⟨pos, 0, ⟨by subst hι; rw [hzero]; exact RedSpec.zeroLit hfe⟩⟩
        else none
      | _ => none
    else none
  | _ => none

def isNat (pos : Nat) : Bool :=
  match F[pos]? with
  | some (.inductive ι _) => decide (ι = Nat.sig)
  | _ => false

def succForm (G : FCtx) : (fe₁ : FExpr) → Option {fe₂ : FExpr // RedSpec F ℓ G fe₁ fe₂}
  | .natLit nat (num + 1) =>
    let ⟨fe₂, h⟩ := litToCtor F G.size (.natLit nat (num + 1))
    some ⟨fe₂, RedSpec.ofRed h⟩
  | .ctor pos 0 1 ls ps fds recFds =>
    if isNat F pos ∧ recFds.size = 1 then
      some ⟨.ctor pos 0 1 ls ps fds recFds, RedSpec.refl _⟩
    else none
  | _ => none

def isDelta : FExpr → Option (Nat × Export.Hints)
  | .const pos ls =>
    match F[pos]? with
    | some (.def nlevels _ _) => if ls.size = nlevels then some (pos, hints.getD pos .opaque) else none
    | _ => none
  | .app f _ => isDelta f
  | _ => none

end Metalean.Checker.Fast
