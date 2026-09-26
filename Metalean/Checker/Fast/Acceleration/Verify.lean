/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Add
public import Metalean.Checker.Fast.Acceleration.Sub
public import Metalean.Checker.Fast.Acceleration.Mul
public import Metalean.Checker.Fast.Acceleration.Pow
public import Metalean.Checker.Fast.Acceleration.ShiftLeft
public import Metalean.Checker.Fast.Acceleration.ShiftRight
public import Metalean.Checker.Fast.Acceleration.Beq
public import Metalean.Checker.Fast.Acceleration.Ble
public import Metalean.Checker.Fast.Acceleration.Div
public import Metalean.Checker.Fast.Acceleration.Mod
public import Metalean.Checker.Fast.Acceleration.Gcd
public import Metalean.Checker.Fast.Acceleration.Bitwise
public import Metalean.Checker.Fast.Acceleration.Decide.Select

@[expose] public section

namespace Metalean.Checker.Fast

open Frontend (Failure Table)

open Lean (Name)

variable (F : FEnv) (hints : Array Export.Hints) (table : Table)

def warnUnverified (name : Name) (f : Failure) : EIO Failure Unit :=
  EIO.adapt (fun _ => .internal) <| IO.eprintln
    s!"warning: {name}: is not verifiable ({repr f})"

def need {α : Type} : Option α → Except Failure α
  | some a => pure a
  | none => throw .internal

def bitwiseDecide (C : Bitwise.Consts) (beq : BoolOp F Nat.beq) :
    EIO Failure (PLift (Decide.DecEqNat F C ∧ Decide.DecEqBool F C ∧
      Decide.DecideEqNat F C)) := do
  let ⟨hd⟩ ← Decide.verifyDecEqNat F hints C table beq
  let ⟨hdb⟩ ← Decide.verifyDecEqBool F hints C table
  let ⟨hde⟩ ← Decide.verifyDecideEqNat F hints C table beq
  pure ⟨hd, hdb, hde⟩

def bitwiseDeps (accel : Accel F) :
    Except Failure (BoolOp F Nat.beq × NatOp F Nat.mod × NatOp F Nat.div ×
      NatOp F Nat.add) :=
  need do pure (← accel.Nat_beq?, ← accel.Nat_mod?, ← accel.Nat_div?, ← accel.Nat_add?)

def verifyOp (accel : Accel F) (name : Name) (pos : Nat) : EIO Failure (Accel F) :=
  match name with
  | ``Nat.add => do pure { accel with Nat_add? := some (← verifyAdd F hints table pos) }
  | ``Nat.sub => do pure { accel with Nat_sub? := some (← verifySub F hints table pos) }
  | ``Nat.mul => do
    let add ← need accel.Nat_add?
    pure { accel with Nat_mul? := some (← verifyMul F hints pos add) }
  | ``Nat.pow => do
    let mul ← need accel.Nat_mul?
    pure { accel with Nat_pow? := some (← verifyPow F hints pos mul) }
  | ``Nat.beq => do pure { accel with Nat_beq? := some (← verifyBeq F hints table pos) }
  | ``Nat.ble => do pure { accel with Nat_ble? := some (← verifyBle F hints table pos) }
  | ``Nat.div => do
    let sub ← need accel.Nat_sub?
    let ble ← need accel.Nat_ble?
    let C ← Div.Consts.resolve table
    let ⟨hd⟩ ← Decide.verifyDecLe F hints C table ble
    pure { accel with Nat_div? := some (← Div.verify F C hints hd pos sub) }
  | ``Nat.mod => do
    let sub ← need accel.Nat_sub?
    let ble ← need accel.Nat_ble?
    let C ← Mod.Consts.resolve table
    let ⟨hd⟩ ← Decide.verifyDecLe F hints C table ble
    pure { accel with Nat_mod? := some (← Mod.verify F C hints hd pos sub) }
  | ``Nat.gcd => do
    let beq ← need accel.Nat_beq?
    let mod ← need accel.Nat_mod?
    let C ← Gcd.Consts.resolve table
    let ⟨hd⟩ ← Decide.verifyDecEqNat F hints C table beq
    let ⟨hdb⟩ ← Decide.verifyDecEqBool F hints C table
    pure { accel with Nat_gcd? := some (← Gcd.verify F C hints hd hdb pos beq mod) }
  | ``Nat.land => do
    let (beq, mod, div, add) ← bitwiseDeps F accel
    let C ← Bitwise.LandConsts.resolve table
    let ⟨hd, hdb, hde⟩ ← bitwiseDecide F hints table C.toBitwise beq
    pure { accel with Nat_land? := some (← Bitwise.verifyLand F C hints hd hdb hde pos beq mod div add) }
  | ``Nat.lor => do
    let (beq, mod, div, add) ← bitwiseDeps F accel
    let C ← Bitwise.LorConsts.resolve table
    let ⟨hd, hdb, hde⟩ ← bitwiseDecide F hints table C.toBitwise beq
    pure { accel with Nat_lor? := some (← Bitwise.verifyLor F C hints hd hdb hde pos beq mod div add) }
  | ``Nat.xor => do
    let (beq, mod, div, add) ← bitwiseDeps F accel
    let C ← Bitwise.XorConsts.resolve table
    let ⟨hd, hdb, hde⟩ ← bitwiseDecide F hints table C.toBitwise beq
    pure { accel with Nat_xor? := some (← Bitwise.verifyXor F C hints hd hdb hde pos beq mod div add) }
  | ``Nat.shiftLeft => do
    let mul ← need accel.Nat_mul?
    pure { accel with Nat_shiftLeft? := some (← verifyShiftLeft F hints pos mul) }
  | ``Nat.shiftRight => do
    let div ← need accel.Nat_div?
    pure { accel with Nat_shiftRight? := some (← verifyShiftRight F hints pos div) }
  | _ => pure accel

def verifyAccel (name : Name) (pos : Nat) (accel : Accel F) : EIO Failure (Accel F) :=
  tryCatch (verifyOp F hints table accel name pos) fun f => do
    warnUnverified name f
    pure accel

end Metalean.Checker.Fast
