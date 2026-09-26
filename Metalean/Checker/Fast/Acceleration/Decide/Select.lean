/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Decide.Inductive.DecideEqNat
public import Metalean.Checker.Fast.Acceleration.Decide.Inductive.EqBool
public import Metalean.Checker.Fast.Acceleration.Decide.Inductive.Le
public import Metalean.Checker.Fast.Acceleration.Decide.Structure

@[expose] public section

namespace Metalean.Checker.Fast.Decide

open Frontend (Failure Table)

variable (F : FEnv) (hints : Array Export.Hints)

def verifyDecLe (D : LeConsts) (t : Table) (ble : BoolOp F Nat.ble) :
    EIO Failure (PLift (DecLe F D)) :=
  tryCatch (Inductive.verifyDecLe F hints D t ble) fun _ =>
    Structure.verifyDecLe F hints D t ble

def verifyDecEqNat (D : EqNatConsts) (t : Table) (beq : BoolOp F Nat.beq) :
    EIO Failure (PLift (DecEqNat F D)) :=
  tryCatch (Inductive.verifyDecEqNat F hints D t beq) fun _ =>
    Structure.verifyDecEqNat F hints D t beq

def verifyDecEqBool (D : EqBoolConsts) (t : Table) : EIO Failure (PLift (DecEqBool F D)) :=
  tryCatch (Inductive.verifyDecEqBool F hints D t) fun _ =>
    Structure.verifyDecEqBool F hints D t

def verifyDecideEqNat (D : DecideConsts) (t : Table) (beq : BoolOp F Nat.beq) :
    EIO Failure (PLift (DecideEqNat F D)) :=
  tryCatch (Inductive.verifyDecideEqNat F hints D t beq) fun _ =>
    Structure.verifyDecideEqNat F hints D t beq

end Metalean.Checker.Fast.Decide
