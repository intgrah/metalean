/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Fuel

@[expose] public section

namespace Metalean.Checker.Fast

open FExpr

open Frontend (Failure Table)

namespace Div

structure Consts extends toFuel : Fuel.Consts where
  protected Nat_div_go : Nat

instance : CoeOut Consts Fuel.Consts := ⟨Consts.toFuel⟩

def Consts.resolve (t : Table) : Except Failure Consts := do
  pure { toFuel := ← Fuel.Consts.resolve t, Nat_div_go := ← t.const ``Nat.div.go }

variable (F : FEnv) (C : Consts) (hints : Array Export.Hints)

def fuelRec (pos : Nat) : Fuel.Rec where
  pos := C.Nat_div_go
  entry := op₂ pos
  step := succ C.Nat_
  base _ := zero C.Nat_
  instFVarsCore_entry _ _ _ := by simp [op₂, instFVarsCore]
  instFVarsCore_step _ _ := by simp [succ, instFVarsCore]
  instFVarsCore_base _ _ := by simp [zero, instFVarsCore]

theorem computes (pos : Nat) : (fuelRec C pos).Computes F C HDiv.hDiv where
  step _ _ hF hn a b hb hba := by
    rw [Nat.div_eq_sub_div hb hba]
    exact FEq.succLit hF hn _
  base _ _ hF hn a b h := by
    rw [Nat.div_eq_zero_iff.mpr h]
    exact FEq.zeroLit hF hn

def verify (hd : Decide.DecLe F C) (pos : Nat) (sub : NatOp F Nat.sub) :
    EIO Failure (NatOp F Nat.div) := do
  let ⟨hop⟩ ← constDef F pos
  let ⟨h⟩ ← Fuel.verify F C hints hd (fuelRec C pos) sub (computes F C pos)
  pure ⟨C.Nat_, pos, NatOpSpec.ofFEq h.natSpec hop h.eq⟩

end Div

end Metalean.Checker.Fast
