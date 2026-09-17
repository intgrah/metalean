/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Control
public import Metalean.Syntax.Ctx

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {ℓ m n a k : Nat}

def liftMap? (ρ : Fin m → Option (Fin n)) : Fin (m + 1) → Option (Fin (n + 1)) :=
  fun v => if h : v.val < m then (ρ ⟨v.val, h⟩).map Fin.castSucc else some (Fin.last n)

namespace Expr

def rename? {m n : Nat} (ρ : Fin m → Option (Fin n)) : Expr ζ ℓ m → Option (Expr ζ ℓ n)
  | .var v => (ρ v).map .var
  | .sort l => some (.sort l)
  | .const η ls => some (.const η ls)
  | .ind η s ls ps is => do
    some (.ind η s ls (← Fin.mapM fun p => (ps p).rename? ρ)
      (← Fin.mapM fun i => (is i).rename? ρ))
  | .ctor η s c ls ps fds recFds => do
    some (.ctor η s c ls (← Fin.mapM fun p => (ps p).rename? ρ)
      (← Fin.mapM fun f => (fds f).rename? ρ)
      (← Fin.mapM fun r => (recFds r).rename? ρ))
  | .recr η s ls l ps ms mins is maj => do
    some (.recr η s ls l (← Fin.mapM fun p => (ps p).rename? ρ)
      (← Fin.mapM fun t => (ms t).rename? ρ)
      (← Fin.mapM fun t => Fin.mapM fun c => (mins t c).rename? ρ)
      (← Fin.mapM fun i => (is i).rename? ρ) (← maj.rename? ρ))
  | .quot η l α r => do some (.quot η l (← α.rename? ρ) (← r.rename? ρ))
  | .quotMk η l α r x => do
    some (.quotMk η l (← α.rename? ρ) (← r.rename? ρ) (← x.rename? ρ))
  | .quotLift η l₁ l₂ α r β f h x => do
    some (.quotLift η l₁ l₂ (← α.rename? ρ) (← r.rename? ρ) (← β.rename? ρ)
      (← f.rename? ρ) (← h.rename? ρ) (← x.rename? ρ))
  | .quotInd η l α r β f x => do
    some (.quotInd η l (← α.rename? ρ) (← r.rename? ρ) (← β.rename? ρ)
      (← f.rename? ρ) (← x.rename? ρ))
  | .app e₁ e₂ => do some (.app (← e₁.rename? ρ) (← e₂.rename? ρ))
  | .lam domain body => do some (.lam (← domain.rename? ρ) (← body.rename? (liftMap? ρ)))
  | .forallE domain body => do
    some (.forallE (← domain.rename? ρ) (← body.rename? (liftMap? ρ)))
  | .letE type value body => do
    some (.letE (← type.rename? ρ) (← value.rename? ρ) (← body.rename? (liftMap? ρ)))

end Expr

namespace Ctx

def permuteMap? (a j : Nat) (πinv : Fin k → Option (Fin k)) (o : Fin k) :
    Fin (a + o.val) → Option (Fin (a + j)) := fun v =>
  if h : v.val < a then some ⟨v.val, by omega⟩
  else do
    let j' ← πinv ⟨v.val - a, by omega⟩
    if h' : j'.val < j then some ⟨a + j'.val, by omega⟩ else none

def permuteAux? {b : Nat} (hb : b = a + k) (π πinv : Fin k → Option (Fin k))
    (Δ : Ctx ζ ℓ a b) : (j : Nat) → j ≤ k → Option (Ctx ζ ℓ a (a + j))
  | 0 => fun _ => some .nil
  | j + 1 => fun hj => do
    let Γ ← permuteAux? hb π πinv Δ j (by omega)
    let o ← π ⟨j, by omega⟩
    let t := Δ.entry (p := a + o.val) (by omega) (by omega)
    let t' ← t.rename? (permuteMap? a j πinv o)
    some (Γ.snoc t')

def permute? {b : Nat} (hb : b = a + k) (π πinv : Fin k → Option (Fin k))
    (Δ : Ctx ζ ℓ a b) : Option (Ctx ζ ℓ a (a + k)) :=
  permuteAux? hb π πinv Δ k (Nat.le_refl k)

end Ctx

end Metalean
