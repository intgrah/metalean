/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Acceleration.Operations
public import Metalean.Typing.Telescope
import Metalean.Typing.InstLevel

@[expose] public section

namespace Metalean.Checker.Acceleration

variable {ζ : Sigs} (E : Env ζ)

/-- An equation `lhs ≡ rhs : ty` over the well-formed telescope `Γ₀` -/
structure Rule {k : Nat} (Γ₀ : Ctx ζ 0 0 k) (lhs rhs ty : Expr ζ 0 k) : Prop where
  ctx : E[Γ₀] ⊢ ok
  defeq : E[Γ₀] ⊢ lhs ≡ rhs : ty

variable {E} {k m : Nat} {Γ₀ : Ctx ζ 0 0 k} {lhs rhs ty : Expr ζ 0 k}

theorem Rule.inst (h : Rule E Γ₀ lhs rhs ty) {Γ : Ctx ζ 0 0 m} {σ₁ σ₂ : Subst ζ 0 k m} :
    E[Γ] ⊢ σ₁ ≡ σ₂ ⊣ Γ₀ →
    E[Γ] ⊢ lhs.subst σ₁ ≡ rhs.subst σ₂ : ty.subst σ₁ :=
  fun hσ => Defeq.substitution_congr h.ctx hσ h.defeq

syntax "rule_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")?
  (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| rule_simp $[[$ls,*]]? $[$loc]?) => do
    let ls := (ls.map (·.getElems)).getD #[]
    `(tactic| simp [Subst.extend, Subst.lift, Fin.snoc, Expr.wk, Expr.wkFrom, $ls,*] $[$loc]?)

/-- Instantiate a rule at closed arguments, one defeq per telescope entry, in order -/
syntax "rule_have " ident " := " term " using " term,* : tactic

macro_rules
  | `(tactic| rule_have $c := $h using $hs,*) => do
    let hs := hs.getElems
    let hole (s : String) (i : Nat) : Lean.MacroM Lean.Ident :=
      return Lean.mkIdent (← Lean.Macro.addMacroScope (.mkSimple s!"rule_{s}{i}"))
    let holes ← (List.range hs.size).toArray.mapM (hole "arg")
    let mut σ ← `(SubstEq.nil (σ₁ := Fin.elim0) (σ₂ := Fin.elim0))
    for i in List.range hs.size do
      σ ← `(SubstEq.extend (e₁ := ?$(← hole "lhs" i)) (e₂ := ?$(← hole "rhs" i)) ?$(holes[i]!) $σ)
    let mut tac ← `(tactic| have $c := Rule.inst (Γ := #t[]) $h $σ)
    for (x, h') in holes.zip hs do
      tac ← `(tactic| ($tac; case $x:ident =>
        have h := $h'
        simpa [Subst.extend, Subst.lift, Fin.snoc, Expr.wk, Expr.wkFrom] using h))
    `(tactic| ($tac; rule_simp at $c:ident))

end Metalean.Checker.Acceleration
