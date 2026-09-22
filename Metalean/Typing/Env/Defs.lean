/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Eq
public import Metalean.Typing.Defs
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n m : Nat} {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ n m}

judgement EntryWF (E : Env ζ) : {sig : Sig} → Entry ζ sig → Prop where

  E[.nil] ⊢ t typ
  ──────────────────── «axiom» {ℓ : Nat} {t : Expr ζ ℓ 0}
  EntryWF E (.axiom t)

  E[.nil] ⊢ e : t
  E[.nil] ⊢ t typ
  ──────────────────── «opaque» {ℓ : Nat} {e t : Expr ζ ℓ 0}
  EntryWF E (.opaque t)

  E[.nil] ⊢ t typ
  E[.nil] ⊢ e : t
  ──────────────────── «def» {ℓ : Nat} {e t : Expr ζ ℓ 0}
  EntryWF E (.def t e)

  (E.get η).block = Eq.block
  ──────────────────── quot {η : Head ζ (.inductive Eq.sig)}
  EntryWF E (.quot η)

  InductiveWF E I
  ──────────────────── «inductive» {ι : IndSig} {I : Inductive ζ ι}
  EntryWF E (.inductive I)

theorem Expr.falseTy_isType (E : Env ζ) : E[.nil] ⊢ (.falseTy : Expr ζ 0 0) typ :=
  ⟨_, .forallEDF .sortDF (.var .sortDF) (.var .sortDF)⟩

inductive EnvWF : {ζ : Sigs} → Env ζ → Prop
  | nil :
    EnvWF .nil
  | snoc {ζ : Sigs} {sig : Sig} {E : Env ζ} {entry : Entry ζ sig} :
    EnvWF E →
    EntryWF E entry →
    EnvWF (.snoc E entry)

theorem EnvWF.comap {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
    (pre : E₁.Prefix E₂) :
    EnvWF E₂ →
    EnvWF E₁ := by
  intro hE
  induction pre with
  | refl => exact hE
  | step _ ih => have .snoc hE _ := hE; exact ih hE

/--
It is not the case that every closed type has a closed inhabitant
This is for a particular environment.
This effectively means you cannot enter new things into the environment like
inductive types, or axioms or definitions.
However definitions are admissible because of let bindings/inlining.
-/
def Env.Con (E : Env ζ) : Prop :=
  ¬∀ t : Expr ζ 0 0, E[.nil] ⊢ t typ → ∃ e, E[.nil] ⊢ e : t

end Metalean
