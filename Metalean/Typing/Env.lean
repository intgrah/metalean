/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Eq
public import Metalean.Strong.Defs
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n m : Nat} {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ n m}

namespace Entry

judgement WFStrong (E : Env ζ) : {sig : Sig} → Entry ζ sig → Prop where

  E[.nil] ⊢ₛ t typ
  ──────────────────── «axiom» {ℓ : Nat} {t : Expr ζ ℓ 0}
  WFStrong E (.axiom t)

  E[.nil] ⊢ₛ e : t
  E[.nil] ⊢ₛ t typ
  ──────────────────── «opaque» {ℓ : Nat} {e t : Expr ζ ℓ 0}
  WFStrong E (.opaque t)

  E[.nil] ⊢ₛ t typ
  E[.nil] ⊢ₛ e : t
  ──────────────────── «def» {ℓ : Nat} {e t : Expr ζ ℓ 0}
  WFStrong E (.def t e)

  (E.get η).block = Eq.block
  ──────────────────── quot {η : Head ζ (.inductive Eq.sig)}
  WFStrong E (.quot η)

  I.WFStrong E
  ──────────────────── «inductive» {ι : IndSig} {I : Inductive ζ ι}
  WFStrong E (.inductive I)

end Entry

theorem Expr.falseTy_isType (E : Env ζ) : E[.nil] ⊢ₛ (.falseTy : Expr ζ 0 0) typ :=
  ⟨_, .forallEDF .sortDF (.var .sortDF) (.var .sortDF)⟩

namespace Env

-- TODO rename to WF
-- TODO do the TODO
inductive Ordered : {ζ : Sigs} → Env ζ → Prop
  | nil : Ordered .nil
  | snoc {ζ : Sigs} {sig : Sig} {E : Env ζ} {entry : Entry ζ sig} :
      Ordered E → Entry.WFStrong E entry → Ordered (.snoc E entry)

theorem Ordered.ofPrefix {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
    (pre : Prefix E₁ E₂) (ho : E₂.Ordered) : E₁.Ordered := by
  induction pre with
  | refl => exact ho
  | step _ ih =>
    have .snoc ho _ := ho
    exact ih ho

/--
It is not the case that every closed type has a closed inhabitant
This is for a particular environment.
This effectively means you cannot enter new things into the environment like
inductive types, or axioms or definitions.
However definitions are admissible because of let bindings/inlining.
-/
def Con (E : Env ζ) : Prop :=
  ¬∀ t : Expr ζ 0 0, E[.nil] ⊢ₛ t typ → ∃ e, E[.nil] ⊢ₛ e : t

end Env

end Metalean
