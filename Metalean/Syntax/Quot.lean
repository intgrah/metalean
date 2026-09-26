/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Expr
public import Metalean.Level.Quot.Basic

@[expose] public section

namespace Metalean.Quot

open Relation

variable {ζ ζ₁ ζ₂ : Sigs} {ℓ ℓ' n : Nat}

/-- `α → α → Prop` -/
abbrev relType (α : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .forallE α (.forallE α.wk .prop)

/-- `Eq t e₁ e₂` -/
abbrev eqApp (ηeq : Head ζ (.inductive Eq.sig)) (l : Level ℓ)
    (α e₁ e₂ : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ind ηeq 0 ![l] ![α, e₁] ![e₂]

/--
info: Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (a : ∀ (a b : α), r a b → f a = f b) :
  Quot r → β
-/
#guard_msgs in
#check Quot.lift

/-- `∀ a b : α, r a b → f a = f b` -/
abbrev compatType (ηeq : Head ζ (.inductive Eq.sig)) (l : Level ℓ)
    (α r β f : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .forallE α
    (.forallE α.wk
      (.forallE
        (.appList r.wk.wk [.var (Fin.last n).castSucc, .var (Fin.last (n + 1))])
        (eqApp ηeq l β.wk.wk.wk
          (.app f.wk.wk.wk (.var (Fin.last n).castSucc.castSucc))
          (.app f.wk.wk.wk (.var (Fin.last (n + 1)).castSucc)))))

/--
info: Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (mk : ∀ (a : α), β (Quot.mk r a)) (q : Quot r) : β q
-/
#guard_msgs in
#check Quot.ind

/-- `Quot α r → Prop` -/
abbrev motiveType (η : Head ζ .quot) (l : Level ℓ) (α r : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .forallE (.quot η l α r) .prop

/-- `Quot.mk α r a` -/
abbrev minorQuotMk (η : Head ζ .quot) (l : Level ℓ) (α r : Expr ζ ℓ n) : Expr ζ ℓ (n + 1) :=
  .quotMk η l α.wk r.wk (.var (Fin.last n))

/-- `∀ a : α, β (Quot.mk α r a)` -/
abbrev minorType (η : Head ζ .quot) (l : Level ℓ)
    (α r β : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .forallE α (.app β.wk (minorQuotMk η l α r))

end Metalean.Quot
