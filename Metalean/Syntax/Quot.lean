/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Expr
public import Metalean.Level.Basic

@[expose] public section

namespace Metalean.Quot

open Relation

variable {ζ ζ₁ ζ₂ : Sigs} {ℓ ℓ' n : Nat}

/-- `α → α → Prop` -/
def relType (α : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .forallE α (.forallE α.wk .prop)

/-- `Eq t e₁ e₂` -/
def eqApp (ηeq : Head ζ (.inductive Eq.sig)) (l : Level ℓ)
    (α e₁ e₂ : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .ind ηeq ⟨0, by decide⟩ (fun _ => l)
    (fun i => if i.val = 0 then α else e₁)
    fun _ => e₂

/--
info: Quot.lift.{u, v} {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β) (a : ∀ (a b : α), r a b → f a = f b) :
  Quot r → β
-/
#guard_msgs in
#check Quot.lift

/-- `∀ a b : α, r a b → f a = f b` -/
def compatType (ηeq : Head ζ (.inductive Eq.sig)) (l : Level ℓ)
    (α r β f : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .forallE α
    (.forallE α.wk
      (.forallE
        (r.wk.wk.app (.var ⟨n, by omega⟩) |>.app (.var ⟨n + 1, by omega⟩))
        (eqApp ηeq l β.wk.wk.wk
          (.app f.wk.wk.wk (.var ⟨n, by omega⟩))
          (.app f.wk.wk.wk (.var ⟨n + 1, by omega⟩)))))

/--
info: Quot.ind.{u} {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop} (mk : ∀ (a : α), β (Quot.mk r a)) (q : Quot r) : β q
-/
#guard_msgs in
#check Quot.ind

/-- `Quot α r → Prop` -/
def motiveType (η : Head ζ .quot) (l : Level ℓ) (α r : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .forallE (.quot η l α r) .prop

/-- `Quot.mk α r a` -/
def minorQuotMk (η : Head ζ .quot) (l : Level ℓ) (α r : Expr ζ ℓ n) : Expr ζ ℓ (n + 1) :=
  .quotMk η l α.wk r.wk (.var (Fin.last n))

/-- `∀ a : α, β (Quot.mk α r a)` -/
def minorType (η : Head ζ .quot) (l : Level ℓ)
    (α r β : Expr ζ ℓ n) : Expr ζ ℓ n :=
  .forallE α (.app β.wk (minorQuotMk η l α r))

@[simp] theorem relType_map (pre : ζ₁ ⟶ ζ₂)
    (α : Expr ζ₁ ℓ n) :
    (relType α).map pre = relType (α.map pre) := by
  simp [relType, Expr.map]

@[simp] theorem eqApp_map (pre : ζ₁ ⟶ ζ₂)
    (eqHead : Head ζ₁ (.inductive Eq.sig)) (l : Level ℓ)
    (α e₁ e₂ : Expr ζ₁ ℓ n) :
    (eqApp eqHead l α e₁ e₂).map pre =
      eqApp (eqHead.map pre) l (α.map pre)
        (e₁.map pre) (e₂.map pre) := by
  simp! [eqApp]
  funext i
  split <;> rfl

@[simp] theorem compatType_map (pre : ζ₁ ⟶ ζ₂)
    (eqHead : Head ζ₁ (.inductive Eq.sig)) (l : Level ℓ)
    (α r β f : Expr ζ₁ ℓ n) :
    (compatType eqHead l α r β f).map pre =
      compatType (eqHead.map pre) l (α.map pre)
        (r.map pre) (β.map pre) (f.map pre) := by
  simp! [compatType]

@[simp] theorem motiveType_map (pre : ζ₁ ⟶ ζ₂)
    (η : Head ζ₁ .quot) (l : Level ℓ) (α r : Expr ζ₁ ℓ n) :
    (motiveType η l α r).map pre =
      motiveType (η.map pre) l (α.map pre)
        (r.map pre) := by
  simp! [motiveType]

@[simp] theorem minorQuotMk_map (pre : ζ₁ ⟶ ζ₂)
    (η : Head ζ₁ .quot) (l : Level ℓ) (α r : Expr ζ₁ ℓ n) :
    (minorQuotMk η l α r).map pre =
      minorQuotMk (η.map pre) l (α.map pre)
        (r.map pre) := by
  simp! [minorQuotMk]

@[simp] theorem minorType_map (pre : ζ₁ ⟶ ζ₂)
    (η : Head ζ₁ .quot) (l : Level ℓ) (α r β : Expr ζ₁ ℓ n) :
    (minorType η l α r β).map pre =
      minorType (η.map pre) l (α.map pre)
        (r.map pre) (β.map pre) := by
  simp! [minorType]

@[simp] theorem relType_instL (α : Expr ζ ℓ n) (levelSubst : Param ℓ → Level ℓ') :
    (relType α).instL levelSubst = relType (α.instL levelSubst) := by
  simp! [relType]

@[simp] theorem eqApp_instL (eqHead : Head ζ (.inductive Eq.sig))
    (l : Level ℓ) (α e₁ e₂ : Expr ζ ℓ n) (levelSubst : Param ℓ → Level ℓ') :
    (eqApp eqHead l α e₁ e₂).instL levelSubst =
      eqApp eqHead (l.inst levelSubst) (α.instL levelSubst) (e₁.instL levelSubst)
        (e₂.instL levelSubst) := by
  simp! [eqApp]
  funext i
  split <;> rfl

@[simp] theorem compatType_instL (eqHead : Head ζ (.inductive Eq.sig))
    (l : Level ℓ) (α r β f : Expr ζ ℓ n) (levelSubst : Param ℓ → Level ℓ') :
    (compatType eqHead l α r β f).instL levelSubst =
      compatType eqHead (l.inst levelSubst) (α.instL levelSubst) (r.instL levelSubst)
        (β.instL levelSubst) (f.instL levelSubst) := by
  simp! [compatType]

@[simp] theorem motiveType_instL (η : Head ζ .quot) (l : Level ℓ)
    (α r : Expr ζ ℓ n) (levelSubst : Param ℓ → Level ℓ') :
    (motiveType η l α r).instL levelSubst =
      motiveType η (l.inst levelSubst) (α.instL levelSubst) (r.instL levelSubst) := by
  simp! [motiveType]

@[simp] theorem minorQuotMk_instL (η : Head ζ .quot) (l : Level ℓ)
    (α r : Expr ζ ℓ n) (levelSubst : Param ℓ → Level ℓ') :
    (minorQuotMk η l α r).instL levelSubst =
      minorQuotMk η (l.inst levelSubst) (α.instL levelSubst) (r.instL levelSubst) := by
  simp! [minorQuotMk]

@[simp] theorem minorType_instL (η : Head ζ .quot) (l : Level ℓ)
    (α r β : Expr ζ ℓ n) (levelSubst : Param ℓ → Level ℓ') :
    (minorType η l α r β).instL levelSubst =
      minorType η (l.inst levelSubst) (α.instL levelSubst) (r.instL levelSubst) (β.instL levelSubst) := by
  simp! [minorType]

end Metalean.Quot
