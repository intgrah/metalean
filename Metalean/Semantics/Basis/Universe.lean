/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Basis.Join
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean.Shape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ : CtxCat E ℓ}

judgement IsCode : Bool → Shape Γ₁ → Prop where

  Basis.IsBottom a
  ──────────────────── bottom {r : Bool} {a : Shape Γ₁}
  IsCode r a

  ──────────────────── sort {s : Level ℓ}
  IsCode true (.sort s)

  ──────────────────── forallE {label : Ty.Pair Γ₁} {a : Shape Γ₁} {k : Nat} {names : Fin k → Tm_ Γ₁}
    {ins outs : Fin k → Shape Γ₁}
  IsCode true (.forallE label a k names ins outs)

  ∀ i, IsCode false (outs i)
  ──────────────────── forallE_prop {label : Ty.Pair Γ₁} {a : Shape Γ₁} {k : Nat} {names : Fin k → Tm_ Γ₁}
    {ins outs : Fin k → Shape Γ₁}
  IsCode false (.forallE label a k names ins outs)

  code.rel = r
  ──────────────────── ind {r : Bool} (code : IndCode Γ₁)
    {ctorTypes : Fin code.toIndHead.nctors → Shape Γ₁}
  IsCode r (.ind code ctorTypes)

  code.level.rel = r
  ──────────────────── quot {r : Bool} (code : QuotCode Γ₁)
  IsCode r (.quot code)

namespace IsCode

theorem bot {r : Bool} : IsCode r (Shape.bot : Shape Γ₁) := .bottom .bot

theorem eq_true_of_sort {r : Bool} {s : Level ℓ} (h : IsCode r (Shape.sort s : Shape Γ₁)) :
    r = true := by
  cases h with
  | bottom h => nomatch h
  | sort => rfl

theorem of_le {r : Bool} {a b : Shape Γ₁} : a ≤ b → IsCode r b → IsCode r a
  | hab, .bottom h => .bottom (Basis.le_bot_iff.mp (hab.trans h.le))
  | .collapse h, _ => .bottom h
  | .sort _, .sort => .sort
  | .forallE _ _, .forallE => .forallE
  | .forallE _ hf, .forallE_prop hb => .forallE_prop fun i =>
    match hf i with
    | .bottom h => .bottom h
    | .mem j _ _ hout => of_le hout (hb j)
  | .ind _, .ind _ h => .ind _ h
  | .quot _, .quot _ h => .quot _ h

theorem map {r : Bool} {a : Shape Γ₁}
    (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) :
    IsCode r a → IsCode r (a.map arg pi)
  | .bottom h => .bottom (h.map arg pi)
  | .sort => .sort
  | .forallE => .forallE
  | .forallE_prop h => .forallE_prop fun i => map arg pi (h i)
  | .ind _ h => .ind _ h
  | .quot _ h => .quot _ h

theorem cSup {r : Bool} {a b : Shape Γ₁} (ha : IsCode r a) (hb : IsCode r b) : IsCode r (a.cSup b) := by
  fun_induction Shape.cSup a b
  · exact hb
  · exact ha
  · cases ha with | bottom ha =>
      cases hb with | bottom hb =>
        exact .bottom (.lam (Graph.IsBottom.append (Basis.IsBottom.lam_iff.mp ha)
          (Basis.IsBottom.lam_iff.mp hb)))
  · cases ha with
    | bottom h => nomatch h
    | forallE => exact .forallE
    | forallE_prop ha =>
      cases hb with
      | bottom h => nomatch h
      | forallE_prop hb => exact .forallE_prop (Fin.addCases (by simpa [Graph.append] using ha) (by simpa [Graph.append] using hb))
  · cases ha with | bottom h => nomatch h
  · exact Shape.cSupBot_induction ha hb
  · exact hb
  · cases ha with | bottom h => exact absurd h (by assumption)
  · exact Shape.cSupBot_induction ha hb
  · cases ha with
    | bottom h => nomatch h
    | ind _ h => exact .ind _ h
  · exact Shape.cSupBot_induction ha hb
  · cases ha with | bottom h => nomatch h
  · exact Shape.cSupBot_induction ha hb

end IsCode

end Metalean.Shape
