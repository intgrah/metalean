/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Basis.Coherence

@[expose] public section

namespace Metalean

open CategoryTheory TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ Γ₁ Γ₂ : CtxCat E ℓ}

namespace CtorHead

variable {α β : Type*} (head : CtorHead ζ)

def projectFields (fields : Fin head.arity → α) (project : Fin head.sig.nrecFields → α) :
    Fin head.arity → α :=
  Fin.append (fun f => fields (f.castAdd head.sig.nrecFields))
    fun f => if head.sig.recursiveArity f = 0 then project f
      else fields (Fin.natAdd head.sig.nfields f)

variable {head}

@[simp] theorem projectFields_castAdd (fields : Fin head.arity → α)
    (project : Fin head.sig.nrecFields → α) (f : Fin head.sig.nfields) :
    head.projectFields fields project (f.castAdd head.sig.nrecFields) = fields (f.castAdd _) :=
  Fin.append_left _ _ f

@[simp] theorem projectFields_natAdd (fields : Fin head.arity → α)
    (project : Fin head.sig.nrecFields → α) (f : Fin head.sig.nrecFields) :
    head.projectFields fields project (Fin.natAdd head.sig.nfields f) =
      if head.sig.recursiveArity f = 0 then project f else fields (Fin.natAdd _ f) :=
  Fin.append_right _ _ f

theorem projectFields_rel₂ {R : α → β → Prop} {fields : Fin head.arity → α}
    {fields' : Fin head.arity → β} {project : Fin head.sig.nrecFields → α}
    {project' : Fin head.sig.nrecFields → β}
    (hfields : ∀ i, R (fields i) (fields' i))
    (hproject : ∀ f, head.sig.recursiveArity f = 0 → R (project f) (project' f))
    (i : Fin head.arity) :
    R (head.projectFields fields project i) (head.projectFields fields' project' i) := by
  refine Fin.addCases (fun f => ?_) (fun f => ?_) i
  · rw [projectFields_castAdd, projectFields_castAdd]
    exact hfields _
  · rw [projectFields_natAdd, projectFields_natAdd]
    split_ifs with h
    · exact hproject f h
    · exact hfields _

@[simp] theorem projectFields_self (fields : Fin head.arity → α) :
    head.projectFields fields (fun f => fields (Fin.natAdd head.sig.nfields f)) = fields := by
  funext i
  refine Fin.addCases (fun f => ?_) (fun f => ?_) i
  · rw [projectFields_castAdd]
  · rw [projectFields_natAdd, ite_self]

theorem projectFields_rel {R : α → β → Prop} {fields : Fin head.arity → α}
    {fields' : Fin head.arity → β} {project : Fin head.sig.nrecFields → α}
    (hfields : ∀ i, R (fields i) (fields' i))
    (hproject : ∀ f, head.sig.recursiveArity f = 0 →
      R (project f) (fields' (Fin.natAdd head.sig.nfields f)))
    (i : Fin head.arity) : R (head.projectFields fields project i) (fields' i) := by
  simpa using projectFields_rel₂ hfields hproject i

end CtorHead

def Shape.indProjection (target : IndHead ζ) : Shape Γ → Shape Γ
  | .ctor head names fields =>
    if head.toIndHead = target then
      .ctor head names (head.projectFields fields fun f =>
        indProjection ⟨head.η, head.sig.recursiveTarget f⟩ (fields (Fin.natAdd head.sig.nfields f)))
    else .bot
  | .struct head hstruct fields =>
    if head.toIndHead = target then
      .struct head hstruct (head.projectFields fields fun f =>
        indProjection ⟨head.η, head.sig.recursiveTarget f⟩ (fields (Fin.natAdd head.sig.nfields f)))
    else .bot
  | _ => .bot

theorem Basis.IsBottom.indProjection (target : IndHead ζ) {a : Shape Γ} :
    Basis.IsBottom a →
    Basis.IsBottom (a.indProjection target)
  | .bot | .lam _ => .bot
  | .struct (head := head) (fields := fields) hf => by
    simp only [Shape.indProjection]
    split_ifs
    · exact .struct (head.projectFields_rel (R := fun x _ => IsBottom x)
        (fields' := fields) hf fun _ _ => indProjection _ (hf _))
    · exact .bot

namespace Shape

theorem indProjection_le (target : IndHead ζ) (a : Shape Γ) : a.indProjection target ≤ a := by
  induction a generalizing target with
  | ctor head names fields ih =>
    simp only [indProjection]
    split_ifs
    · exact .ctor (head.projectFields_rel (fun _ => Basis.Le.refl _)
        fun _ _ => ih _ _)
    · exact Basis.Le.bot _
  | struct head hstruct fields ih =>
    simp only [indProjection]
    split_ifs
    · exact .struct (head.projectFields_rel (fun _ => Basis.Le.refl _)
        fun _ _ => ih _ _)
    · exact Basis.Le.bot _
  | _ => exact Basis.Le.bot _

theorem indProjection_mono (target : IndHead ζ) {a b : Shape Γ} :
    a ≤ b →
    a.indProjection target ≤ b.indProjection target
  | .collapse h => .collapse (h.indProjection target)
  | .ctor (head := head) hf => by
    simp only [indProjection]
    split_ifs
    · exact .ctor (head.projectFields_rel₂ (R := (· ≤ ·)) hf fun _ _ =>
        indProjection_mono _ (hf _))
    · exact Basis.Le.bot _
  | .struct (head := head) hf => by
    simp only [indProjection]
    split_ifs
    · exact .struct (head.projectFields_rel₂ (R := (· ≤ ·)) hf fun _ _ =>
        indProjection_mono _ (hf _))
    · exact Basis.Le.bot _
  | .sort _ | .forallE _ _ | .lam _ | .ind _ | .quot _ | .quotMk _ => Basis.Le.bot _

@[simp] theorem indProjection_idempotent (target : IndHead ζ) (a : Shape Γ) :
    (a.indProjection target).indProjection target = a.indProjection target := by
  induction a generalizing target with
  | ctor head names fields ih =>
    simp only [indProjection]
    split_ifs
    · simp only [indProjection]
      split_ifs
      refine congrArg _ (funext (head.projectFields_rel (fun _ => rfl) fun f hf => ?_))
      simp only [CtorHead.projectFields_natAdd, hf, ↓reduceIte]
      exact ih _ _
    · rfl
  | struct head hstruct fields ih =>
    simp only [indProjection]
    split_ifs
    · simp only [indProjection]
      split_ifs
      refine congrArg _ (funext (head.projectFields_rel (fun _ => rfl) fun f hf => ?_))
      simp only [CtorHead.projectFields_natAdd, hf, ↓reduceIte]
      exact ih _ _
    · rfl
  | _ => rfl

theorem indProjection_map (target : IndHead ζ)
    (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) (a : Shape Γ₁) :
    (a.map arg pi).indProjection target = (a.indProjection target).map arg pi := by
  induction a generalizing target with
  | ctor head names fields ih =>
    simp only [map, indProjection]
    split_ifs
    · exact congrArg _ (funext (head.projectFields_rel₂
        (R := fun x (y : Shape Γ₁) => x = y.map arg pi) (fun _ => rfl) fun _ _ => ih _ _))
    · rfl
  | struct head hstruct fields ih =>
    simp only [map, indProjection]
    split_ifs
    · exact congrArg _ (funext (head.projectFields_rel₂
        (R := fun x (y : Shape Γ₁) => x = y.map arg pi) (fun _ => rfl) fun _ _ => ih _ _))
    · rfl
  | _ => rfl

theorem IsCoherent.indProjection (target : IndHead ζ) {a : Shape Γ} (ha : IsCoherent Γ a) :
    IsCoherent Γ (a.indProjection target) := by
  induction ha generalizing target with
  | @ctor _ _ fields hns hf ih =>
    simp only [Shape.indProjection]
    split_ifs
    · exact .ctor hns (CtorHead.projectFields_rel (R := fun x _ => IsCoherent Γ x)
        (fields' := fields) hf fun _ _ => ih _ _)
    · exact .bot
  | @struct _ _ fields hf ih =>
    simp only [Shape.indProjection]
    split_ifs
    · exact .struct (CtorHead.projectFields_rel (R := fun x _ => IsCoherent Γ x)
        (fields' := fields) hf fun _ _ => ih _ _)
    · exact .bot
  | _ => exact .bot

end Shape

end Metalean
