/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Pi

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]

variable (Ty) in
inductive Tele : C → Type u where
  | nil {Γ : C} :
    Tele Γ
  | cons {Γ : C} (A : y Γ ⟶ Ty) (Θ : Tele (ext A)) :
    Tele Γ

@[reducible] def extTele {Γ : C} : Tele Ty Γ → C
  | .nil => Γ
  | .cons _ Θ => extTele Θ

@[reducible] def dispTele {Γ : C} : (Θ : Tele Ty Γ) → extTele Θ ⟶ Γ
  | .nil => 𝟙 Γ
  | .cons A Θ => dispTele Θ ≫ disp A

@[reducible] def Tele.subst {Γ Δ : C} (σ : Δ ⟶ Γ) : Tele Ty Γ → Tele Ty Δ
  | .nil => .nil
  | .cons A Θ => .cons (y σ ≫ A) (Θ.subst (extMap σ A))

def Tele.extMap {Γ Δ : C} (σ : Δ ⟶ Γ) : (Θ : Tele Ty Γ) → extTele (Θ.subst σ) ⟶ extTele Θ
  | .nil => σ
  | .cons A Θ => Θ.extMap (NaturalModel.extMap σ A)

theorem Tele.extMap_disp {Γ Δ : C} (σ : Δ ⟶ Γ) (Θ : Tele Ty Γ) :
    Θ.extMap σ ≫ dispTele Θ = dispTele (Θ.subst σ) ≫ σ := by
  induction Θ generalizing Δ with
  | nil => simp!
  | cons A Θ ih => simp! [reassoc_of% ih, NaturalModel.extMap_disp]

def Tele.ofFam {Γ Δ : C} (σ : Δ ⟶ Γ) : (m : Nat) → (Fin m → (y Γ ⟶ Ty)) → Tele Ty Δ
  | 0, _ => .nil
  | m + 1, A => .cons (y σ ≫ A 0) (Tele.ofFam (disp (y σ ≫ A 0) ≫ σ) m fun k => A k.succ)

def Tele.var {Γ Δ : C} (σ : Δ ⟶ Γ) :
    (m : Nat) → (A : Fin m → (y Γ ⟶ Ty)) → (k : Fin m) →
      Tm.obj (op (extTele (Tele.ofFam σ m A)))
  | 0, _ => Fin.elim0
  | m + 1, A =>
    Fin.cases
      (Tm.map (dispTele (Tele.ofFam (disp (y σ ≫ A 0) ≫ σ) m fun k => A k.succ)).op
        (genericTerm (y σ ≫ A 0)))
      (Tele.var (disp (y σ ≫ A 0) ≫ σ) m fun k => A k.succ)

theorem Tele.var_typing {Γ Δ : C} (σ : Δ ⟶ Γ) (m : Nat) (A : Fin m → (y Γ ⟶ Ty)) (k : Fin m) :
    ℳ.typing.app _ (Tele.var σ m A k) =
      yonedaEquiv (y (dispTele (Tele.ofFam σ m A) ≫ σ) ≫ A k) := by
  induction m generalizing Δ with
  | zero => exact k.elim0
  | succ m ih =>
    induction k using Fin.cases with
    | zero =>
      refine (map_term_typing _ _ _ (genericTerm_typing (y σ ≫ A 0))).trans ?_
      simp!
    | succ j =>
      refine (ih (disp (y σ ≫ A 0) ≫ σ) (fun k => A k.succ) j).trans (congrArg yonedaEquiv ?_)
      rw [← Category.assoc]
      rfl

def piTele [HasPi Ty Tm] {Γ : C} : (Θ : Tele Ty Γ) → (y (extTele Θ) ⟶ Ty) → (y Γ ⟶ Ty)
  | .nil => id
  | .cons A Θ => piCode A ∘ piTele Θ

theorem subst_piTele [HasPi Ty Tm] {Γ Δ : C} (σ : Δ ⟶ Γ) (Θ : Tele Ty Γ) (B : y (extTele Θ) ⟶ Ty) :
    piTele (Θ.subst σ) (y (Θ.extMap σ) ≫ B) = y σ ≫ piTele Θ B := by
  induction Θ generalizing Δ with
  | nil => rfl
  | cons A Θ ih =>
    exact (congrArg (piCode (y σ ≫ A)) (ih (NaturalModel.extMap σ A) B)).trans
      (subst_piCode σ A (piTele Θ B)).symm

def appTele [HasPi Ty Tm] {Γ : C} :
    (Θ : Tele Ty Γ) → (B : y (extTele Θ) ⟶ Ty) → Sect (piTele Θ B) → Sect B
  | .nil, _, s => s
  | .cons A Θ, B, s =>
    appTele Θ B (Sect.ofTerm (piTele Θ B)
      (appTerm A (piTele Θ B) s.term s.term_typing)
      (appTerm_typing A (piTele Θ B) s.term s.term_typing))

def lamTele [HasPi Ty Tm] {Γ : C} :
    (Θ : Tele Ty Γ) → (B : y (extTele Θ) ⟶ Ty) → Sect B → Sect (piTele Θ B)
  | .nil, _, s => s
  | .cons A Θ, B, s => lamTele Θ B s |> lamSect A (piTele Θ B)

structure TeleSect {Γ : C} (Θ : Tele Ty Γ) where
  hom : Γ ⟶ extTele Θ
  hom_disp : hom ≫ dispTele Θ = 𝟙 Γ

def TeleSect.ofFam {Γ Δ : C} (σ : Δ ⟶ Γ) :
    (m : Nat) → (A : Fin m → (y Γ ⟶ Ty)) → (∀ k : Fin m, Sect (y σ ≫ A k)) →
      TeleSect (Tele.ofFam σ m A)
  | 0, _, _ => ⟨𝟙 Δ, Category.comp_id _⟩
  | m + 1, A, s =>
    have t := TeleSect.ofFam (disp (y σ ≫ A 0) ≫ σ) m (fun k => A k.succ)
      fun k => Sect.convert (by simp)
        (Sect.pullbackAlong (disp (y σ ≫ A 0)) (s k.succ))
    ⟨(s 0).hom ≫ t.hom, by
      simpa [Tele.ofFam, reassoc_of% t.hom_disp] using (s 0).hom_disp⟩

end Metalean.TypeTheory.NaturalModel
