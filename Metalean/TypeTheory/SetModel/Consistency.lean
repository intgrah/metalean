/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Interpretation
public import Metalean.TypeTheory.SetModel.False
public import Metalean.TypeTheory.SetModel.Quotient

@[expose] public noncomputable section

namespace Metalean.TypeTheory.SetModel

open CategoryTheory Opposite ZFSet NaturalModel

universe u

variable {ζ : Sigs} {E : Env ζ} {Γ : ZFSet.{u}}

theorem sort_inj {n m : Nat} (h : S_ n = S_ m) : n = m := by
  rcases Nat.lt_trichotomy n m with hlt | heq | hgt
  · have hmem : S_ n ∈ S_ m := mem_sort_mono hlt (sort_mem_succ n)
    rw [← h] at hmem
    exact absurd hmem (mem_irrefl _)
  · exact heq
  · have hmem : S_ m ∈ S_ n := mem_sort_mono hgt (sort_mem_succ m)
    rw [h] at hmem
    exact absurd hmem (mem_irrefl _)

theorem sort_injective {Z : ZFSet.{u}} (ζ : Z) {v₁ v₂ : Level 0}
    (h : HasSorts.sort (Ty := Ty) v₁ Z = HasSorts.sort v₂ Z) : v₁ = v₂ := by
  have hfam : sortFam v₁ Z = sortFam v₂ Z := ofFam_injective h
  have hval : value v₁ = value v₂ :=
    sort_inj (congrArg (fun A : Fam Z => A.obj ζ) hfam)
  refine Level.ext fun ν => ?_
  have hν : ν = fun _ => 0 := funext fun p => p.elim0
  rw [hν]
  exact hval

theorem con (γ : Γ) : E.Con :=
  TypeTheory.con (Tm := Tm) (fun σ => sort_injective (σ γ))
    (isEmpty_sect_falseType γ)

end Metalean.TypeTheory.SetModel
