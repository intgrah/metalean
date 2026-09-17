/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.False
public import Metalean.TypeTheory.SetModel.Pi
public import Metalean.TypeTheory.SetModel.Sort

@[expose] public noncomputable section

namespace Metalean.TypeTheory.SetModel

open CategoryTheory Opposite Limits ZFSet NaturalModel

universe u

variable {ℓ : Nat} {Γ : ZFSet.{u}}

def emptyFam (Γ : ZFSet.{u}) : Fam Γ where
  obj _ := ∅
  bound := ⟨0, fun _ => falsum_mem_truth⟩

theorem isEmpty_sect_of_obj_eq_empty {A : Fam Γ} (γ : Γ) (hA : A.obj γ = ∅) :
    IsEmpty (Sect (ofFam A)) := by
  refine ⟨fun s => ?_⟩
  have htype : s.term.type = A := s.term_typing.trans (yonedaEquiv_ofFam A)
  have hmem := s.term.obj_mem γ
  rw [htype, hA] at hmem
  exact notMem_empty _ hmem

theorem isEmpty_sect_falseType (γ : Γ) : IsEmpty (Sect (falseType Ty.{u} ℓ Γ)) := by
  refine NaturalModel.isEmpty_sect_falseType
    (code (emptyFam Γ) (Level.zero : Level ℓ) fun _ => falsum_mem_truth) rfl ?_
  exact isEmpty_sect_of_obj_eq_empty γ rfl

end Metalean.TypeTheory.SetModel
