/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Sort
public import Metalean.TypeTheory.SetModel.Category

@[expose] public noncomputable section

namespace Metalean.TypeTheory.SetModel

open CategoryTheory Opposite ZFSet NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {ℓ : Nat} {Γ Δ : ZFSet.{u}}

def value (v : Level ℓ) : Nat :=
  v.eval fun _ => 0

def sortFam (v : Level ℓ) (Γ : ZFSet.{u}) : Fam Γ where
  obj _ := S_ (value v)
  bound := ⟨value v + 1, fun _ => sort_mem_succ _⟩

theorem type_of_sort {v : Level ℓ} {t : Elt Γ}
    (ht : typing.app (op Γ) t = yonedaEquiv (ofFam (sortFam v Γ))) :
    t.type = sortFam v Γ :=
  ht.trans (yonedaEquiv_ofFam (sortFam v Γ))

def elFam (v : Level ℓ) (t : Elt Γ) (ht : t.type = sortFam v Γ) : Fam Γ where
  obj := t.obj
  bound := ⟨value v, fun γ => by
    have h := t.obj_mem γ
    rw [ht] at h
    exact h⟩

def code (A : Fam Γ) (v : Level ℓ) (hv : ∀ γ, A.obj γ ∈ S_ (value v)) : Elt Γ where
  type := sortFam v Γ
  obj := A.obj
  obj_mem := hv

instance : HasSorts Ty.{u} Tm.{u} ℓ where
  sort v Γ := ofFam (sortFam v Γ)
  subst_sort σ v := map_ofFam σ (sortFam v _)
  el v t ht := ofFam (elFam v t (type_of_sort ht))
  subst_el σ v t ht := map_ofFam σ (elFam v t (type_of_sort ht))
  exists_el {Γ} A := by
    have ⟨n, hn⟩ := (yonedaEquiv A).bound
    refine ⟨Level.ofNat n, code (yonedaEquiv A) (Level.ofNat n) fun γ => ?_, rfl,
      ofFam_yonedaEquiv A⟩
    simpa [value] using hn γ
  exists_el_sort v Γ := by
    refine ⟨code (sortFam v Γ) v.succ fun _ => ?_, rfl, rfl⟩
    simpa [value, sortFam] using sort_mem_succ (value v)

end Metalean.TypeTheory.SetModel
