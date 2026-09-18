/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Semantics.Basis.Join

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ Γ₁ Γ₂ : CtxCat E ℓ}

def Shape.rank : Shape Γ → Nat
  | .forallE _ a _ _ ins outs =>
    max (rank a) (Finset.univ.sup fun i => max (rank (ins i)) (rank (outs i))) + 1
  | .lam _ _ ins outs => (Finset.univ.sup fun i => max (rank (ins i)) (rank (outs i))) + 1
  | .ind _ ctorTypes => (Finset.univ.sup fun c => rank (ctorTypes c)) + 1
  | .ctor _ _ fields => (Finset.univ.sup fun i => rank (fields i)) + 1
  | .struct _ _ fields => (Finset.univ.sup fun i => rank (fields i)) + 1
  | .quotMk _ _ value => value.rank + 1
  | _ => 0

theorem Shape.rank_le_sup {n : Nat} (fields : Fin n → Shape Γ) (i : Fin n) :
    (fields i).rank ≤ Finset.univ.sup fun j => (fields j).rank :=
  Finset.le_sup (f := fun j => (fields j).rank) (Finset.mem_univ i)

def Graph.rank (f : Graph Γ) : Nat :=
  Finset.univ.sup fun i => max (Shape.rank (f.ins i)) (Shape.rank (f.outs i))

namespace Shape

@[simp] theorem rank_map (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) (a : Shape Γ₁) :
    (a.map arg pi).rank = a.rank := by
  induction a with
  | ind _ _ ih =>
    simp! only [map, rank]
    exact congrArg (· + 1) (Finset.sup_congr rfl fun c _ => ih c)
  | _ => simp! [*]

end Shape

namespace Graph

theorem le_rank (f : Graph Γ) (i : Fin f.size) :
    max (f.ins i).rank (f.outs i).rank ≤ f.rank :=
  Finset.le_sup (f := fun i => max (f.ins i).rank (f.outs i).rank) (Finset.mem_univ i)

theorem rank_outs_le (f : Graph Γ) (i : Fin f.size) : (f.outs i).rank ≤ f.rank :=
  (le_max_right _ _).trans (f.le_rank i)

theorem rank_append_le (f g : Graph Γ) : (f.append g).rank ≤ max f.rank g.rank := by
  refine Finset.sup_le fun i _ => ?_
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa using le_max_of_le_left (f.le_rank i)
  · simpa using le_max_of_le_right (g.le_rank i)

@[simp] theorem rank_map (arg : (Tm_ Γ₁) → Tm_ Γ₂) (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) (f : Graph Γ₁) :
    (f.map arg pi).rank = f.rank := by
  simp! [rank, map]

end Graph

theorem Shape.rank_cSup {a b : Shape Γ} : (a.cSup b).rank ≤ max a.rank b.rank := by
  fun_induction cSup a b
  · exact le_max_right _ _
  · exact le_max_left _ _
  · rename_i k names ins outs k' names' ins' outs'
    simp! only [Nat.add_max_add_right, Nat.add_le_add_iff_right]
    exact Graph.rank_append_le ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩
  · rename_i k names ins outs _ _ k' names' ins' outs' ih
    simp! only [Nat.add_max_add_right, Nat.add_le_add_iff_right]
    rw [max_max_max_comm]
    exact max_le_max ih (Graph.rank_append_le ⟨k, names, ins, outs⟩ ⟨k', names', ins', outs'⟩)
  · rename_i ih
    simp! only [Nat.add_max_add_right, Nat.add_le_add_iff_right]
    exact Finset.sup_le fun i _ => (ih i).trans (max_le_max (rank_le_sup _ _) (rank_le_sup _ _))
  · exact cSupBot_induction (P := (·.rank ≤ _)) (le_max_left _ _) (le_max_right _ _)
  · exact le_max_right _ _
  · rename_i ih
    simp! only [Nat.add_max_add_right, Nat.add_le_add_iff_right]
    exact Finset.sup_le fun i _ => (ih i).trans (max_le_max (rank_le_sup _ _) (rank_le_sup _ _))
  · exact cSupBot_induction (P := (·.rank ≤ _)) (le_max_left _ _) (le_max_right _ _)
  · rename_i _ ih
    simp! only [Nat.add_max_add_right, Nat.add_le_add_iff_right]
    exact Finset.sup_le fun c _ => (ih c).trans (max_le_max (rank_le_sup _ _) (rank_le_sup _ _))
  · exact cSupBot_induction (P := (·.rank ≤ _)) (le_max_left _ _) (le_max_right _ _)
  · rename_i ih
    simpa [rank, Nat.add_max_add_right] using Nat.add_le_add_right ih 1
  · exact cSupBot_induction (P := (·.rank ≤ _)) (le_max_left _ _) (le_max_right _ _)

end Metalean
