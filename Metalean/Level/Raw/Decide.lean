/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Raw.Order
import Metalean.Data.List

/-!
# Level algebra

This file incorporates code from Lean4Lean.

## References

- Yoan Géran, _A Canonical Form for Universe Levels in Impredicative Type Theory_, CSL 2026,
  <https://doi.org/10.4230/LIPIcs.CSL.2026.39>
-/

namespace Metalean.RawLevel

variable {ℓ : Nat}

abbrev Guard (ℓ : Nat) : Type := List (Param ℓ)

namespace Guard

def sat (G : Guard ℓ) (ν : Param ℓ → Nat) : Bool :=
  G.all fun p => ν p != 0

def subset (G₁ G₂ : Guard ℓ) : Bool :=
  G₁.all fun p => G₂.contains p

variable (ν : Param ℓ → Nat)

@[simp] theorem sat_nil : sat [] ν = true := rfl

@[simp] theorem sat_cons (p : Param ℓ) (G : Guard ℓ) :
    sat (p :: G) ν = ((ν p != 0) && sat G ν) := by
  simp [sat]

theorem sat_iff {G : Guard ℓ} : sat G ν = true ↔ ∀ p ∈ G, ν p ≠ 0 := by
  simp [sat]

theorem subset_iff {G₁ G₂ : Guard ℓ} : subset G₁ G₂ = true ↔ ∀ p ∈ G₁, p ∈ G₂ := by
  simp [subset]

theorem sat_of_subset {G₁ G₂ : Guard ℓ} :
    subset G₁ G₂ = true →
    sat G₂ ν = true →
    sat G₁ ν = true :=
  fun h hs => (sat_iff ν).mpr fun p hp => (sat_iff ν).mp hs p (subset_iff.mp h p hp)

end Guard

inductive Sub (ℓ : Nat) where
  | const (guard : Guard ℓ) (offset : Nat)
  | var (p : Param ℓ) (guard : Guard ℓ) (offset : Nat)

namespace Sub

def offset : Sub ℓ → Nat
  | const _ k | var _ _ k => k

def eval (ν : Param ℓ → Nat) : Sub ℓ → Nat
  | const G k => if Guard.sat G ν then k else 0
  | var p G k => if Guard.sat (p :: G) ν then ν p + k else 0

def nontrivial : Sub ℓ → Bool
  | const _ k => k != 0
  | var .. => true

def dominates : Sub ℓ → Sub ℓ → Bool
  | const G₂ k₂, const G₁ k₁ => Guard.subset G₂ G₁ && decide (k₁ ≤ k₂)
  | var p₂ G₂ k₂, const G₁ k₁ => Guard.subset (p₂ :: G₂) G₁ && decide (k₁ ≤ k₂ + 1)
  | const .., var .. => false
  | var p₂ G₂ k₂, var p₁ G₁ k₁ =>
    decide (p₂ = p₁) && Guard.subset G₂ (p₁ :: G₁) && decide (k₁ ≤ k₂)

def atLeast (G : Guard ℓ) (k : Nat) : List (Sub ℓ) :=
  if k = 0 then [] else [const G k]

def evalMax (ν : Param ℓ → Nat) (S : List (Sub ℓ)) : Nat :=
  (S.map (eval ν)).foldr Nat.max 0

def subsLe (S₁ S₂ : List (Sub ℓ)) : Bool :=
  S₁.all fun t₁ => S₂.any fun t₂ => dominates t₂ t₁

variable (ν : Param ℓ → Nat)

@[simp] theorem evalMax_nil : evalMax ν ([] : List (Sub ℓ)) = 0 := rfl

@[simp] theorem evalMax_cons (t : Sub ℓ) (S : List (Sub ℓ)) :
    evalMax ν (t :: S) = Nat.max (t.eval ν) (evalMax ν S) := rfl

@[simp] theorem evalMax_append (S₁ S₂ : List (Sub ℓ)) :
    evalMax ν (S₁ ++ S₂) = Nat.max (evalMax ν S₁) (evalMax ν S₂) := by
  simp only [evalMax, List.map_append]
  exact List.foldr_max_append _ _

theorem le_evalMax {t : Sub ℓ} {S : List (Sub ℓ)} :
    t ∈ S →
    t.eval ν ≤ evalMax ν S :=
  fun h => List.foldr_max_le_of_mem (List.mem_map_of_mem h)

@[simp] theorem evalMax_atLeast (G : Guard ℓ) (k : Nat) :
    evalMax ν (atLeast G k) = if Guard.sat G ν then k else 0 := by
  unfold atLeast
  split
  · simp [*]
  · simp [evalMax, eval]

theorem eval_const_le (G : Guard ℓ) (k : Nat) : eval ν (const G k) ≤ k := by
  simp only [eval]
  split <;> simp

theorem dominates_sound {t₁ t₂ : Sub ℓ} :
    dominates t₂ t₁ = true →
    t₁.eval ν ≤ t₂.eval ν := by
  cases t₂ with
  | const G₂ k₂ =>
    cases t₁ with
    | const G₁ k₁ =>
      simp only [dominates, Bool.and_eq_true, decide_eq_true_eq, eval]
      intro ⟨hsub, hk⟩
      by_cases h₁ : Guard.sat G₁ ν = true
      · simp [h₁, Guard.sat_of_subset ν hsub h₁]
        exact hk
      · simp [h₁]
    | var p₁ G₁ k₁ => simp [dominates]
  | var p₂ G₂ k₂ =>
    cases t₁ with
    | const G₁ k₁ =>
      simp only [dominates, Bool.and_eq_true, decide_eq_true_eq, eval]
      intro ⟨hsub, hk⟩
      by_cases h₁ : Guard.sat G₁ ν = true
      · have hsat := Guard.sat_of_subset ν hsub h₁
        have hp : ν p₂ ≠ 0 := (Guard.sat_iff ν).mp hsat p₂ List.mem_cons_self
        rw [ite_eq_left h₁, ite_eq_left hsat]
        omega
      · simp [h₁]
    | var p₁ G₁ k₁ =>
      simp only [dominates, Bool.and_eq_true, decide_eq_true_eq, eval]
      intro ⟨⟨rfl, hsub⟩, hk⟩
      by_cases h₁ : Guard.sat (p₂ :: G₁) ν = true
      · have hsat : Guard.sat (p₂ :: G₂) ν = true :=
          (Guard.sat_iff ν).mpr fun q hq => match List.mem_cons.mp hq with
            | .inl rfl => (Guard.sat_iff ν).mp h₁ q List.mem_cons_self
            | .inr hq => (Guard.sat_iff ν).mp h₁ q (Guard.subset_iff.mp hsub q hq)
        rw [ite_eq_left h₁, ite_eq_left hsat]
        omega
      · simp [h₁]

theorem exists_dominator {S : List (Sub ℓ)} {t : Sub ℓ} :
    t.nontrivial = true →
    (∀ ν, t.eval ν ≤ evalMax ν S) →
    ∃ t' ∈ S, dominates t' t = true := by
  intro hnt h
  cases t with
  | const G k =>
    have hk : k ≠ 0 := by simpa [nontrivial] using hnt
    let ν : Param ℓ → Nat := fun p => if p ∈ G then 1 else 0
    have hmem (p : Param ℓ) : ν p ≠ 0 → p ∈ G := by
      simp only [ν]
      split <;> simp_all
    have hle (p : Param ℓ) : ν p ≤ 1 := by
      simp only [ν]
      split <;> omega
    have hsat : Guard.sat G ν = true := (Guard.sat_iff ν).mpr fun p hp => by simp [ν, hp]
    have hval : eval ν (const G k) = k := by simp [eval, hsat]
    obtain hz | ⟨y, hy, hyle⟩ := List.le_foldr_max_iff (hval ▸ h ν)
    · exact absurd hz hk
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hy
    refine ⟨t', ht', ?_⟩
    cases t' with
    | const G₂ k₂ =>
      simp only [eval] at hyle
      split at hyle
      · simp only [dominates, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨Guard.subset_iff.mpr fun p hp => hmem p ((Guard.sat_iff ν).mp ‹_› p hp), hyle⟩
      · omega
    | var p₂ G₂ k₂ =>
      simp only [eval] at hyle
      split at hyle
      · rename_i hsat₂
        have := hle p₂
        simp only [dominates, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨Guard.subset_iff.mpr fun p hp => hmem p ((Guard.sat_iff ν).mp hsat₂ p hp), by omega⟩
      · omega
  | var p G k =>
    let N := (S.map offset).foldr Nat.max 0 + 2
    let ν : Param ℓ → Nat := fun q => if q = p then N else if q ∈ G then 1 else 0
    have hN : 2 ≤ N := by simp only [N]; omega
    have hνp : ν p = N := by simp [ν]
    have hmem (q : Param ℓ) : ν q ≠ 0 → q ∈ p :: G := by
      simp only [ν, List.mem_cons]
      split <;> [simp_all; (split <;> simp_all)]
    have hne (q : Param ℓ) : q ≠ p → ν q ≤ 1 := by
      simp only [ν]
      intro hq
      simp [hq]
      split <;> omega
    have hbound (t' : Sub ℓ) : t' ∈ S → t'.offset + 2 ≤ N := fun ht' => by
      have := List.foldr_max_le_of_mem (List.mem_map_of_mem (f := offset) ht')
      simp only [N]
      omega
    have hsat : Guard.sat (p :: G) ν = true := (Guard.sat_iff ν).mpr fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · omega
      · simp only [ν]
        split
        · omega
        · simp
    have hval : eval ν (var p G k) = N + k := by simp only [eval, ite_eq_left hsat, hνp]
    obtain hz | ⟨y, hy, hyle⟩ := List.le_foldr_max_iff (hval ▸ h ν)
    · omega
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp hy
    have hoff := hbound t' ht'
    refine ⟨t', ht', ?_⟩
    cases t' with
    | const G₂ k₂ =>
      have := eval_const_le ν G₂ k₂
      simp only [offset] at hoff
      omega
    | var p₂ G₂ k₂ =>
      simp only [offset] at hoff
      simp only [eval] at hyle
      split at hyle
      · rename_i hsat₂
        have hp₂ : p₂ = p := by
          by_contra hc
          have := hne p₂ hc
          omega
        subst hp₂
        rw [hνp] at hyle
        simp only [dominates, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨trivial, Guard.subset_iff.mpr fun q hq =>
          hmem q ((Guard.sat_iff ν).mp hsat₂ q (List.mem_cons_of_mem _ hq))⟩, by omega⟩
      · omega

end Sub

def subs (G : Guard ℓ) (k : Nat) : RawLevel ℓ → List (Sub ℓ)
  | zero => Sub.atLeast G k
  | succ l => subs G (k + 1) l
  | max l₁ l₂ => subs G k l₁ ++ subs G k l₂
  | param p => Sub.atLeast G k ++ [.var p G k]
  | imax _ zero => Sub.atLeast G k
  | imax l₁ (succ l₂) => subs G k l₁ ++ subs G (k + 1) l₂
  | imax l₁ (max l₂ l₃) => subs G k (l₁.imax l₂) ++ subs G k (l₁.imax l₃)
  | imax l₁ (imax l₂ l₃) => subs G k (l₁.imax l₃) ++ subs G k (l₂.imax l₃)
  | imax l₁ (param p) => Sub.atLeast G k ++ Sub.var p G k :: subs (p :: G) k l₁
termination_by l => sizeOf l

theorem nontrivial_of_mem_subs {G : Guard ℓ} {k : Nat} {l : RawLevel ℓ} {t : Sub ℓ} :
    t ∈ subs G k l →
    t.nontrivial = true := by
  fun_induction subs G k l <;> intro ht <;>
    simp_all [Sub.atLeast, Sub.nontrivial] <;> grind

theorem evalMax_subs (ν : Param ℓ → Nat) (G : Guard ℓ) (k : Nat) (l : RawLevel ℓ) :
    Sub.evalMax ν (subs G k l) = if Guard.sat G ν then l.eval ν + k else 0 := by
  fun_induction subs G k l with
  | case1 G k => simp
  | case2 G k l ih =>
    simp only [ih, eval_succ]
    split_ifs <;> omega
  | case3 G k l₁ l₂ ih₁ ih₂ =>
    simp only [Sub.evalMax_append, ih₁, ih₂, eval_max, Nat.max_def]
    split_ifs <;> omega
  | case4 G k p =>
    simp only [Sub.evalMax_append, Sub.evalMax_atLeast, Sub.evalMax_cons, Sub.evalMax_nil,
      Sub.eval, Guard.sat_cons, eval_param, Nat.max_def]
    by_cases hp : ν p = 0 <;> split_ifs <;> simp_all
  | case5 G k l => simp
  | case6 G k l₁ l₂ ih₁ ih₂ =>
    simp only [Sub.evalMax_append, ih₁, ih₂, eval_imax, eval_succ, Nat.imax_succ_right,
      Nat.max_def]
    split_ifs <;> omega
  | case7 G k l₁ l₂ l₃ ih₁ ih₂ =>
    simp only [Sub.evalMax_append, ih₁, ih₂, eval_imax, eval_max, Nat.imax, Nat.max_def]
    split_ifs <;> omega
  | case8 G k l₁ l₂ l₃ ih₁ ih₂ =>
    simp only [Sub.evalMax_append, ih₁, ih₂, eval_imax, Nat.imax, Nat.max_def]
    split_ifs <;> omega
  | case9 G k l₁ p ih =>
    simp only [Sub.evalMax_append, Sub.evalMax_atLeast, Sub.evalMax_cons, Sub.eval, ih,
      Guard.sat_cons, eval_imax, eval_param, Nat.imax, Nat.max_def]
    by_cases hp : ν p = 0 <;> split_ifs <;> simp_all <;> omega

public def decLe (l₁ l₂ : RawLevel ℓ) : Bool :=
  Sub.subsLe (subs [] 0 l₁) (subs [] 0 l₂)

theorem evalMax_subs_nil (ν : Param ℓ → Nat) (l : RawLevel ℓ) :
    Sub.evalMax ν (subs [] 0 l) = l.eval ν := by
  simp [evalMax_subs]

public theorem decLe_iff (l₁ l₂ : RawLevel ℓ) : decLe l₁ l₂ = true ↔ l₁ ≤ l₂ := by
  simp only [decLe, Sub.subsLe, List.all_eq_true, List.any_eq_true]
  constructor
  · intro h ν
    rw [← evalMax_subs_nil ν l₁, ← evalMax_subs_nil ν l₂]
    refine List.foldr_max_le_of_all fun y hy => ?_
    obtain ⟨t₁, ht₁, rfl⟩ := List.mem_map.mp hy
    have ⟨t₂, ht₂, hd⟩ := h t₁ ht₁
    calc Sub.eval ν t₁
      _ ≤ Sub.eval ν t₂ := Sub.dominates_sound ν hd
      _ ≤ Sub.evalMax ν (subs [] 0 l₂) := Sub.le_evalMax ν ht₂
  · intro h t₁ ht₁
    refine Sub.exists_dominator (nontrivial_of_mem_subs ht₁) fun ν => ?_
    calc Sub.eval ν t₁
      _ ≤ Sub.evalMax ν (subs [] 0 l₁) := Sub.le_evalMax ν ht₁
      _ = eval ν l₁ := evalMax_subs_nil ν l₁
      _ ≤ eval ν l₂ := h ν
      _ = Sub.evalMax ν (subs [] 0 l₂) := (evalMax_subs_nil ν l₂).symm

public instance : DecidableLE (RawLevel ℓ) :=
  fun l₁ l₂ => decidable_of_iff _ (decLe_iff l₁ l₂)

public instance (l₁ l₂ : RawLevel ℓ) : Decidable (l₁ ≈ l₂) :=
  decidable_of_iff _ RawLevel.equiv_iff_le_le.symm

end Metalean.RawLevel
