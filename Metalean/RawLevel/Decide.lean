/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.RawLevel.Order
import Metalean.List

public section

namespace Metalean.RawLevel

abbrev Zeros (ℓ : Nat) : Type := Param ℓ → Bool

abbrev Atom (ℓ : Nat) : Type := Option (Param ℓ) × Nat

variable {ℓ : Nat}

namespace Atom

@[expose] def eval (ν : Param ℓ → Nat) : Atom ℓ → Nat
  | (none, k) => k
  | (some p, k) => ν p + k

theorem eval_zero_le_eval (ν : Param ℓ → Nat) : ∀ a, eval (fun _ => 0) a ≤ eval ν a
  | (none, _) => Nat.le_refl _
  | (some _, _) => Nat.add_le_add_right (Nat.zero_le _) _

theorem eval_shift (ν : Param ℓ → Nat) (k : Nat) :
    ∀ p, eval ν (p, k + 1) = eval ν (p, k) + 1
  | none => rfl
  | some _ => (Nat.add_assoc _ _ _).symm

@[expose] def dominates : Atom ℓ → Atom ℓ → Bool
  | (_, kb), (none, ka) => decide (ka ≤ kb)
  | (some jb, kb), (some ja, ka) => decide (jb = ja) && decide (ka ≤ kb)
  | (none, _), (some _, _) => false

theorem dominates_sound (ν : Param ℓ → Nat) : ∀ {b a : Atom ℓ}, dominates b a = true →
    eval ν a ≤ eval ν b
  | (none, _), (none, _) => decide_eq_true_eq.mp
  | (some _, _), (none, _) => fun h => by
    have := decide_eq_true_eq.mp h
    simp only [eval]
    omega
  | (some _, _), (some _, _) => fun h => by
    simp only [dominates, Bool.and_eq_true, decide_eq_true_eq] at h
    have rfl := h
    change _ + _ ≤ _ + _
    lia
  | (none, _), (some _, _) => fun h => by simp [dominates] at h

theorem dominates_complete : ∀ b a : Atom ℓ,
    (∀ ν, eval ν a ≤ eval ν b) → dominates b a = true
  | (none, _), (none, _) => fun h => decide_eq_true_eq.mpr (h fun _ => 0)
  | (some _, _), (none, _) => fun h => by
    have := h fun _ => 0
    simp only [eval] at this
    exact decide_eq_true_eq.mpr (by omega)
  | (none, kb), (some i, _) => fun h => by
    have := h fun j => if j = i then kb + 1 else 0
    simp [eval] at this
    omega
  | (some j, kb), (some i, ka) => fun h => by
    simp [dominates]
    by_cases hij : j = i
    · subst hij
      have := h fun _ => 0
      simp only [eval] at this
      exact ⟨rfl, by omega⟩
    · exfalso
      have := h fun k => if k = i then kb + 1 else 0
      have hji : j ≠ i := hij
      simp [eval, ite_eq_right hji] at this
      omega

end Atom

theorem Atom.extract_dominator (B : List (Atom ℓ)) (hB : B ≠ []) : ∀ a : Atom ℓ,
    (∀ ν, eval ν a ≤ (B.map (eval ν)).foldr Nat.max 0) →
    ∃ b ∈ B, ∀ ν, eval ν a ≤ eval ν b
  | (none, ka) => fun h => by
    by_cases hka : ka = 0
    · have ⟨b, hb⟩ := List.exists_mem_of_ne_nil B hB
      exact ⟨b, hb, fun _ => hka ▸ Nat.zero_le _⟩
    rcases List.le_foldr_max_iff (h fun _ => 0) with heq | ⟨_, hymem, hyle⟩
    · exact absurd heq hka
    have ⟨b, hbmem, hbeq⟩ := List.mem_map.mp hymem
    exact ⟨b, hbmem, fun ν => Nat.le_trans (hbeq ▸ hyle) (eval_zero_le_eval ν b)⟩
  | (some i, ka) => fun h => by
    let C := (B.map (eval fun _ => 0)).foldr Nat.max 0
    let N := C + ka + 1
    let ns_N : Param ℓ → Nat := fun j => if j = i then N else 0
    have hnsi : ns_N i = N := ite_eq_left rfl
    have hKey : N + ka ≤ (B.map (eval ns_N)).foldr Nat.max 0 := hnsi ▸ h ns_N
    rcases List.le_foldr_max_iff hKey with hzero | ⟨y, hymem, hyle⟩
    · exact absurd hzero (by change C + ka + 1 + ka ≠ 0; omega)
    have ⟨b, hbmem, hbeq⟩ := List.mem_map.mp hymem
    have hbBound : eval (fun _ => 0) b ≤ C :=
      List.foldr_max_le_of_mem (List.mem_map_of_mem hbmem)
    rcases b with ⟨_ | j, kb⟩
    · simp only [eval] at hbeq hbBound
      omega
    · simp only [eval] at hbeq hbBound
      by_cases hji : j = i
      · subst hji
        refine ⟨_, hbmem, fun ν => ?_⟩
        change ν j + ka ≤ ν j + kb
        rw [hnsi] at hbeq
        omega
      · have : ns_N j = 0 := ite_eq_right hji
        rw [this] at hbeq
        omega

@[expose] def atomsLe (A B : List (Atom ℓ)) : Bool :=
  A.all fun a => B.any fun b => Atom.dominates b a

theorem atomsLe_iff (A B : List (Atom ℓ)) (hB : B ≠ []) :
    atomsLe A B = true ↔
      ∀ ν, (A.map (Atom.eval ν)).foldr Nat.max 0 ≤ (B.map (Atom.eval ν)).foldr Nat.max 0 := by
  simp only [atomsLe, List.all_eq_true, List.any_eq_true]
  refine ⟨fun h ν => ?_, fun h a ha => ?_⟩
  · apply List.foldr_max_le_of_all
    intro y hy
    have ⟨a, ha, haeq⟩ := List.mem_map.mp hy
    have ⟨b, hbmem, hdom⟩ := h a ha
    exact haeq ▸ Nat.le_trans (Atom.dominates_sound ν hdom)
      (List.foldr_max_le_of_mem (List.mem_map_of_mem hbmem))
  · have hPoint : ∀ ν, Atom.eval ν a ≤ (B.map (Atom.eval ν)).foldr Nat.max 0 := fun ν =>
      Nat.le_trans (List.foldr_max_le_of_mem (List.mem_map_of_mem ha)) (h ν)
    have ⟨b, hbmem, hb⟩ := Atom.extract_dominator B hB a hPoint
    exact ⟨b, hbmem, Atom.dominates_complete b a hb⟩

@[expose] def Zeros.lift (Z : Zeros ℓ) (ν : Param ℓ → Nat) : Param ℓ → Nat :=
  fun p => if Z p then 0 else ν p + 1

@[expose] def isZero (Z : Zeros ℓ) : RawLevel ℓ → Bool
  | zero => true
  | succ _ => false
  | max l₁ l₂ => isZero Z l₁ && isZero Z l₂
  | imax _ l₂ => isZero Z l₂
  | param p => Z p

theorem isZero_iff (Z : Zeros ℓ) (ν : Param ℓ → Nat) (l : RawLevel ℓ) :
    isZero Z l = true ↔ l.eval (Z.lift ν) = 0 := by
  induction l with
  | zero | succ => simp [isZero, eval]
  | max _ _ ih₁ ih₂ =>
    simp only [isZero, eval, Bool.and_eq_true, ih₁, ih₂]
    grind
  | imax _ l₂ _ ih₂ =>
    change isZero Z l₂ = true ↔ Nat.imax _ _ = 0
    rw [ih₂, Nat.imax_eq_zero_iff]
  | param p =>
    change Z p = true ↔ (if Z p = true then 0 else ν p + 1) = 0
    cases Z p <;> simp

@[expose] def atoms (Z : Zeros ℓ) : RawLevel ℓ → List (Atom ℓ)
  | zero => [(none, 0)]
  | succ l => (atoms Z l).map fun (p, k) => (p, k + 1)
  | max l₁ l₂ => atoms Z l₁ ++ atoms Z l₂
  | imax l₁ l₂ => if isZero Z l₂ then [(none, 0)] else atoms Z l₁ ++ atoms Z l₂
  | param p => if Z p then [(none, 0)] else [(some p, 1)]

theorem atoms_ne_nil (Z : Zeros ℓ) (l : RawLevel ℓ) : atoms Z l ≠ [] := by
  induction l with
  | zero => simp!
  | succ _ ih => simp! [ih]
  | max _ _ ih₁ _ => simp! [ih₁]
  | imax _ _ ih₁ _ => simp!; split <;> simp [ih₁]
  | param p => simp!; split <;> simp

theorem foldr_atoms (Z : Zeros ℓ) (ν : Param ℓ → Nat) (l : RawLevel ℓ) :
    ((atoms Z l).map (Atom.eval ν)).foldr Nat.max 0 = l.eval (Z.lift ν) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    have hmap : ((atoms Z l).map fun (p, k) => (p, k + 1)).map (Atom.eval ν)
        = ((atoms Z l).map (Atom.eval ν)).map (· + 1) := by
      simp
      intro p k _
      exact Atom.eval_shift ν k p
    change (((atoms Z l).map fun (p, k) => (p, k + 1)).map (Atom.eval ν)).foldr Nat.max 0 = _
    rw [hmap, List.foldr_max_map_succ fun h => atoms_ne_nil Z l (List.map_eq_nil_iff.mp h), ih]
    rfl
  | max l₁ l₂ ih₁ ih₂ =>
    change ((atoms Z l₁ ++ atoms Z l₂).map (Atom.eval ν)).foldr Nat.max 0 = _
    rw [List.map_append, List.foldr_max_append, ih₁, ih₂]
    rfl
  | imax l₁ l₂ ih₁ ih₂ =>
    change ((if isZero Z l₂ then _ else atoms Z l₁ ++ atoms Z l₂).map
      (Atom.eval ν)).foldr Nat.max 0 = Nat.imax _ _
    by_cases hz : isZero Z l₂ = true
    · rw [ite_eq_left hz, Nat.imax_eq_zero_iff.mpr ((isZero_iff Z ν l₂).mp hz)]
      rfl
    · rw [ite_eq_right hz, Nat.imax_eq_max fun h => hz ((isZero_iff Z ν l₂).mpr h),
        List.map_append, List.foldr_max_append, ih₁, ih₂]
  | param p =>
    change ((if Z p then [(none, 0)] else [(some p, 1)]).map (Atom.eval ν)).foldr Nat.max 0
      = Z.lift ν p
    simp only [Zeros.lift]
    split <;> simp [Atom.eval]

@[expose] def zerosOf : List (Param ℓ) → List (Zeros ℓ)
  | [] => [fun _ => false]
  | p :: ps => (zerosOf ps).flatMap fun Z => [Z, fun q => decide (q = p) || Z q]

theorem exists_mem_zerosOf (Z : Zeros ℓ) (ps : List (Param ℓ)) :
    ∃ Z' ∈ zerosOf ps, ∀ p, Z' p = true ↔ p ∈ ps ∧ Z p = true := by
  induction ps with
  | nil => exact ⟨fun _ => false, List.mem_singleton_self _, by simp⟩
  | cons p ps ih =>
    have ⟨Z', hmem, hZ'⟩ := ih
    by_cases hp : Z p = true
    · refine ⟨fun q => decide (q = p) || Z' q, List.mem_flatMap.mpr ⟨Z', hmem, by simp⟩, fun q => ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq, hZ' q, List.mem_cons]
      constructor
      · rintro (rfl | ⟨hq, hZq⟩)
        · exact ⟨Or.inl rfl, hp⟩
        · exact ⟨Or.inr hq, hZq⟩
      · rintro ⟨rfl | hq, hZq⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hq, hZq⟩
    · refine ⟨Z', List.mem_flatMap.mpr ⟨Z', hmem, by simp⟩, fun q => ?_⟩
      simp only [hZ' q, List.mem_cons]
      constructor
      · exact fun ⟨hq, hZq⟩ => ⟨Or.inr hq, hZq⟩
      · rintro ⟨rfl | hq, hZq⟩
        · exact absurd hZq hp
        · exact ⟨hq, hZq⟩

@[expose] def allZeros (ℓ : Nat) : List (Zeros ℓ) := zerosOf (List.finRange ℓ)

theorem exists_mem_allZeros (Z : Zeros ℓ) : ∃ Z' ∈ allZeros ℓ, ∀ p, Z' p = Z p :=
  have ⟨Z', hmem, hZ'⟩ := exists_mem_zerosOf Z (List.finRange ℓ)
  ⟨Z', hmem, fun p => Bool.eq_iff_iff.mpr
    ⟨fun h => ((hZ' p).mp h).2, fun h => (hZ' p).mpr ⟨List.mem_finRange p, h⟩⟩⟩

@[expose] def decLe (l₁ l₂ : RawLevel ℓ) : Bool :=
  (allZeros ℓ).all fun Z => atomsLe (atoms Z l₁) (atoms Z l₂)

theorem decLe_iff (l₁ l₂ : RawLevel ℓ) : decLe l₁ l₂ = true ↔ l₁ ≤ l₂ := by
  simp only [decLe, List.all_eq_true]
  constructor
  · intro h ν
    have ⟨Z, hmem, hZ⟩ := exists_mem_allZeros (ℓ := ℓ) fun p => decide (ν p = 0)
    have hle := (atomsLe_iff _ _ (atoms_ne_nil Z l₂)).mp (h Z hmem) fun p => ν p - 1
    rw [foldr_atoms, foldr_atoms] at hle
    have hlift : Z.lift (fun p => ν p - 1) = ν := funext fun p => by
      change (if Z p = true then 0 else ν p - 1 + 1) = ν p
      rw [hZ p]
      by_cases hns : ν p = 0
      · simp [hns]
      · rw [ite_eq_right (by simp [hns])]
        omega
    rwa [hlift] at hle
  · intro h Z _
    refine (atomsLe_iff _ _ (atoms_ne_nil Z l₂)).mpr fun ν => ?_
    rw [foldr_atoms, foldr_atoms]
    exact h _

@[expose] def decZeroLe (l₁ l₂ : RawLevel ℓ) : Bool :=
  (allZeros ℓ).all fun Z => !isZero Z l₁ || isZero Z l₂

theorem decZeroLe_iff (l₁ l₂ : RawLevel ℓ) :
    decZeroLe l₁ l₂ = true ↔ ∀ ν, l₁.eval ν = 0 → l₂.eval ν = 0 := by
  simp only [decZeroLe, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h ν hzero
    have ⟨Z, hmem, hZ⟩ := exists_mem_allZeros (ℓ := ℓ) fun p => decide (ν p = 0)
    have hlift : Z.lift (fun p => ν p - 1) = ν := funext fun p => by
      change (if Z p = true then 0 else ν p - 1 + 1) = ν p
      rw [hZ p]
      by_cases hns : ν p = 0
      · simp [hns]
      · rw [ite_eq_right (by simp [hns])]
        omega
    have hl : isZero Z l₁ = true := (isZero_iff Z _ l₁).mpr (hlift ▸ hzero)
    exact hlift ▸ (isZero_iff Z _ l₂).mp ((h Z hmem).resolve_left (by simp [hl]))
  · intro h Z _
    by_cases hl : isZero Z l₁ = true
    · exact Or.inr ((isZero_iff Z (fun _ => 0) l₂).mpr
        (h _ ((isZero_iff Z (fun _ => 0) l₁).mp hl)))
    · exact Or.inl (by simpa using hl)

instance : DecidableLE (RawLevel ℓ) :=
  fun l₁ l₂ => decidable_of_iff _ (decLe_iff l₁ l₂)

instance (l₁ l₂ : RawLevel ℓ) : Decidable (l₁ ≈ l₂) :=
  decidable_of_iff _ RawLevel.equiv_iff_le_le.symm

end Metalean.RawLevel
