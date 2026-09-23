/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Raw.Equiv

@[expose] public section

namespace Metalean.RawLevel

variable {ℓ : Nat} (ν : Param ℓ → Nat)

def toOffset : RawLevel ℓ → RawLevel ℓ × Nat
  | succ l => ((toOffset l).1, (toOffset l).2 + 1)
  | l => (l, 0)

def succN (l : RawLevel ℓ) : Nat → RawLevel ℓ
  | 0 => l
  | k + 1 => succ (succN l k)

def isExplicit : RawLevel ℓ → Bool
  | zero => true
  | succ l => isExplicit l
  | _ => false

def isNotZero : RawLevel ℓ → Bool
  | succ _ => true
  | max l₁ l₂ => isNotZero l₁ || isNotZero l₂
  | imax _ l₂ => isNotZero l₂
  | _ => false

def isMaxOf (l : RawLevel ℓ) : RawLevel ℓ → Bool
  | max a b => a == l || b == l
  | _ => false

def mkMax (l₁ l₂ : RawLevel ℓ) : RawLevel ℓ :=
  if isExplicit l₁ && isExplicit l₂ then
    if (toOffset l₂).2 ≤ (toOffset l₁).2 then l₁ else l₂
  else if l₁ = l₂ then l₁
  else if l₁ = zero then l₂
  else if l₂ = zero then l₁
  else if isMaxOf l₁ l₂ then l₂
  else if isMaxOf l₂ l₁ then l₁
  else if (toOffset l₁).1 = (toOffset l₂).1 then
    if (toOffset l₂).2 < (toOffset l₁).2 then l₁ else l₂
  else max l₁ l₂

def mkIMax (l₁ l₂ : RawLevel ℓ) : RawLevel ℓ :=
  if isNotZero l₂ then mkMax l₁ l₂
  else if l₂ = zero then l₂
  else if l₁ = zero || l₁ = one then l₂
  else if l₁ = l₂ then l₁
  else imax l₁ l₂

def mkMaxList : List (RawLevel ℓ) → RawLevel ℓ
  | [] => zero
  | [l] => l
  | l :: ls => mkMax l (mkMaxList ls)

def maxArgs : RawLevel ℓ → List (RawLevel ℓ)
  | max l₁ l₂ => maxArgs l₁ ++ maxArgs l₂
  | l => [l]

def kindIdx : RawLevel ℓ → Nat
  | zero => 0
  | succ _ => 1
  | max .. => 2
  | imax .. => 3
  | param _ => 4

theorem sizeOf_toOffset_le (l : RawLevel ℓ) : sizeOf (toOffset l).1 ≤ sizeOf l := by
  induction l with
  | succ l ih => simp only [toOffset, succ.sizeOf_spec]; omega
  | zero | max | imax | param => simp [toOffset]

mutual

def normLt (a b : RawLevel ℓ) : Bool :=
  if (toOffset a).1 = (toOffset b).1 then (toOffset a).2 < (toOffset b).2
  else normLtBase (toOffset a).1 (toOffset b).1
termination_by (sizeOf a, 1)
decreasing_by exact Prod.Lex.right' _ (sizeOf_toOffset_le a) Nat.zero_lt_one

def normLtBase : RawLevel ℓ → RawLevel ℓ → Bool
  | param p₁, param p₂ => p₁ < p₂
  | max a₁ b₁, max a₂ b₂ | imax a₁ b₁, imax a₂ b₂ =>
    if a₁ = a₂ then normLt b₁ b₂ else normLt a₁ a₂
  | l₁, l₂ => kindIdx l₁ < kindIdx l₂
termination_by l₁ => (sizeOf l₁, 0)

end

def dropExplicit (args : List (RawLevel ℓ)) : List (RawLevel ℓ) :=
  let rest := args.dropWhile isExplicit
  match args.takeWhile isExplicit with
  | [] => args
  | expl =>
    let k := expl.foldr (fun a acc => Nat.max (toOffset a).2 acc) 0
    if rest.any fun a => k ≤ (toOffset a).2 then rest else succN zero k :: rest

def mergeOffsets : List (RawLevel ℓ) → List (RawLevel ℓ)
  | a :: b :: rest =>
    if (toOffset a).1 = (toOffset b).1 then
      if (toOffset a).2 < (toOffset b).2 then mergeOffsets (b :: rest)
      else mergeOffsets (a :: rest)
    else a :: mergeOffsets (b :: rest)
  | l => l
termination_by l => l.length

mutual

def normalizeAux (k : Nat) : RawLevel ℓ → RawLevel ℓ
  | succ l => normalizeAux (k + 1) l
  | imax l₁ l₂ => succN (mkIMax (normalizeAux 0 l₁) (normalizeAux 0 l₂)) k
  | max l₁ l₂ =>
    mkMaxList ((mergeOffsets (dropExplicit
      ((normArgs l₁ ++ normArgs l₂).mergeSort fun a b => !normLt b a))).map (succN · k))
  | l => succN l k
termination_by l => (sizeOf l, 0)

def normArgs : RawLevel ℓ → List (RawLevel ℓ)
  | max l₁ l₂ => normArgs l₁ ++ normArgs l₂
  | l => maxArgs (normalizeAux 0 l)
termination_by l => (sizeOf l, 1)

end

def normalize (l : RawLevel ℓ) : RawLevel ℓ :=
  normalizeAux 0 l

def evalMax (ls : List (RawLevel ℓ)) : Nat :=
  ls.foldr (fun l acc => Nat.max (eval ν l) acc) 0

theorem natMax_def (a b : Nat) : Nat.max a b = if a ≤ b then b else a := rfl

@[simp] theorem evalMax_nil : evalMax ν ([] : List (RawLevel ℓ)) = 0 := rfl

@[simp] theorem evalMax_cons (l : RawLevel ℓ) (ls : List (RawLevel ℓ)) :
    evalMax ν (l :: ls) = Nat.max (eval ν l) (evalMax ν ls) := rfl

@[simp] theorem evalMax_append (ls₁ ls₂ : List (RawLevel ℓ)) :
    evalMax ν (ls₁ ++ ls₂) = Nat.max (evalMax ν ls₁) (evalMax ν ls₂) := by
  induction ls₁ <;> simp [*]

theorem le_evalMax {l : RawLevel ℓ} {ls : List (RawLevel ℓ)} :
    l ∈ ls →
    eval ν l ≤ evalMax ν ls := by
  intro h
  induction ls with
  | nil => cases h
  | cons l' ls ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem evalMax_perm {ls₁ ls₂ : List (RawLevel ℓ)} :
    ls₁.Perm ls₂ →
    evalMax ν ls₁ = evalMax ν ls₂ := by
  intro h
  refine h.foldr_eq' (fun _ _ _ _ z => ?_) 0
  simp only [natMax_def]
  (repeat' split) <;> omega

@[simp] theorem eval_succN (l : RawLevel ℓ) (k : Nat) : eval ν (succN l k) = eval ν l + k := by
  induction k <;> simp [succN, Nat.add_assoc, *]

theorem eval_toOffset (l : RawLevel ℓ) : eval ν l = eval ν (toOffset l).1 + (toOffset l).2 := by
  induction l with
  | succ l ih => simp [toOffset, ih, Nat.add_assoc]
  | zero | max | imax | param => rfl

theorem eval_of_isExplicit {l : RawLevel ℓ} :
    isExplicit l = true →
    eval ν l = (toOffset l).2 := by
  intro h
  induction l with
  | zero => rfl
  | succ l ih => simp [toOffset, ih h]
  | max | imax | param => cases h

theorem pos_of_isNotZero {l : RawLevel ℓ} :
    isNotZero l = true →
    0 < eval ν l := by
  intro h
  induction l with
  | succ => simp
  | max l₁ l₂ ih₁ ih₂ =>
    simp only [isNotZero, Bool.or_eq_true] at h
    simp only [eval_max, natMax_def]
    rcases h with h | h
    · have := ih₁ h
      (repeat' split) <;> omega
    · have := ih₂ h
      (repeat' split) <;> omega
  | imax l₁ l₂ _ ih₂ =>
    have := ih₂ h
    simp only [eval_imax, Nat.imax, natMax_def]
    (repeat' split) <;> omega
  | zero | param => cases h

theorem eval_mkMax (l₁ l₂ : RawLevel ℓ) :
    eval ν (mkMax l₁ l₂) = Nat.max (eval ν l₁) (eval ν l₂) := by
  unfold mkMax
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    split <;> rw [eval_of_isExplicit ν h.1, eval_of_isExplicit ν h.2, natMax_def] <;>
      (repeat' split) <;> omega
  split
  · subst_vars
    simp
  split
  · subst_vars
    simp
  split
  · subst_vars
    simp
  split
  · rename_i h
    cases l₂ with
    | max a b =>
      simp only [isMaxOf, Bool.or_eq_true, beq_iff_eq] at h
      simp only [eval_max, natMax_def]
      rcases h with rfl | rfl <;> (repeat' split) <;> omega
    | zero | succ | imax | param => cases h
  split
  · rename_i h
    cases l₁ with
    | max a b =>
      simp only [isMaxOf, Bool.or_eq_true, beq_iff_eq] at h
      simp only [eval_max, natMax_def]
      rcases h with rfl | rfl <;> (repeat' split) <;> omega
    | zero | succ | imax | param => cases h
  split
  · rename_i h
    split <;> rw [eval_toOffset ν l₁, eval_toOffset ν l₂, h, natMax_def] <;>
      (repeat' split) <;> omega
  rfl

theorem eval_mkIMax (l₁ l₂ : RawLevel ℓ) :
    eval ν (mkIMax l₁ l₂) = Nat.imax (eval ν l₁) (eval ν l₂) := by
  unfold mkIMax
  split
  · rename_i h
    rw [eval_mkMax, Nat.imax_eq_max (Nat.pos_iff_ne_zero.mp (pos_of_isNotZero ν h))]
  split
  · subst_vars
    simp
  split
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | rfl
    · simp
    · simp only [one, eval_succ, eval_zero, Nat.imax, natMax_def]
      (repeat' split) <;> omega
  split
  · subst_vars
    simp
  rfl

theorem eval_mkMaxList (ls : List (RawLevel ℓ)) : eval ν (mkMaxList ls) = evalMax ν ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    cases ls with
    | nil => simp [mkMaxList]
    | cons l' ls =>
      change eval ν (mkMax l (mkMaxList (l' :: ls))) = _
      rw [eval_mkMax, ih]
      rfl

theorem maxArgs_ne_nil (l : RawLevel ℓ) : maxArgs l ≠ [] := by
  induction l with
  | max _ _ ih₁ _ => simp [maxArgs, ih₁]
  | zero | succ | imax | param => simp [maxArgs]

theorem evalMax_maxArgs (l : RawLevel ℓ) : evalMax ν (maxArgs l) = eval ν l := by
  induction l with
  | max l₁ l₂ ih₁ ih₂ => simp [maxArgs, ih₁, ih₂]
  | zero | succ | imax | param => simp [maxArgs]

theorem evalMax_map_succN (k : Nat) {ls : List (RawLevel ℓ)} :
    ls ≠ [] →
    evalMax ν (ls.map (succN · k)) = evalMax ν ls + k := by
  intro h
  induction ls with
  | nil => contradiction
  | cons l ls ih =>
    cases ls with
    | nil => simp
    | cons l' ls =>
      rw [List.map_cons, evalMax_cons, ih (List.cons_ne_nil _ _), evalMax_cons ν l, eval_succN]
      simp only [natMax_def]
      (repeat' split) <;> omega

theorem mergeOffsets_spec (ls : List (RawLevel ℓ)) :
    evalMax ν (mergeOffsets ls) = evalMax ν ls ∧ (ls ≠ [] → mergeOffsets ls ≠ []) := by
  fun_induction mergeOffsets ls with
  | case1 a b rest hbase hlt ih =>
    refine ⟨?_, fun _ => ih.2 (List.cons_ne_nil _ _)⟩
    simp only [ih.1, evalMax_cons, eval_toOffset ν a, eval_toOffset ν b, hbase, natMax_def]
    (repeat' split) <;> omega
  | case2 a b rest hbase hlt ih =>
    refine ⟨?_, fun _ => ih.2 (List.cons_ne_nil _ _)⟩
    simp only [ih.1, evalMax_cons, eval_toOffset ν a, eval_toOffset ν b, hbase, natMax_def]
    (repeat' split) <;> omega
  | case3 a b rest _ ih =>
    exact ⟨by rw [evalMax_cons, ih.1]; rfl, fun _ => List.cons_ne_nil _ _⟩
  | case4 l => exact ⟨rfl, id⟩

theorem evalMax_explicit {ls : List (RawLevel ℓ)} :
    (∀ a ∈ ls, isExplicit a = true) →
    evalMax ν ls = ls.foldr (fun a acc => Nat.max (toOffset a).2 acc) 0 := by
  intro h
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.foldr_cons, evalMax_cons]
    rw [eval_of_isExplicit ν (h l List.mem_cons_self),
      ih fun a ha => h a (List.mem_cons_of_mem _ ha)]

theorem dropExplicit_spec (ls : List (RawLevel ℓ)) :
    evalMax ν (dropExplicit ls) = evalMax ν ls ∧ (ls ≠ [] → dropExplicit ls ≠ []) := by
  unfold dropExplicit
  split
  · exact ⟨rfl, id⟩
  have hsplit := List.takeWhile_append_dropWhile (p := isExplicit) (l := ls)
  have hk := evalMax_explicit ν (List.all_eq_true.mp (List.all_takeWhile (l := ls)))
  dsimp only
  split
  · rename_i hany
    have ⟨a, ha, hle⟩ := List.any_eq_true.mp hany
    have hle' := Nat.le_trans (decide_eq_true_iff.mp hle)
      (show (toOffset a).2 ≤ eval ν a by rw [eval_toOffset ν a]; omega)
    have ha' := le_evalMax ν ha
    refine ⟨?_, fun _ => List.ne_nil_of_mem ha⟩
    conv => rhs; rw [← hsplit]
    rw [evalMax_append, hk]
    exact ((natMax_def _ _).trans (ite_eq_left_iff.mpr fun h => absurd (Nat.le_trans hle' ha') h)).symm
  · refine ⟨?_, fun _ => List.cons_ne_nil _ _⟩
    conv => rhs; rw [← hsplit]
    rw [evalMax_append, hk, evalMax_cons, eval_succN, eval_zero, Nat.zero_add]

theorem normalizeAux_spec (l : RawLevel ℓ) :
    (∀ k, eval ν (normalizeAux k l) = eval ν l + k) ∧
      evalMax ν (normArgs l) = eval ν l ∧ normArgs l ≠ [] := by
  have hargs (l : RawLevel ℓ) (h : eval ν (normalizeAux 0 l) = eval ν l) :
      evalMax ν (maxArgs (normalizeAux 0 l)) = eval ν l ∧ maxArgs (normalizeAux 0 l) ≠ [] :=
    ⟨(evalMax_maxArgs ν _).trans h, maxArgs_ne_nil _⟩
  induction l with
  | zero =>
    have h k : eval ν (normalizeAux k (zero : RawLevel ℓ)) = eval ν zero + k := by
      rw [normalizeAux.eq_def]
      exact eval_succN ν _ _
    rw [normArgs.eq_def]
    exact ⟨h, hargs _ (h 0)⟩
  | param p =>
    have h k : eval ν (normalizeAux k (param p)) = eval ν (param p) + k := by
      rw [normalizeAux.eq_def]
      exact eval_succN ν _ _
    rw [normArgs.eq_def]
    exact ⟨h, hargs _ (h 0)⟩
  | succ l ih =>
    have h k : eval ν (normalizeAux k l.succ) = eval ν l.succ + k := by
      rw [normalizeAux, ih.1, eval_succ]
      omega
    rw [normArgs.eq_def]
    exact ⟨h, hargs _ (h 0)⟩
  | imax l₁ l₂ ih₁ ih₂ =>
    have h k : eval ν (normalizeAux k (l₁.imax l₂)) = eval ν (l₁.imax l₂) + k := by
      rw [normalizeAux, eval_succN, eval_mkIMax, ih₁.1, ih₂.1]
      rfl
    rw [normArgs.eq_def]
    exact ⟨h, hargs _ (h 0)⟩
  | max l₁ l₂ ih₁ ih₂ =>
    have hne : normArgs l₁ ++ normArgs l₂ ≠ [] := by simp [ih₁.2.2]
    have hsort := List.mergeSort_perm (normArgs l₁ ++ normArgs l₂) fun a b => !normLt b a
    have hsortne : (normArgs l₁ ++ normArgs l₂).mergeSort (fun a b => !normLt b a) ≠ [] :=
      fun h => by
        rw [h] at hsort
        exact hne hsort.symm.eq_nil
    have hdrop := dropExplicit_spec ν
      ((normArgs l₁ ++ normArgs l₂).mergeSort fun a b => !normLt b a)
    have hmerge := mergeOffsets_spec ν (dropExplicit
      ((normArgs l₁ ++ normArgs l₂).mergeSort fun a b => !normLt b a))
    refine ⟨fun k => ?_, ?_⟩
    · rw [normalizeAux, eval_mkMaxList, evalMax_map_succN ν k (hmerge.2 (hdrop.2 hsortne)),
        hmerge.1, hdrop.1, evalMax_perm ν hsort, evalMax_append, ih₁.2.1, ih₂.2.1, eval_max]
    · rw [normArgs, evalMax_append, ih₁.2.1, ih₂.2.1]
      exact ⟨rfl, by simp [ih₁.2.2]⟩

theorem normalize_equiv (l : RawLevel ℓ) : normalize l ≈ l :=
  Equiv.of_eval fun ν => (normalizeAux_spec ν l).1 0

end Metalean.RawLevel
