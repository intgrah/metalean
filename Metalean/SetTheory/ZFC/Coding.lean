/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetTheory.ZFC.Universe.Type
import Metalean.Data.Fin

public section

universe u v w

namespace ZFSet

variable {n : Nat} {α : Type v} {β : Type w}

noncomputable def tupleValues (count : Nat) (value : ZFSet.{u}) : Fin count → ZFSet.{u} :=
  fun i => fst ((snd^[i.val]) value)

@[simp] theorem tupleValues_succ (value : ZFSet.{u}) :
    tupleValues (n + 1) value = Fin.cons (fst value) (tupleValues n (snd value)) := by
  funext i
  cases i using Fin.cases <;> simp [tupleValues, Function.iterate_succ_apply]

@[expose] noncomputable def tuple : {count : Nat} → (Fin count → ZFSet.{u}) → ZFSet.{u}
  | 0, _ => ∅
  | count + 1, values => pair (values 0) (tuple (fun i : Fin count => values i.succ))

theorem tuple_of_isEmpty {count : Nat} (h : IsEmpty (Fin count)) (values : Fin count → ZFSet.{u}) :
    tuple values = ∅ := by
  obtain rfl := Fin.eq_zero_of_isEmpty h
  rfl

@[expose] noncomputable def tupleSet : {count : Nat} → (Fin count → ZFSet.{u}) → ZFSet.{u}
  | 0, _ => {∅}
  | count + 1, domains => prod (domains 0) (tupleSet (fun i : Fin count => domains i.succ))

@[simp] theorem tupleValues_tuple {count : Nat} (values : Fin count → ZFSet) :
    tupleValues count (tuple values) = values := by
  induction count with
  | zero => exact Subsingleton.elim _ _
  | succ count ih =>
    simp only [tuple, tupleValues_succ, fst_pair, snd_pair, ih]
    exact Fin.cons_self_tail values

theorem tuple_mem_tupleSet {count : Nat} {domains values : Fin count → ZFSet}
    (h : ∀ i, values i ∈ domains i) : tuple values ∈ tupleSet domains := by
  induction count with
  | zero => simp [tuple, tupleSet]
  | succ count ih => exact pair_mem_prod.mpr ⟨h 0, ih fun i => h i.succ⟩

theorem mem_tupleSet {count : Nat} {domains : Fin count → ZFSet} {value : ZFSet} :
    value ∈ tupleSet domains ↔
      (∀ i, tupleValues count value i ∈ domains i) ∧ tuple (tupleValues count value) = value := by
  constructor
  · intro h
    induction count generalizing value with
    | zero => exact ⟨fun i => i.elim0, (mem_singleton.mp h).symm⟩
    | succ count ih =>
      obtain ⟨head, hhead, tail, htail, rfl⟩ := mem_prod.mp h
      obtain ⟨htail, heq⟩ := ih htail
      refine ⟨Fin.cases (by simpa using hhead) (fun i => by simpa using htail i), ?_⟩
      simpa [tuple, tupleValues_succ] using congrArg (pair head) heq
  · rintro ⟨h, heq⟩
    rw [← heq]
    exact tuple_mem_tupleSet h

theorem tuple_mem_vonNeumann {count : Nat} {o : Ordinal.{u}} (ho : Order.IsSuccLimit o)
    {values : Fin count → ZFSet.{u}} (h : ∀ i, values i ∈ V_ o) : tuple values ∈ V_ o := by
  induction count with
  | zero => exact empty_mem_vonNeumann ho.bot_lt
  | succ count ih => exact pair_mem_vonNeumann ho (h 0) (ih fun i => h i.succ)

theorem tupleSet_mem_vonNeumann {count : Nat} {o : Ordinal.{u}} (ho : Order.IsSuccLimit o)
    {domains : Fin count → ZFSet.{u}} (h : ∀ i, domains i ∈ V_ o) : tupleSet domains ∈ V_ o := by
  induction count with
  | zero => exact singleton_mem_vonNeumann ho (empty_mem_vonNeumann ho.bot_lt)
  | succ count ih => exact prod_mem_vonNeumann ho (h 0) (ih fun i => h i.succ)

class Encode (α : Type v) where
  encode : α → ZFSet.{u}
  injective : Function.Injective encode

export Encode (encode)

instance : Encode ZFSet where
  encode := id
  injective _ _ h := h

instance [Encode α] [Encode β] : Encode (α × β) where
  encode := fun (a, b) => pair (encode a) (encode b)
  injective _ _ h :=
    have ⟨hleft, hright⟩ := pair_inj.mp h
    Prod.ext (Encode.injective hleft) (Encode.injective hright)

instance [Encode α] : Encode (Fin n → α) := by
  induction n with
  | zero => exact { encode _ := ∅, injective _ _ _ := Subsingleton.elim _ _ }
  | succ n ih =>
    exact
      { encode v := encode (Fin.init v, v (Fin.last n))
        injective v w h := by
          have ⟨hinit, hlast⟩ : Fin.init v = Fin.init w ∧ v (Fin.last n) = w (Fin.last n) := by
            simpa using Encode.injective h
          rw [← Fin.snoc_init_self v, ← Fin.snoc_init_self w, hinit, hlast] }

theorem encode_fin_mem_type {values : Fin n → ZFSet} {level : Nat}
    (h : ∀ i, values i ∈ U_ level) : encode values ∈ U_ level := by
  induction n with
  | zero => exact empty_mem_type
  | succ n ih =>
    exact pair_mem_type (ih fun i => h i.castSucc) (h (Fin.last n))

def numeral : Nat → ZFSet
  | 0 => ∅
  | n + 1 => {numeral n}

theorem numeral_succ_ne_empty (n : Nat) : numeral (n + 1) ≠ ∅ := fun h =>
  notMem_empty (numeral n) (h ▸ mem_singleton.mpr rfl)

theorem numeral_injective {n m : Nat} (h : numeral m = numeral n) : m = n := by
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => exact absurd h.symm (numeral_succ_ne_empty n)
  | succ m ih =>
    cases n with
    | zero => exact absurd h (numeral_succ_ne_empty m)
    | succ n => exact congrArg (· + 1) (ih (singleton_injective h))

theorem numeral_mem_type (level tag : Nat) : numeral tag ∈ U_ level := by
  induction tag with
  | zero => exact empty_mem_type
  | succ tag ih => exact singleton_mem_type ih

noncomputable instance : Encode Nat where
  encode := numeral
  injective _ _ h := numeral_injective h

@[expose] noncomputable def sortKey (sortCode : Nat) (vis : ZFSet) : ZFSet :=
  encode (sortCode, vis)

@[expose] noncomputable def entry (key : ZFSet) (tag : Nat) (vargs : ZFSet) : ZFSet :=
  encode (key, tag, vargs)

@[expose] noncomputable def entryValue (tag : Nat) (vargs : ZFSet) : ZFSet :=
  pair (numeral tag) vargs

theorem entry_eq (key : ZFSet) (tag : Nat) (vargs : ZFSet) :
    entry key tag vargs = pair key (entryValue tag vargs) := rfl

theorem sortKey_injective {s s' : Nat} {i i' : ZFSet} (h : sortKey s i = sortKey s' i') :
    (s, i) = (s', i') :=
  Encode.injective h

theorem entry_injective {k k' a a' : ZFSet} {t t' : Nat} (h : entry k t a = entry k' t' a') :
    (k, t, a) = (k', t', a') :=
  Encode.injective h

theorem entry_tag_eq {k k' a a' : ZFSet} {t t' : Nat} (h : entry k t a = entry k' t' a') :
    t = t' :=
  congrArg (·.2.1) (entry_injective h)

theorem entry_args_eq {k k' a a' : ZFSet} {t t' : Nat} (h : entry k t a = entry k' t' a') :
    a = a' :=
  congrArg (·.2.2) (entry_injective h)

theorem entry_mem_type {level tag : Nat} {key vargs : ZFSet}
    (hkey : key ∈ U_ level) (hargs : vargs ∈ U_ level) : entry key tag vargs ∈ U_ level :=
  pair_mem_type hkey (pair_mem_type (numeral_mem_type level tag) hargs)

theorem sortKey_mem_type {level sortCode : Nat} {vis : ZFSet}
    (his : vis ∈ U_ level) : sortKey sortCode vis ∈ U_ level :=
  pair_mem_type (numeral_mem_type level sortCode) his

theorem entryValue_mem_fibre {key vargs X : ZFSet} {tag : Nat}
    (h : entry key tag vargs ∈ X) : entryValue tag vargs ∈ fibreOp X key :=
  mem_fibre.mpr (entry_eq key tag vargs ▸ h)

end ZFSet
