/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module
import Mathlib.Data.Fintype.Shrink

public import Metalean.SetSemantics.Inductive.Recursion
public import Metalean.SetTheory.ZFC.SmallSupport
import Metalean.Grind
import Metalean.SetTheory.ZFC.Aczel.Universe

public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {a b n m level : Nat} {nctors : Fin m → Nat}

theorem fibreOp_subset_type {block : ZFSet} (h : block ⊆ U_ level) (key : ZFSet) :
    fibreOp block key ⊆ U_ level := fun _ he => by
  have h' := snd_mem_type (h (mem_fibre.mp he))
  rwa [snd_pair] at h'

structure CtorCode.DomsIn (level : Nat) (code : CtorCode n) : Prop where
  ordinary : code.ordinary.DomsIn level
  recursive : ∀ f, (code.recursive f).tele.DomsIn level

theorem CtorCode.DomsIn.mono {level₁ level₂ : Nat} (hle : level₁ ≤ level₂)
    {code : CtorCode n} (h : code.DomsIn level₁) : code.DomsIn level₂ :=
  ⟨h.ordinary.mono hle, fun f => (h.recursive f).mono hle⟩

theorem recFieldSet_subset_type {Δ : SemTele n b} (hdoms : Δ.DomsIn level)
    {index : Dom b} {block : ZFSet} (hblock : ∀ key, fibreOp block key ⊆ U_ level)
    (γ : Slots n) : recFieldSet Δ index block γ ⊆ U_ level :=
  Δ.pi_subset_type hdoms (fun s => hblock (index s)) γ

theorem recFieldSet_mem_type {Δ : SemTele n b} (hdoms : Δ.DomsIn level)
    {index : Dom b} {block : ZFSet} (hblock : ∀ key, fibreOp block key ∈ U_ level)
    (γ : Slots n) : recFieldSet Δ index block γ ∈ U_ level :=
  Δ.pi_mem_type hdoms (fun current => hblock (index current)) γ

theorem CtorCode.support_card_lt {code : CtorCode.{u} n}
    (hdoms : code.DomsIn level) (γ : Slots n) :
    Cardinal.mk (code.Support γ) < Cardinal.lift.{u + 1} (Cardinal.inaccessible.{u} level) := by
  have hκ := Cardinal.inaccessible_isInaccessible.{u} level
  have hreg : (Cardinal.lift.{u + 1} (Cardinal.inaccessible.{u} level)).IsRegular := hκ.isRegular.lift
  have hbase : Cardinal.mk ({γ} : Set (Slots n)) < Cardinal.lift.{u + 1} (Cardinal.inaccessible.{u} level) := by
    rw [Cardinal.mk_singleton]
    exact Cardinal.one_lt_aleph0.trans_le hreg.aleph0_le
  rw [CtorCode.Support.cardinalMk]
  refine Cardinal.sum_lt_of_isRegular hreg
    (Reachable.card_lt hκ hdoms.ordinary hbase) fun final => ?_
  exact Cardinal.sum_lt_lift_of_isRegular hreg
    (lt_of_lt_of_le (by simp) hreg.aleph0_le)
    fun f => Reachable.card_lt hκ (hdoms.recursive f) (by simpa using hbase)

theorem CtorCode.argSet_mem_type {code : CtorCode n}
    (hdoms : code.DomsIn level) {block : ZFSet}
    (hblock : ∀ key, fibreOp block key ∈ U_ level) (γ : Slots n) :
    code.argSet block γ ∈ U_ level :=
  code.ordinary.sigma_mem_type hdoms.ordinary
    (fun final => tupleSet_mem_vonNeumann Cardinal.ord_inaccessible_isSuccLimit
      fun f => recFieldSet_mem_type (hdoms.recursive f) hblock final) γ

abbrev CodesDomsIn (level : Nat) (codes : (s : Fin m) → Fin (nctors s) → CtorCode n) : Prop :=
  ∀ s c, (codes s c).DomsIn level

theorem image_snd_indOp_mem_type (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (hdoms : CodesDomsIn level codes)
    {block : ZFSet} (hblock : ∀ key, fibreOp block key ∈ U_ level)
    (γ : Slots n) : image snd (indOp codes γ block) ∈ U_ level := by
  have hvalues (s : Fin m) (c : Fin (nctors s)) :
      image (entryValue (tagOf s c)) ((codes s c).argSet block γ) ∈ U_ level :=
    have hargs := CtorCode.argSet_mem_type (hdoms s c) hblock γ
    image_mem_type hargs fun vargs hvargs =>
      pair_mem_type (numeral_mem_type level _) (mem_type_of_mem hargs hvargs)
  have hvaluesEq : image snd (indOp codes γ block) =
      ⋃₀ range (fun s => ⋃₀ range fun c =>
        image (entryValue (tagOf s c)) ((codes s c).argSet block γ)) := by
    ext value
    simp [indOp, entry_eq]
  rw [hvaluesEq]
  exact sUnion_mem_type (range_mem_type
    (Cardinal.mk_lt_aleph0.trans (Cardinal.inaccessible_isInaccessible _).aleph0_lt) fun s =>
      sUnion_mem_type (range_mem_type
        (Cardinal.mk_lt_aleph0.trans (Cardinal.inaccessible_isInaccessible _).aleph0_lt) (hvalues s)))

noncomputable def bodyOp (codes : (s : Fin m) → Fin (nctors s) → CtorCode n) (bound : ZFSet)
    (γ : Slots n) (body : ZFSet) : ZFSet :=
  image snd (indOp codes γ (prod bound body))

theorem bodyOp_mono {codes : (s : Fin m) → Fin (nctors s) → CtorCode n} {bound : ZFSet}
    {γ : Slots n} {body body' : ZFSet} (h : body ⊆ body') :
    bodyOp codes bound γ body ⊆ bodyOp codes bound γ body' := by
  intro value hvalue
  have ⟨entry', hentry, heq⟩ := mem_image.mp hvalue
  refine mem_image.mpr ⟨entry', indOp_mono ?_ hentry, heq⟩
  intro member hmember
  have ⟨key, hkey, value', hvalue', hpair⟩ := mem_prod.mp hmember
  exact mem_prod.mpr ⟨key, hkey, value', h hvalue', hpair⟩

theorem bodyOp_mem_type {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    (hdoms : CodesDomsIn level codes)
    (bound : ZFSet) (γ : Slots n) {body : ZFSet} (hbody : body ∈ U_ level) :
    bodyOp codes bound γ body ∈ U_ level :=
  image_snd_indOp_mem_type codes hdoms (fun _ =>
    mem_type_of_subset hbody fun _ hvalue =>
      (pair_mem_prod.mp (mem_fibre.mp hvalue)).2) γ

theorem exists_bodyOp_closed {codes : (s : Fin m) → Fin (nctors s) → CtorCode.{u} n}
    (hdoms : CodesDomsIn level codes)
    (bound : ZFSet) (γ : Slots n) :
    ∃ body, body ∈ U_ level ∧ bodyOp codes bound γ body ⊆ body := by
  let I := (s : Fin m) × (c : Fin (nctors s)) × (codes s c).Support γ
  have hκ := Cardinal.inaccessible_isInaccessible.{u} level
  have hI : Cardinal.mk I < Cardinal.lift.{u + 1} (Cardinal.inaccessible.{u} level) := by
    simp only [I, Cardinal.mk_sigma]
    refine Cardinal.sum_lt_lift_of_isRegular hκ.isRegular.lift
      (lt_of_lt_of_le (by simp) hκ.isRegular.lift.aleph0_le) fun s => ?_
    exact Cardinal.sum_lt_lift_of_isRegular hκ.isRegular.lift
      (lt_of_lt_of_le (by simp) hκ.isRegular.lift.aleph0_le)
      fun c => CtorCode.support_card_lt (hdoms s c) γ
  have hsmall : Cardinal.lift.{u + 1} (Cardinal.mk (Shrink.{u} I)) <
      Cardinal.lift.{u + 1} (Cardinal.inaccessible.{u} level) := by
    rwa [Cardinal.lift_mk_shrink'' I]
  refine exists_closed_of_indexed_support hκ
    (fun _ _ h => bodyOp_mono h)
    (fun _ hbody => bodyOp_mem_type hdoms bound γ hbody)
    (ι := I) (Cardinal.lift_lt.mp hsmall) ?_
  intro body value hvalue
  obtain ⟨entry', hentry, heq⟩ := mem_image.mp hvalue
  obtain ⟨s, c, vargs, hargs, hentry'⟩ := mem_indOp.mp hentry
  let read : I → ZFSet := fun point =>
    snd ((codes point.1 point.2.1).readSupport γ vargs point.2.2)
  let small := (range read).sep (· ∈ body)
  refine ⟨small, fun _ h => (mem_sep.mp h).2, ⟨read, sep_subset⟩, ?_⟩
  refine mem_image.mpr ⟨entry', mem_indOp.mpr ⟨s, c, vargs, ?_, hentry'⟩, heq⟩
  apply CtorCode.argSet_mem_of_support _ γ vargs hargs
  intro point hpoint
  obtain ⟨key, hkey, member, hmember, hpair⟩ := mem_prod.mp hpoint
  have hsnd : read ⟨s, c, point⟩ = member := by simp [read, hpair]
  exact mem_prod.mpr ⟨key, hkey, member,
    mem_sep.mpr ⟨hsnd ▸ mem_range_self (f := read) ⟨s, c, point⟩, hmember⟩, hpair⟩

theorem fibreOp_indSet_mem_type {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    (hdoms : CodesDomsIn level codes)
    {slots : Slots n}
    (hmaps : Set.MapsTo (indOp codes slots) (Set.Iic (U_ b)) (Set.Iic (U_ b)))
    (key : ZFSet) : fibreOp (indSet codes (U_ b) slots) key ∈ U_ level := by
  have ⟨body, hbody, hclosed⟩ := exists_bodyOp_closed hdoms (U_ b) slots
  have hind : indSet codes (U_ b) slots ⊆ prod (U_ b) body :=
    lfp_le_of_inter hmaps (fun _ _ h => indOp_mono h) fun entry' hentry => by
      have ⟨hentry, hbound⟩ := mem_inter.mp hentry
      have hpair : entry' = pair (fst entry') (snd entry') := by
        obtain ⟨_, _, _, _, rfl⟩ := mem_indOp.mp hentry
        simp [entry_eq]
      have hbody' := hclosed (mem_image.mpr ⟨entry', hentry, rfl⟩)
      rw [hpair]
      exact pair_mem_prod.mpr ⟨fst_mem_type hbound, hbody'⟩
  exact mem_type_of_subset hbody fun _ hvalue =>
    (pair_mem_prod.mp (hind (mem_fibre.mp hvalue))).2

theorem CtorCode.argSet_subset_type {code : CtorCode n}
    (hdoms : code.DomsIn level)
    {block : ZFSet} (hblock : ∀ key, fibreOp block key ⊆ U_ level) (γ : Slots n) :
    code.argSet block γ ⊆ U_ level :=
  code.ordinary.sigma_subset_type hdoms.ordinary (fun final _ hv =>
    let ⟨hvalues, heq⟩ := mem_tupleSet.mp hv
    heq ▸ tuple_mem_vonNeumann Cardinal.ord_inaccessible_isSuccLimit
      (fun f => recFieldSet_subset_type (hdoms.recursive f) hblock final (hvalues f))) γ

theorem indOp_subset_type {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    (hdoms : CodesDomsIn level codes)
    {block : ZFSet} (hblock : ∀ key, fibreOp block key ⊆ U_ level)
    (hindex : ∀ s c (γ : Slots n) vargs, (codes s c).targetIndex γ vargs ∈ U_ level)
    (γ : Slots n) : indOp codes γ block ⊆ U_ level := fun _ hz => by
  obtain ⟨s, c, vargs, hargs, rfl⟩ := mem_indOp.mp hz
  exact entry_mem_type (hindex s c γ vargs)
    (CtorCode.argSet_subset_type (hdoms s c) hblock γ hargs)

theorem indOp_mapsTo {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    (hdoms : CodesDomsIn level codes)
    (hindex : ∀ s c (γ : Slots n) vargs, (codes s c).targetIndex γ vargs ∈ U_ level)
    (γ : Slots n) :
    Set.MapsTo (indOp codes γ) (Set.Iic (U_ level)) (Set.Iic (U_ level)) := fun _ hblock =>
  indOp_subset_type hdoms (fun key => fibreOp_subset_type hblock key) hindex γ

end Metalean
