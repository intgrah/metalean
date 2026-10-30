/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Batteries.Data.Fin.Coding
public import Metalean.SetSemantics.Inductive.Constructor
public import Metalean.SetTheory.ZFC.Recursion

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {n m level : Nat} {nctors : Fin m → Nat} {s : Fin m} {c : Fin (nctors s)}
  {block blockW bound motive step graph z vargs : ZFSet}
  {minors : (s : Fin m) → Fin (nctors s) → ZFSet}
  {γ : Slots n} {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}

def tagOf (s : Fin m) (c : Fin (nctors s)) : Nat :=
  (Fin.encodeSigma nctors ⟨s, c⟩).val

theorem tagOf_injective {s₁ s₂ : Fin m} {c₁ : Fin (nctors s₁)} {c₂ : Fin (nctors s₂)}
    (h : tagOf s₁ c₁ = tagOf s₂ c₂) :
    (⟨s₁, c₁⟩ : (s : Fin m) × Fin (nctors s)) = ⟨s₂, c₂⟩ := by
  simpa using congrArg (Fin.decodeSigma nctors)
    (Fin.ext h : Fin.encodeSigma nctors ⟨s₁, c₁⟩ = Fin.encodeSigma nctors ⟨s₂, c₂⟩)

noncomputable def indOp (codes : (s : Fin m) → Fin (nctors s) → CtorCode.{u} n)
    (γ : Slots.{u} n) (block : ZFSet.{u}) : ZFSet.{u} :=
  range fun p : (s : Fin m) × (c : Fin (nctors s)) × (codes s c).argSet block γ =>
    entry ((codes p.1 p.2.1).targetIndex γ p.2.2) (tagOf p.1 p.2.1) p.2.2

theorem mem_indOp :
    z ∈ indOp codes γ block ↔
      ∃ s c, ∃ vargs ∈ (codes s c).argSet block γ,
        entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs = z := by
  simp [indOp]

theorem mem_indOp_inter {block₁ block₂ : ZFSet}
    (hz₁ : z ∈ indOp codes γ block₁)
    (hz₂ : z ∈ indOp codes γ block₂) :
    ∃ s c, ∃ vargs ∈ (codes s c).argSet block₁ γ,
      vargs ∈ (codes s c).argSet block₂ γ ∧
        entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs = z := by
  obtain ⟨_, _, _, hargs₁, rfl⟩ := mem_indOp.mp hz₁
  have ⟨_, _, _, hargs₂, heq⟩ := mem_indOp.mp hz₂
  cases tagOf_injective (entry_tag_eq heq)
  cases entry_args_eq heq
  exact ⟨_, _, _, hargs₁, hargs₂, rfl⟩

theorem indOp_mono {block₁ block₂ : ZFSet} (h : block₁ ⊆ block₂) :
    indOp codes γ block₁ ⊆ indOp codes γ block₂ := fun _ hz =>
  have ⟨s, c, vargs, hargs, heq⟩ := mem_indOp.mp hz
  mem_indOp.mpr ⟨s, c, vargs, CtorCode.argSet_mono h _ γ hargs, heq⟩

noncomputable def indSet
    (codes : (s : Fin m) → Fin (nctors s) → CtorCode n) (bound : ZFSet) (γ : Slots n) : ZFSet :=
  lfp bound (indOp codes γ)

noncomputable def stepGraph (level : Nat) (block graph : ZFSet.{u}) (γ : Slots.{u} n)
    (minors : (s : Fin m) → Fin (nctors s) → ZFSet.{u}) (codes : (s : Fin m) → Fin (nctors s) → CtorCode.{u} n) : ZFSet.{u} :=
  range fun p : (s : Fin m) × (c : Fin (nctors s)) × (codes s c).argSet block γ =>
    pair (entry ((codes p.1 p.2.1).targetIndex γ p.2.2) (tagOf p.1 p.2.1) p.2.2)
      ((codes p.1 p.2.1).applyMinor level graph γ
        (minors p.1 p.2.1) p.2.2)

theorem app_stepGraph (hargs : vargs ∈ (codes s c).argSet block γ) :
    app (stepGraph level block graph γ minors codes)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs) =
      (codes s c).applyMinor level graph γ (minors s c) vargs := by
  have hkey : Function.Injective
      (fun p : (s : Fin m) × (c : Fin (nctors s)) × (codes s c).argSet block γ =>
        entry ((codes p.1 p.2.1).targetIndex γ p.2.2) (tagOf p.1 p.2.1) p.2.2) := by
    intro ⟨s₁, c₁, a₁⟩ ⟨s₂, c₂, a₂⟩ heq
    cases tagOf_injective (entry_tag_eq heq)
    cases Subtype.ext (entry_args_eq heq)
    rfl
  exact (isFunc_range_pair _ _ hkey).app_eq (mem_range.mpr ⟨⟨s, c, vargs, hargs⟩, rfl⟩)

theorem indOp_inter {block₁ block₂ : ZFSet}
    (hw : ∀ value, value ∈ block₁ → value ∈ block₂ → value ∈ blockW)
    (hz₁ : z ∈ indOp codes γ block₁) (hz₂ : z ∈ indOp codes γ block₂) :
    z ∈ indOp codes γ blockW := by
  obtain ⟨s, c, vargs, hargs₁, hargs₂, rfl⟩ := mem_indOp_inter hz₁ hz₂
  exact mem_indOp.mpr ⟨s, c, vargs, CtorCode.argSet_inter hw _ γ vargs hargs₁ hargs₂, rfl⟩

theorem stepGraph_app_congr {inner outer graph₁ graph₂ : ZFSet}
    (hagree : ∀ value ∈ inner, app graph₁ value = app graph₂ value)
    (hinner : z ∈ indOp codes γ inner) (houter : z ∈ indOp codes γ outer) :
    app (stepGraph level outer graph₁ γ minors codes) z =
      app (stepGraph level outer graph₂ γ minors codes) z := by
  obtain ⟨_, _, vargs, hinnerArgs, hargs, rfl⟩ := mem_indOp_inter hinner houter
  rw [app_stepGraph hargs, app_stepGraph hargs]
  exact CtorCode.applyMinor_congr hagree _ γ _ vargs hinnerArgs

def StepSound (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (block motive : ZFSet) (level : Nat)
    (minors : (s : Fin m) → Fin (nctors s) → ZFSet) (γ : Slots n) : Prop :=
  ∀ inner ⊆ block, ∀ graph, (∀ value ∈ inner, app graph value ∈ fibreOp motive value) →
  ∀ s c, ∀ vargs ∈ (codes s c).argSet inner γ,
  (codes s c).applyMinor level graph γ (minors s c) vargs ∈
    fibreOp motive (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs)

noncomputable def recGraph (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (bound motive : ZFSet) (level : Nat)
    (minors : (s : Fin m) → Fin (nctors s) → ZFSet) (γ : Slots n) : ZFSet :=
  ZFSet.recGraph (indOp codes γ) bound (fibreOp motive)
    (fun graph z => app (stepGraph level (indSet codes bound γ) graph γ minors codes) z)

theorem indOp_monotoneOn {bound : ZFSet} :
    MonotoneOn (indOp codes γ) (Set.Iic bound) :=
  fun _ _ _ _ h => indOp_mono h

theorem indSet_unfold {bound : ZFSet}
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound)) :
    indOp codes γ (indSet codes bound γ) = indSet codes bound γ :=
  lfp_fixed hmaps indOp_monotoneOn

theorem recGraph_isApprox
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound)) :
    ZFSet.IsApprox (indOp codes γ) bound (fibreOp motive)
      (fun graph z => app (stepGraph level (indSet codes bound γ) graph γ minors codes) z)
      (recGraph codes bound motive level minors γ) :=
  ZFSet.recGraph_isApprox hmaps indOp_monotoneOn
    (fun _ _ _ hz => indOp_inter (fun _ h₁ h₂ => mem_inter.mpr ⟨h₁, h₂⟩)
      (mem_inter.mp hz).1 (mem_inter.mp hz).2)
    (fun _ _ _ _ hagree hz hblock =>
      stepGraph_app_congr hagree hz ((indSet_unfold hmaps).symm ▸ hblock))

theorem dom_recGraph
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hstep : StepSound codes (indSet codes bound γ) motive level minors γ) :
    dom (recGraph codes bound motive level minors γ) = indSet codes bound γ := by
  apply ZFSet.dom_recGraph
    (F := fun graph z => app (stepGraph level (indSet codes bound γ) graph γ minors codes) z)
    hmaps indOp_monotoneOn
    (fun _ _ _ hz => indOp_inter (fun _ h₁ h₂ => mem_inter.mpr ⟨h₁, h₂⟩)
      (mem_inter.mp hz).1 (mem_inter.mp hz).2)
    (fun _ _ _ _ hagree hz hblock =>
      stepGraph_app_congr hagree hz ((indSet_unfold hmaps).symm ▸ hblock))
  intro inner hsub graph hgraph z hz
  obtain ⟨s, c, vargs, hargs, rfl⟩ := mem_indOp.mp hz
  have hargs' : vargs ∈ (codes s c).argSet (indSet codes bound γ) γ :=
    CtorCode.argSet_mono hsub _ γ hargs
  rw [app_stepGraph hargs']
  exact hstep inner hsub graph hgraph s c vargs hargs

end Metalean

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {n m level : Nat} {nctors : Fin m → Nat} {s : Fin m} {c : Fin (nctors s)}
  {block bound motive step graph vargs : ZFSet}
  {minors : (s : Fin m) → Fin (nctors s) → ZFSet} {γ : Slots n}
  {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}

theorem recGraph_iota
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hstep : StepSound codes (indSet codes bound γ) motive level minors γ)
    (hargs : vargs ∈ (codes s c).argSet (indSet codes bound γ) γ) :
    app (recGraph codes bound motive level minors γ)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs) =
      (codes s c).applyMinor level (recGraph codes bound motive level minors γ) γ
        (minors s c) vargs := by
  have hdom : entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs ∈
      dom (recGraph codes bound motive level minors γ) := by
    rw [dom_recGraph hmaps hstep, ← indSet_unfold hmaps]
    exact mem_indOp.mpr ⟨s, c, vargs, hargs, rfl⟩
  rw [(recGraph_isApprox hmaps).appEq _ hdom, app_stepGraph hargs]

theorem recGraph_iota_of_empty
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hargs : vargs ∈ (codes s c).argSet ∅ γ)
    (hvalue : (codes s c).applyMinor level ∅ γ (minors s c) vargs ∈
      fibreOp motive (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs)) :
    app (recGraph codes bound motive level minors γ)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs) =
      (codes s c).applyMinor level ∅ γ (minors s c) vargs := by
  have hargs' : vargs ∈ (codes s c).argSet (indSet codes bound γ) γ :=
    CtorCode.argSet_mono (empty_subset _) _ γ hargs
  have h := ZFSet.recGraph_app_of_empty
    (F := fun graph z => app (stepGraph level (indSet codes bound γ) graph γ minors codes) z)
    hmaps indOp_monotoneOn
    (fun _ _ _ hz => indOp_inter (fun _ h₁ h₂ => mem_inter.mpr ⟨h₁, h₂⟩)
      (mem_inter.mp hz).1 (mem_inter.mp hz).2)
    (fun _ _ _ _ hagree hz hblock =>
      stepGraph_app_congr hagree hz ((indSet_unfold hmaps).symm ▸ hblock))
    (mem_indOp.mpr ⟨s, c, vargs, hargs, rfl⟩)
    (by rwa [app_stepGraph hargs'])
  rwa [app_stepGraph hargs'] at h

theorem entry_mem_indSet (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hargs : vargs ∈ (codes s c).argSet (indSet codes bound γ) γ) :
    entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs ∈ indSet codes bound γ :=
  indSet_unfold hmaps ▸ mem_indOp.mpr ⟨s, c, vargs, hargs, rfl⟩

end Metalean
