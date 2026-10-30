/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.InductiveBlock

public section

universe u

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
