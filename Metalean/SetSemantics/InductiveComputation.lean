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
  {block bound motive step graph minors vargs : ZFSet} {γ : Slots n}
  {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}

theorem dom_recGraph (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hstep : StepSound codes (indSet codes bound γ) motive step γ) :
    dom (recGraph codes bound motive step γ) = indSet codes bound γ :=
  subset_antisymm (recGraph_isApprox hmaps).memBlock (dom_recGraph_eq hmaps hstep)

theorem recGraph_entry (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hstep : StepSound codes (indSet codes bound γ) motive step γ)
    (hargs : vargs ∈ (codes s c).argSet (indSet codes bound γ) γ) :
    app (recGraph codes bound motive step γ)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs)
      = app step (app (blockMapGraph (indSet codes bound γ)
          (recGraph codes bound motive step γ) γ codes)
          (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs)) := by
  refine (recGraph_isApprox hmaps).appEq _ ?_
  rw [dom_recGraph hmaps hstep, ← indSet_unfold hmaps]
  exact mem_indOp.mpr ⟨s, c, vargs, hargs, rfl⟩

theorem app_stepGraph (hargs : vargs ∈ (codes s c).ihArgSet block motive γ) :
    app (stepGraph level block motive γ minors codes)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs)
      = (codes s c).applyMinor level γ [zf|minors $(encode (tagOf s c))] vargs :=
  app_pairGraph hargs

theorem recGraph_iota
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hstep : StepSound codes (indSet codes bound γ) motive
      (stepGraph level (indSet codes bound γ) motive γ minors codes) γ)
    (hargs : vargs ∈ (codes s c).argSet (indSet codes bound γ) γ) :
    app (recGraph codes bound motive
        (stepGraph level (indSet codes bound γ) motive γ minors codes) γ)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs)
      = (codes s c).applyMinor level γ [zf|minors $(encode (tagOf s c))]
          ((codes s c).argMap (recGraph codes bound motive
            (stepGraph level (indSet codes bound γ) motive γ minors codes) γ)
            γ vargs) := by
  set graph := recGraph codes bound motive
    (stepGraph level (indSet codes bound γ) motive γ minors codes) γ
  have hmapped : (codes s c).argMap graph γ vargs
      ∈ (codes s c).ihArgSet (indSet codes bound γ) motive γ :=
    CtorCode.argMap_mem (fun _ hx => recGraph_app_mem hmaps
      (by rwa [dom_recGraph hmaps hstep])) _ γ vargs hargs
  rw [recGraph_entry hmaps hstep hargs, app_blockMapGraph hargs,
    app_stepGraph hmapped]

theorem entry_mem_indSet (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hargs : vargs ∈ (codes s c).argSet (indSet codes bound γ) γ) :
    entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs ∈ indSet codes bound γ :=
  indSet_unfold hmaps ▸ mem_indOp.mpr ⟨s, c, vargs, hargs, rfl⟩

end Metalean
