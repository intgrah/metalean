/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Batteries.Data.Fin.Coding
public import Metalean.SetSemantics.ConstructorValue
public import Metalean.SetTheory.ZFC.Recursion

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {n m level : Nat} {nctors : Fin m → Nat} {s : Fin m} {c : Fin (nctors s)}
  {block blockW bound motive step graph minors z vargs : ZFSet}
  {γ : Slots n} {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
  {args : CtorCode n → ZFSet}
  {emit val : CtorCode n → Nat → ZFSet → ZFSet}

def tagOf (s : Fin m) (c : Fin (nctors s)) : Nat :=
  (Fin.encodeSigma nctors ⟨s, c⟩).val

theorem tagOf_injective {s₁ s₂ : Fin m} {c₁ : Fin (nctors s₁)} {c₂ : Fin (nctors s₂)}
    (h : tagOf s₁ c₁ = tagOf s₂ c₂) :
    (⟨s₁, c₁⟩ : (s : Fin m) × Fin (nctors s)) = ⟨s₂, c₂⟩ := by
  simpa using congrArg (Fin.decodeSigma nctors)
    (Fin.ext h : Fin.encodeSigma nctors ⟨s₁, c₁⟩ = Fin.encodeSigma nctors ⟨s₂, c₂⟩)

noncomputable def tagGraph (args : CtorCode.{u} n → ZFSet.{u})
    (emit : CtorCode.{u} n → Nat → ZFSet.{u} → ZFSet.{u})
    (codes : (s : Fin m) → Fin (nctors s) → CtorCode.{u} n) : ZFSet.{u} :=
  ⋃₀ range fun s => ⋃₀ range fun c =>
    image (emit (codes s c) (tagOf s c)) (args (codes s c))

theorem mem_tagGraph :
    z ∈ tagGraph args emit codes ↔
      ∃ s c, ∃ vargs ∈ args (codes s c), emit (codes s c) (tagOf s c) vargs = z := by
  simp [tagGraph]

noncomputable def pairGraph (γ : Slots.{u} n) (args : CtorCode.{u} n → ZFSet.{u})
    (val : CtorCode.{u} n → Nat → ZFSet.{u} → ZFSet.{u})
    (codes : (s : Fin m) → Fin (nctors s) → CtorCode.{u} n) : ZFSet.{u} :=
  range fun p : (s : Fin m) × (c : Fin (nctors s)) × args (codes s c) =>
    pair (entry ((codes p.1 p.2.1).targetIndex γ p.2.2) (tagOf p.1 p.2.1) p.2.2)
      (val (codes p.1 p.2.1) (tagOf p.1 p.2.1) p.2.2)

theorem pairGraph_isFunc :
    IsFunc (dom (pairGraph γ args val codes))
      (image snd (pairGraph γ args val codes)) (pairGraph γ args val codes) := by
  apply isFunc_range_pair
  intro ⟨s₁, c₁, a₁⟩ ⟨s₂, c₂, a₂⟩ heq
  cases tagOf_injective (entry_tag_eq heq)
  cases Subtype.ext (entry_args_eq heq)
  rfl

theorem app_pairGraph (hargs : vargs ∈ args (codes s c)) :
    app (pairGraph γ args val codes)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs) =
      val (codes s c) (tagOf s c) vargs :=
  pairGraph_isFunc.app_eq (mem_range.mpr ⟨⟨s, c, vargs, hargs⟩, rfl⟩)

noncomputable def indOp (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (γ : Slots n) (block : ZFSet) : ZFSet :=
  tagGraph (fun code => code.argSet block γ)
    (fun code tag vargs => entry (code.targetIndex γ vargs) tag vargs) codes

theorem mem_indOp :
    z ∈ indOp codes γ block ↔
      ∃ s c, ∃ vargs ∈ (codes s c).argSet block γ,
        entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs = z :=
  mem_tagGraph

noncomputable def blockPredecessorRel (block : ZFSet) (γ : Slots n)
    (codes : (s : Fin m) → Fin (nctors s) → CtorCode n) : ZFSet :=
  ⋃₀ tagGraph (fun code => code.argSet block γ)
    (fun code tag vargs => image
      (fun predecessor => [zf|(predecessor, $(entry (code.targetIndex γ vargs) tag vargs))])
      (code.predecessors γ vargs))
    codes

theorem mem_blockPredecessorRel {predecessor current : ZFSet} :
    [zf|(predecessor, current)] ∈ blockPredecessorRel block γ codes ↔
      ∃ s c, ∃ vargs ∈ (codes s c).argSet block γ,
        predecessor ∈ (codes s c).predecessors γ vargs ∧
        current = entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs := by
  constructor
  · intro h
    have ⟨edges, hedges, hedge⟩ := mem_sUnion.mp h
    obtain ⟨s, c, vargs, hargs, rfl⟩ := mem_tagGraph.mp hedges
    have ⟨_, hpredecessor, heq⟩ := mem_image.mp hedge
    have ⟨rfl, rfl⟩ := pair_inj.mp heq
    exact ⟨s, c, vargs, hargs, hpredecessor, rfl⟩
  · intro ⟨s, c, vargs, hargs, hpredecessor, hcurrent⟩
    rw [hcurrent]
    exact mem_sUnion.mpr ⟨_, mem_tagGraph.mpr ⟨s, c, vargs, hargs, rfl⟩,
      mem_image.mpr ⟨predecessor, hpredecessor, rfl⟩⟩

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

noncomputable def blockMapGraph (block graph : ZFSet) (γ : Slots n) :
    ((s : Fin m) → Fin (nctors s) → CtorCode n) → ZFSet :=
  pairGraph γ (fun code => code.argSet block γ)
    fun code tag vargs =>
      entry (code.targetIndex γ (code.argMap graph γ vargs)) tag (code.argMap graph γ vargs)

noncomputable def stepGraph (level : Nat) (block motive : ZFSet) (γ : Slots n)
    (minors : ZFSet) : ((s : Fin m) → Fin (nctors s) → CtorCode n) → ZFSet :=
  pairGraph γ (fun code => code.ihArgSet block motive γ)
    fun code tag vargs => code.applyMinor level γ [zf|minors $(encode tag)] vargs

theorem indOp_inter {block₁ block₂ : ZFSet}
    (hw : ∀ value, value ∈ block₁ → value ∈ block₂ → value ∈ blockW)
    (hz₁ : z ∈ indOp codes γ block₁) (hz₂ : z ∈ indOp codes γ block₂) :
    z ∈ indOp codes γ blockW := by
  obtain ⟨s, c, vargs, hargs₁, hargs₂, rfl⟩ := mem_indOp_inter hz₁ hz₂
  exact mem_indOp.mpr ⟨s, c, vargs, CtorCode.argSet_inter hw _ γ vargs hargs₁ hargs₂, rfl⟩

theorem app_blockMapGraph (hargs : vargs ∈ (codes s c).argSet block γ) :
    app (blockMapGraph block graph γ codes)
        (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs) =
      entry ((codes s c).targetIndex γ ((codes s c).argMap graph γ vargs)) (tagOf s c)
        ((codes s c).argMap graph γ vargs) :=
  app_pairGraph hargs

theorem blockMapGraph_app_cand {block₁ block₂ : ZFSet}
    (hz₁ : z ∈ indOp codes γ block₁) (hz₂ : z ∈ indOp codes γ block₂) :
    app (blockMapGraph block₁ graph γ codes) z = app (blockMapGraph block₂ graph γ codes) z := by
  obtain ⟨_, _, _, hargs₁, hargs₂, rfl⟩ := mem_indOp_inter hz₁ hz₂
  rw [app_blockMapGraph hargs₁, app_blockMapGraph hargs₂]

theorem blockMapGraph_app_congr {inner outer graph₁ graph₂ : ZFSet}
    (hagree : ∀ value ∈ inner, app graph₁ value = app graph₂ value)
    (hinner : z ∈ indOp codes γ inner) (houter : z ∈ indOp codes γ outer) :
    app (blockMapGraph outer graph₁ γ codes) z = app (blockMapGraph outer graph₂ γ codes) z := by
  obtain ⟨_, _, vargs, hinnerArgs, hargs, rfl⟩ := mem_indOp_inter hinner houter
  rw [app_blockMapGraph hargs, app_blockMapGraph hargs,
    CtorCode.argMap_congr hagree _ γ vargs hinnerArgs]

def StepSound (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (block motive step : ZFSet) (γ : Slots n) : Prop :=
  ∀ s c, ∀ vargs ∈ (codes s c).ihArgSet block motive γ,
  app step (entry ((codes s c).targetIndex γ vargs) (tagOf s c) vargs)
    ∈ fibreOp motive
      (entry ((codes s c).targetIndex γ ((codes s c).forgetIhs vargs)) (tagOf s c)
        ((codes s c).forgetIhs vargs))

noncomputable def recGraph (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (bound motive step : ZFSet) (γ : Slots n) : ZFSet :=
  ZFSet.recGraph (indOp codes γ) bound (fibreOp motive)
    (fun graph z => app step (app (blockMapGraph (indSet codes bound γ) graph γ codes) z))

theorem indOp_monotoneOn {bound : ZFSet} :
    MonotoneOn (indOp codes γ) (Set.Iic bound) :=
  fun _ _ _ _ h => indOp_mono h

theorem indSet_unfold {bound : ZFSet}
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound)) :
    indOp codes γ (indSet codes bound γ) = indSet codes bound γ :=
  lfp_fixed hmaps indOp_monotoneOn

theorem blockMapGraph_app_mem {inner outer graph motive step : ZFSet} (hsub : inner ⊆ outer)
    (hgraph : ∀ value ∈ inner, app graph value ∈ fibreOp motive value)
    (hstep : StepSound codes outer motive step γ)
    (z : ZFSet) (hz : z ∈ indOp codes γ inner) :
    app step (app (blockMapGraph inner graph γ codes) z) ∈ fibreOp motive z := by
  obtain ⟨s, c, vargs, hargs, rfl⟩ := mem_indOp.mp hz
  have hmem : (codes s c).argMap graph γ vargs ∈ (codes s c).ihArgSet outer motive γ :=
    CtorCode.ihArgSet_mono hsub motive _ γ (CtorCode.argMap_mem hgraph _ γ vargs hargs)
  have h := hstep s c _ hmem
  rw [CtorCode.forgetIhs_argMap _ γ vargs hargs] at h
  rwa [app_blockMapGraph hargs]

theorem recGraph_isApprox
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound)) :
    ZFSet.IsApprox (indOp codes γ) bound (fibreOp motive)
      (fun graph z => app step (app (blockMapGraph (indSet codes bound γ) graph γ codes) z))
      (recGraph codes bound motive step γ) :=
  ZFSet.recGraph_isApprox hmaps indOp_monotoneOn
    (fun _ _ _ hz => indOp_inter (fun _ h₁ h₂ => mem_inter.mpr ⟨h₁, h₂⟩)
      (mem_inter.mp hz).1 (mem_inter.mp hz).2)
    (fun _ _ _ _ hagree hz hblock => congrArg (app step)
      (blockMapGraph_app_congr hagree hz ((indSet_unfold hmaps).symm ▸ hblock)))

theorem dom_recGraph
    (hmaps : Set.MapsTo (indOp codes γ) (Set.Iic bound) (Set.Iic bound))
    (hstep : StepSound codes (indSet codes bound γ) motive step γ) :
    dom (recGraph codes bound motive step γ) = indSet codes bound γ := by
  apply ZFSet.dom_recGraph
    (F := fun graph z => app step (app (blockMapGraph (indSet codes bound γ) graph γ codes) z))
    hmaps indOp_monotoneOn
    (fun _ _ _ hz => indOp_inter (fun _ h₁ h₂ => mem_inter.mpr ⟨h₁, h₂⟩)
      (mem_inter.mp hz).1 (mem_inter.mp hz).2)
    (fun _ _ _ _ hagree hz hblock => congrArg (app step)
      (blockMapGraph_app_congr hagree hz ((indSet_unfold hmaps).symm ▸ hblock)))
  intro inner hsub graph hgraph z hz
  have h := blockMapGraph_app_mem hsub hgraph hstep z hz
  rwa [blockMapGraph_app_cand hz (indOp_mono hsub hz)] at h

end Metalean
