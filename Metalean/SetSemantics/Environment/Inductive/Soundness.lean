/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model

@[expose] public section

universe u

namespace Metalean

open CategoryTheory ZFSet

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₁ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0} {witness : InductiveModel.{u} ι}

def Inductive.RulesSound (E₁ : Env ζ₁) (ε₁ : Atom ζ₁ 0 → ZFSet.{u})
    (η : Head ζ₁ (.inductive ι)) (ls : Fin ι.nlevels → Level 0) : Prop :=
  ∀ {ζ₂ : Sigs} {E₂ : Env ζ₂} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
    (pre : E₁.as ⟶ E₂.as), AtomsMap pre.sigs ε₁ ε₂ →
    Inductive.SemRules ε₂ ![] (E₂.get (η.map pre.sigs)).block (η.map pre.sigs) ls

theorem Inductive.RulesSound.map (h : Inductive.RulesSound E₁ ε₁ η ls)
    (pre : E₁.as ⟶ E₂.as) (hatoms₁ : AtomsMap pre.sigs ε₁ ε₂) :
    Inductive.RulesSound E₂ ε₂ (η.map pre.sigs) ls := fun {ζ₃ E₃ ε₃} suffix hatoms₂ => by
  have hcomp : AtomsMap (pre ≫ suffix).sigs ε₁ ε₃ := by
    simpa [dsimp% Env.forget.map_comp pre suffix] using hatoms₁.trans hatoms₂
  have hmap : (η.map pre.sigs).map suffix.sigs = η.map (pre ≫ suffix).sigs :=
    ((Env.forget ⋙ Head.functor _).map_comp_apply pre suffix η).symm
  simpa [hmap] using h (pre ≫ suffix) hcomp

structure InductiveModel.Sound (E₁ : Env ζ₁) (ε : Atom ζ₁ 0 → ZFSet.{u})
    (I : Inductive ζ₁ ι) (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level 0) (witness : InductiveModel.{u} ι) : Prop where
  block_eq : (E₁.get η).block = I
  realizes : witness.Interprets ε ![] I ls
  sortAtom (s : Fin ι.nsorts) (vps : Slots ι.nparams) (vis : Slots (ι.nindices s)) :
    ε (.ind η s ls vps vis) = witness.sortValue s vps vis
  rules : Inductive.RulesSound E₁ ε η ls

namespace InductiveModel.Sound

theorem uniqueCtor_of_mem_fibre (h : InductiveModel.Sound E₁ ε₁ I η ls witness)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (hs : ∀ s₁ : Fin ι.nsorts, s₁ = s)
    (hc : ∀ c₁ : Fin (ι.nctors s), c₁ = c)
    (vps : Slots ι.nparams) {key raw : ZFSet.{u}}
    (hraw : raw ∈ fibreOp (witness.block vps) key) :
    ∃ vargs, vargs ∈ (witness.codes s c).argSet (witness.block vps) vps ∧
      (witness.codes s c).targetIndex vps vargs = key := by
  have hentry := mem_fibre.mp hraw
  unfold InductiveModel.block at hentry
  rw [← indSet_unfold (h.realizes.bounded vps)] at hentry
  have ⟨s₁, c₁, vargs, hargs, hentryEq⟩ := mem_indOp.mp hentry
  obtain rfl := hs s₁
  obtain rfl := hc c₁
  exact ⟨vargs, hargs, by simpa [entry_eq] using congrArg fst hentryEq⟩

theorem map
    (h : InductiveModel.Sound E₁ ε₁ I η ls witness)
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂) :
    InductiveModel.Sound E₂ ε₂ (I.map pre.sigs) (η.map pre.sigs) ls witness where
  block_eq := by
    simpa [dsimp% (Env.lookup _).naturality_apply pre η] using
      congrArg (Inductive.map pre.sigs) h.block_eq
  realizes := h.realizes.map pre hatoms
  sortAtom s vps vis := (congrFun hatoms _).trans (h.sortAtom s vps vis)
  rules := Inductive.RulesSound.map h.rules pre hatoms

end InductiveModel.Sound

end Metalean
