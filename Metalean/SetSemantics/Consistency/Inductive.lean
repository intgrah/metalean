/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Consistency.Environment
public import Metalean.SetSemantics.Environment.Inductive.Rules.EtaStruct
public import Metalean.SetSemantics.Environment.Inductive.Rules.Iota

universe u

namespace Metalean

open CategoryTheory ZFSet

variable {ζ : Sigs}

public noncomputable def Env.Model.addInductive {pre : Env ζ} {ι : IndSig}
    {I : Inductive ζ ι} (m : Env.Model.{u} pre) (ho : pre.Ordered)
    (hwf : EntryWF pre (.inductive I)) :
    Env.Model.{u} (pre.snoc (.inductive I)) := by
  have hblock : InductiveWF pre I :=
    have .inductive hblock := hwf
    hblock
  let model (ls) : StrongInductiveModel pre m.atoms I ls :=
    Classical.choice (hblock.model m.semDecls m.semDeclRules ho)
  let fresh : Atom (.snoc ζ (.inductive ι)) 0 → ZFSet.{u}
    | .ind .here s ls vps vis => (model ls).toModel.sortValue s vps vis
    | .ctor .here s c ls vps vfds vrecFds => (model ls).ctorResult s c vps vfds vrecFds
    | .recr .here s ls l vps vms vmins vis vmaj =>
      (model ls).recLeaf s l (RecSlots.args vps vms vmins vis vmaj)
    | _ => ∅
  let step : pre.as ⟶ (pre.snoc (.inductive I)).as := .step .refl
  have hatoms : AtomsMap step.sigs m.atoms (atomBelow m.atoms fresh) :=
    atomBelow.map m.atoms fresh
  refine m.snoc fresh (.inductive fun ls => ?_)
  let current := model ls
  have hsorts (s vps vis) :
      atomBelow m.atoms fresh
        (.ind (.here : Head _ (.inductive ι)) s ls vps vis)
        = current.toModel.sortValue s vps vis := rfl
  have hctors (s c vps vfds vrecFds) :
      atomBelow m.atoms fresh
        (.ctor (.here : Head _ (.inductive ι)) s c ls vps vfds vrecFds)
        = current.ctorResult s c vps vfds vrecFds := rfl
  have hrecr (s l vps vms vmins vis vmaj) :
      atomBelow m.atoms fresh (.recr (.here : Head _ (.inductive ι)) s ls l
          vps vms vmins vis vmaj)
        = current.recLeaf s l
          (RecSlots.args vps vms vmins vis vmaj) := rfl
  have hatomsAt {ζ₂ : Sigs} {E₂ : Env ζ₂} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
      (suffix : (pre.snoc (.inductive I)).as ⟶ E₂.as)
      (hatoms₁ : AtomsMap suffix.sigs (atomBelow m.atoms fresh) ε₂) :
      AtomsMap (step ≫ suffix).sigs m.atoms ε₂ := by
    simpa [dsimp% Env.forget.map_comp step suffix] using hatoms.trans hatoms₁
  have hblockAt {ζ₂ : Sigs} {E₂ : Env ζ₂}
      (suffix : (pre.snoc (.inductive I)).as ⟶ E₂.as) :
      (E₂.get (Head.map suffix.sigs .here)).block = I.map (step ≫ suffix).sigs := by
    simpa [dsimp% (Env.lookup _).naturality_apply suffix .here,
      show ((pre.snoc (.inductive I)).get .here).block = I.map step.sigs from rfl] using
      ((Env.forget ⋙ Inductive.functor ι).map_comp_apply step suffix I).symm
  have hsortsAt {ζ₂ : Sigs} {E₂ : Env ζ₂} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
      (suffix : (pre.snoc (.inductive I)).as ⟶ E₂.as)
      (hatoms₁ : AtomsMap suffix.sigs (atomBelow m.atoms fresh) ε₂) (s vps vis) :=
    (congrFun hatoms₁ _).trans (hsorts s vps vis)
  have hctorsAt {ζ₂ : Sigs} {E₂ : Env ζ₂} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
      (suffix : (pre.snoc (.inductive I)).as ⟶ E₂.as)
      (hatoms₁ : AtomsMap suffix.sigs (atomBelow m.atoms fresh) ε₂) (s c vps vfds vrecFds) :=
    (congrFun hatoms₁ _).trans (hctors s c vps vfds vrecFds)
  have hrecrAt {ζ₂ : Sigs} {E₂ : Env ζ₂} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
      (suffix : (pre.snoc (.inductive I)).as ⟶ E₂.as)
      (hatoms₁ : AtomsMap suffix.sigs (atomBelow m.atoms fresh) ε₂) (s l vps vms vmins vis vmaj) :=
    (congrFun hatoms₁ _).trans (hrecr s l vps vms vmins vis vmaj)
  exact ⟨current.toModel,
    { block_eq := rfl
      realizes := current.realizes step hatoms hsorts
      sortAtom := hsorts
      rules :=
      { ind := fun suffix hatoms₁ =>
          current.indRuleSound (step ≫ suffix) (hblockAt suffix)
            (hsortsAt suffix hatoms₁)
        ctor := fun suffix hatoms₁ =>
          current.ctorRuleSound (step ≫ suffix) (hatomsAt suffix hatoms₁) (hblockAt suffix)
            (hsortsAt suffix hatoms₁)
            (hctorsAt suffix hatoms₁)
        recr := fun {ζ₂ E₂ ε₂} suffix hatoms₁
            {n ρ s u ps₁ ps₂ ms₁ ms₂ cases cases' is₁ is₂ maj₁ maj₂} hallowed hps hms hmins his hmaj =>
          SemDefeq.recr (E := E₂) (ε := ε₂)
            (by
              rw [hblockAt suffix]
              exact current.recrTeleRealizes (step ≫ suffix) (hatomsAt suffix hatoms₁)
                (hsortsAt suffix hatoms₁) (hctorsAt suffix hatoms₁) s u)
            (current.recLeaf_mem s u) (hrecrAt suffix hatoms₁ s u) hps hms hmins his hmaj
        iota := fun {ζ₂ E₂ ε₂} suffix hatoms₁ {n ρ u ps ms mins s c fds recFds}
            hallowed hps hms hmins hfields hrecFields =>
          current.iotaRuleSound m.semDecls m.semDeclRules ho hblock
            (step ≫ suffix) (hatomsAt suffix hatoms₁) (hblockAt suffix)
            (hsortsAt suffix hatoms₁)
            (hctorsAt suffix hatoms₁)
            (hrecrAt suffix hatoms₁)
            hallowed hps hms hmins hfields hrecFields
        etaStruct := fun {ζ₂ E₂ ε₂} suffix hatoms₁ {n γ s c ps is maj} hstruct =>
          current.etaStructRuleSound m.semDecls m.semDeclRules ho hblock
            (step ≫ suffix) (hatomsAt suffix hatoms₁) (hblockAt suffix)
            (hsortsAt suffix hatoms₁)
            (hctorsAt suffix hatoms₁)
            (hrecrAt suffix hatoms₁)
            hstruct } }⟩

end Metalean
