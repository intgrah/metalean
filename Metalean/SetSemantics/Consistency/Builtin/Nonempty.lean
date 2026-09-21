/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Nonempty
public import Metalean.SetSemantics.Consistency.Environment

public section

universe u

namespace Metalean.Nonempty

open ZFSet

variable {ζ : Sigs} {E : Env ζ} {ε : Atom ζ 0 → ZFSet.{u}}
  {η : Head ζ (.inductive sig)} {l : Level 0}
  {w : InductiveModel.{u} Nonempty.sig}

structure Sem (ε : Atom ζ 0 → ZFSet.{u})
    (η : Head ζ (.inductive sig)) : Prop where
  exists_mem {l : Level 0} {α h : ZFSet.{u}} (hα : α ∈ S_ (l.eval zeroNs))
    (hh : h ∈ ε (.ind η ⟨0, by decide⟩ (fun _ => l) ![α] ![])) :
    ∃ x, x ∈ α

namespace Sem

private theorem reachable (h : InductiveModel.Sound E ε Nonempty.block η (fun _ => l) w)
    {α : ZFSet.{u}} (hα : α ∈ S_ (l.eval zeroNs)) :
    ![α] ∈ Reachable Set.univ w.paramsSem :=
  h.realizes.params.reachable_of_semCtx ![α]
    (by simpa! [Ctx.instL] using (.nil : ε[zeroNs] ⊨ ![] : #t[]).snoc hα) trivial

theorem ofSound (h : ∀ level, ∃ w : InductiveModel.{u} Nonempty.sig,
      InductiveModel.Sound E ε Nonempty.block η (fun _ => level) w) :
    Sem ε η where
  exists_mem {level α raw} hα hraw := by
    have ⟨w, hclause⟩ := h level
    have ⟨vargs, hargs, _⟩ := hclause.uniqueCtor_of_mem_sort hclause.realizes.level_eq
      ⟨0, by decide⟩ ⟨0, by decide⟩ Fin.eq_zero Fin.eq_zero hraw
    have hparam : w.ordinaryOf 0 0 ![α] vargs 0 = α :=
      hclause.realizes.ordinaryOf_castLE ⟨0, by decide⟩ ⟨0, by decide⟩ ![α] vargs 0
    exact ⟨_, by
      simpa! [Ctor.ordinaryTeleAux, Ctx.instL, Expr.wk, hparam] using
        hclause.realizes.fieldsRealize ⟨0, by decide⟩ ⟨0, by decide⟩ ![α]
          (reachable hclause hα) vargs hargs ⟨1, by decide⟩⟩

theorem of_model (m : Env.Model.{u} E)
    (hblock : (E.get η).block = Nonempty.block) :
    Sem m.atoms η :=
  ofSound fun l => by simpa [hblock] using m.sound.inductiveModel η fun _ => l

end Sem

end Metalean.Nonempty
