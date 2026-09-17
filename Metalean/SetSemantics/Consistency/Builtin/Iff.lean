/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Iff
public import Metalean.SetSemantics.Consistency.Environment

public section

universe u

namespace Metalean.Iff

open ZFSet

variable {ζ : Sigs} {E : Env ζ} {ε : Atom ζ 0 → ZFSet.{u}} {η : Head ζ (.inductive sig)}
  {w : InductiveModel.{u} Iff.sig}

structure Sem (ε : Atom ζ 0 → ZFSet.{u})
    (η : Head ζ (.inductive sig)) : Prop where
  sound {a b h : ZFSet.{u}} (ha : a ∈ truth) (hb : b ∈ truth)
    (hh : h ∈ ε (.ind η ⟨0, by decide⟩ ![] ![a, b] ![])) :
    a = b

namespace Sem

private theorem reachable (h : InductiveModel.Sound E ε Iff.block η ![] w)
    {a b : ZFSet.{u}} (ha : a ∈ truth) (hb : b ∈ truth) :
    ![a, b] ∈ Reachable Set.univ w.paramsSem :=
  h.realizes.params.reachable_of_semCtx ![a, b]
    (by
      simpa [Iff.block, Ctx.instL, Expr.instL] using
        ((.nil : ε[zeroNs] ⊨ ![] : #t[]).snoc ha).snoc
          hb)
    trivial

theorem ofSound (h : ∃ w : InductiveModel.{u} Iff.sig,
      InductiveModel.Sound E ε Iff.block η ![] w) :
    Sem ε η where
  sound {a b raw} ha hb hraw := by
    have ⟨w, hclause⟩ := h
    have ⟨vargs, hargs, _⟩ := hclause.uniqueCtor_of_mem_sort
      (by simpa [Iff.block] using hclause.realizes.level_eq)
      ⟨0, by decide⟩ ⟨0, by decide⟩ Fin.eq_zero Fin.eq_zero hraw
    have hfields := hclause.realizes.fieldsRealize ⟨0, by decide⟩ ⟨0, by decide⟩ ![a, b]
      (reachable hclause ha hb) vargs hargs
    have hfirst : w.ordinaryOf 0 0 ![a, b] vargs 0 = a :=
      hclause.realizes.ordinaryOf_castLE ⟨0, by decide⟩ ⟨0, by decide⟩ ![a, b] vargs 0
    have hsecond : w.ordinaryOf 0 0 ![a, b] vargs 1 = b :=
      hclause.realizes.ordinaryOf_castLE ⟨0, by decide⟩ ⟨0, by decide⟩ ![a, b] vargs 1
    have himp (i : Fin 4) (x y : ZFSet.{u})
        (hi : w.ordinaryOf ⟨0, by decide⟩ ⟨0, by decide⟩ ![a, b] vargs i ∈ [zf|x → y])
        (hx : proof ∈ x) : y ≠ ∅ := by
      have hmem := Aczel.app_mem hi hx
      rw [app_map hx] at hmem
      exact fun h => (notMem_empty _ (h ▸ hmem)).elim
    have hforward := himp ⟨2, by decide⟩ a b (by
      simpa [Iff.block, Ctor.ordinaryTeleAux, Ctor.ordinaryType, Ctx.get, Ctx.instL,
        Expr.instL, Expr.wk, Expr.denote, Fin.snoc, hfirst, hsecond] using
        hfields ⟨2, by decide⟩)
    have hbackward := himp ⟨3, by decide⟩ b a (by
      simpa [Iff.block, Ctor.ordinaryTeleAux, Ctor.ordinaryType, Ctx.get, Ctx.instL,
        Expr.instL, Expr.wk, Expr.denote, Fin.snoc, hfirst, hsecond] using
        hfields ⟨3, by decide⟩)
    rcases mem_truth.mp ha with rfl | rfl <;> rcases mem_truth.mp hb with rfl | rfl
    · rfl
    · exact (hbackward proof_mem_verum rfl).elim
    · exact (hforward proof_mem_verum rfl).elim
    · rfl

theorem of_model (m : Env.Model.{u} E)
    (hblock : (E.get η).block = Iff.block) :
    Sem m.atoms η :=
  ofSound (by simpa [hblock] using m.sound.inductiveModel η ![])

end Sem

end Metalean.Iff
