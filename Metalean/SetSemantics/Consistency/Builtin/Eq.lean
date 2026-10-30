/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Consistency.Environment
public import Metalean.SetSemantics.QuotientValue

public section

universe u

namespace Metalean.Eq

open ZFSet

variable {ζ : Sigs} {E : Env ζ} {ε : Atom ζ 0 → ZFSet.{u}}
  {η : Head ζ (.inductive sig)} {l : Level 0}
  {w : InductiveModel.{u} Eq.sig}

structure Sem (ε : Atom ζ 0 → ZFSet.{u})
    (η : Head ζ (.inductive sig)) : Prop where
  separates (l : Level 0) :
    EqualitySeparates (l.eval ![]) fun α x y =>
      ε (.ind η ⟨0, by decide⟩ (fun _ => l) ![α, x] ![y])
  refl {l : Level 0} {α x : ZFSet.{u}} (hα : α ∈ S_ (l.eval ![])) (hx : x ∈ α) :
    proof ∈ ε (.ind η ⟨0, by decide⟩ (fun _ => l) ![α, x] ![x])

namespace Sem

private theorem reachable (h : InductiveModel.Sound E ε Eq.block η (fun _ => l) w)
    {α x : ZFSet.{u}} (hα : α ∈ S_ (l.eval ![])) (hx : x ∈ α) :
    ![α, x] ∈ Reachable Set.univ w.paramsSem :=
  h.realizes.params.reachable_of_semCtx ![α, x]
    (by
      simpa [Ctx.instL] using
        ((.nil : ε[![]] ⊨ ![] : #t[]).snoc hα).snoc
          hx)
    trivial

private theorem target (h : InductiveModel.Sound E ε Eq.block η (fun _ => l) w)
    {α x key : ZFSet.{u}} (hps : ![α, x] ∈ Reachable Set.univ w.paramsSem)
    {vargs : _} (hargs : vargs ∈ (w.codes ⟨0, by decide⟩ ⟨0, by decide⟩).argSet
      (w.block ![α, x]) ![α, x])
    (hkey : (w.codes ⟨0, by decide⟩ ⟨0, by decide⟩).targetIndex ![α, x] vargs = key) :
    key = sortKey 0 (encode ![x]) := by
  let vfds := w.ordinaryOf ⟨0, by decide⟩ ⟨0, by decide⟩ ![α, x] vargs
  have htargetValue : w.targetValues ⟨0, by decide⟩ ⟨0, by decide⟩
      vfds ⟨0, by decide⟩ = vfds ⟨1, by decide⟩ := by
    simpa! [Eq.ctorDecl, vfds] using (h.realizes.targetRealizes ⟨0, by decide⟩ ⟨0, by decide⟩
      ![α, x] hps vargs hargs ⟨0, by decide⟩).symm
  have hvalues : w.targetValues ⟨0, by decide⟩ ⟨0, by decide⟩ vfds = ![x] := by
    funext index
    obtain rfl := Fin.eq_zero index
    simpa using htargetValue.trans
      (h.realizes.ordinaryOf_castLE ⟨0, by decide⟩ ⟨0, by decide⟩ ![α, x] vargs ⟨1, by decide⟩)
  rw [← hkey, h.realizes.targetIndex_eq, hvalues]

theorem ofSound (h : ∀ level, ∃ w : InductiveModel.{u} Eq.sig,
      InductiveModel.Sound E ε Eq.block η (fun _ => level) w) :
    Sem ε η where
  separates level α hα x hx y hy raw hraw := by
    have ⟨w, hclause⟩ := h level
    have ⟨vargs, hargs, hkeyEq⟩ := hclause.uniqueCtor_of_mem_sort
      (by simpa using hclause.realizes.level_eq)
      ⟨0, by decide⟩ ⟨0, by decide⟩ Fin.eq_zero Fin.eq_zero hraw
    have hvis : ![y] = ![x] := Encode.injective <| congrArg Prod.snd <| sortKey_injective <|
      target hclause (reachable hclause hα hx) hargs hkeyEq
    exact (congrFun hvis ⟨0, by decide⟩).symm
  refl {level α x} hα hx := by
    have ⟨w, hclause⟩ := h level
    have hps (p : Fin 2) : ε[![α, x]] ⊨
        (Expr.var p : Expr ζ 0 2) ≡ .var p :
        (E.get η).block.paramType (fun _ => level) Expr.var p := by
      rw [hclause.block_eq]
      refine Fin.cases ?_ ?_ p
      · exact ⟨rfl, hα⟩
      · intro p
        obtain rfl := Fin.eq_zero p
        exact ⟨rfl, hx⟩
    have hctor := hclause.rules.ctor (E₂ := E) (ε₂ := ε) .refl
      (funext fun a => congrArg ε ((Atom.functor _).map_id_apply _ a))
      (γ := ![α, x]) (s := ⟨0, by decide⟩) (c := ⟨0, by decide⟩)
      (ps₁ := Expr.var) (ps₂ := Expr.var)
      (fds₁ := ![]) (fds₂ := ![]) (recFds₁ := ![]) (recFds₂ := ![])
      hps nofun nofun
    have hmem : ε (.ctor η 0 0 (fun _ => level) ![α, x] ![] ![]) ∈
        ε (.ind η 0 (fun _ => level) ![α, x] ![x]) := by
      simpa! [Env.Prefix.sigs, Head.map, hclause.block_eq, ctorDecl, Ctor.targetIndex,
        Fin.fun_vecEmpty, Fin.const_fin_one] using hctor.mem
    rw [hclause.sortAtom, InductiveModel.sortValue,
      show w.level = 0 by simpa using hclause.realizes.level_eq] at hmem ⊢
    exact propVal_mem_propSet (level := 0) (propGet_mem hmem)

theorem of_model (m : Env.Model.{u} E)
    (hblock : (E.get η).block = Eq.block) :
    Sem m.atoms η :=
  ofSound fun l => by simpa [hblock] using m.sound.inductiveModel η fun _ => l

end Sem

end Metalean.Eq
