/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Env
import Metalean.Typing.InstLevel
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}
variable {ι : IndSig} {I : Inductive ζ ι} {nfields : Nat}

namespace RecField

variable {Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields)}
variable {arity : Nat} {s : Fin ι.nsorts}
  {telescope : Ctx ζ ι.nlevels (ι.nparams + nfields) (ι.nparams + nfields + arity)}
  {is : Fin (ι.nindices s) → Expr ζ ι.nlevels (ι.nparams + nfields + arity)}

theorem WF.teleAt (h : RecField.WF E I Γ ⟨telescope, is⟩)
    {ls : Fin ι.nlevels → Level 0} {bound : Nat}
    (hblock : (I.level.inst ls).eval zeroNs = bound + 1) :
    WFTele E (fun level => level.eval zeroNs ≤ bound + 1)
      (Ctx.instL ls Γ) (Ctx.instL ls telescope) := by
  have hnz : I.level.eval (Level.eval zeroNs ∘ ls) ≠ 0 := by
    rw [← Level.eval_inst, hblock]
    omega
  apply h.tele.instLevel ls
  intro level hlevel
  rw [Level.eval_inst, ← hblock, Level.eval_inst]
  exact Level.eval_le_of_imax_le hlevel hnz

theorem WF.recursiveIndex (h : RecField.WF E I Γ ⟨telescope, is⟩)
    {ls : Fin ι.nlevels → Level ℓ} (index : Fin (ι.nindices s)) :
    E[Ctx.instL ls Γ ++ Ctx.instL ls telescope] ⊢
      (is index).instL ls :
        I.indexType ls s
          (fun param => .var ⟨param.val, by omega⟩)
          (fun i => (is i).instL ls) index := by
  simpa! using h.indices.instLevel ls index

end RecField

namespace Ctor

variable {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts} {ctor : Ctor ζ ι s csig}

theorem wfOrdinaryTeleAux (count : Nat) (hcount : count ≤ csig.nfields)
    (h : ∀ f : Fin count,
      Field.WF E I (I.params ++ ctor.ordinaryTeleAux f.val (by omega))
        (ctor.ordinary (f.castLE hcount))) :
    WFTele E I.LevelOK I.params (ctor.ordinaryTeleAux count hcount) := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
    have ⟨htype, hlevel⟩ := h ⟨count, by omega⟩
    exact .snoc (ih (by omega) fun f => h (f.castSucc)) ⟨_, htype, hlevel⟩

theorem WF.ordinaryTele (h : ctor.WF E I) :
    WFTele E I.LevelOK I.params ctor.ordinaryTele :=
  wfOrdinaryTeleAux csig.nfields le_rfl fun f => h.ordinary (f.castLE le_rfl)

private theorem WF.ordinaryTeleAux_get (h : ctor.WF E I) (count : Nat)
    (hcount : count ≤ csig.nfields) (f : Fin count) :
    E[I.params ++ ctor.ordinaryTeleAux count hcount] ⊢
      Ctx.get (Fin.natAdd ι.nparams f)
        (I.params ++ ctor.ordinaryTeleAux count hcount) :
      .sort (ctor.ordinary (f.castLE hcount)).level := by
  induction f using Fin.lastInduction with
  | last count =>
    rw [Ctor.ordinaryTeleAux, Tele.append_snoc, Fin.natAdd_last, Ctx.get_last]
    exact (h.ordinary ((Fin.last count).castLE hcount)).typeExact.wk
      (ctor.ordinaryType ⟨count, hcount⟩)
  | @cast count f ih =>
    rw [Ctor.ordinaryTeleAux, Tele.append_snoc, Ctx.get_snoc _ _ _ (by simp; omega)]
    exact (ih (by omega)).wk (ctor.ordinaryType ⟨count, hcount⟩)

theorem WF.ordinaryTele_get (h : ctor.WF E I) (f : Fin csig.nfields) :
    E[I.params ++ ctor.ordinaryTele] ⊢
      Ctx.get (Fin.natAdd ι.nparams f)
        (I.params ++ ctor.ordinaryTele) :
      .sort (ctor.ordinary f).level :=
  h.ordinaryTeleAux_get csig.nfields le_rfl f

end Ctor

end Metalean
