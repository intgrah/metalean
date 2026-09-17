/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Eq
public import Metalean.Typing.Defeq
import Metalean.Meta.Judgement

@[expose] public section

namespace Metalean

variable {ζ : Sigs} {E : Env ζ} {ℓ n m : Nat} {Γ : Ctx ζ ℓ 0 n} {Δ : Ctx ζ ℓ n m}

def WFTele (E : Env ζ) (P : Level ℓ → Prop)
    (Γ : Ctx ζ ℓ 0 n) (Δ : Ctx ζ ℓ n m) : Prop :=
  Δ.Forall fun Δ' t => ∃ l, E[Γ ++ Δ'] ⊢ t : .sort l ∧ P l

namespace Inductive

variable {ι : IndSig} (I : Inductive ζ ι)

def IdxWF (E : Env ζ) (Γ : Ctx ζ ℓ 0 n) (s : Fin ι.nsorts)
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) : Prop :=
  ∀ i, E[Γ] ⊢ is i : I.indexType ls s ps is i

def LevelOK (l : Level ι.nlevels) : Prop :=
  Level.imax l I.level ≤ I.level

theorem levelOK_of_zero {l : Level ι.nlevels} :
    I.level = .zero → I.LevelOK l :=
  Level.imax_le_right_of_eq_zero

end Inductive

namespace Field

variable {ι : IndSig} {nfields : Nat}

structure WF (E : Env ζ) (I : Inductive ζ ι)
    (Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields))
    (fd : Field ζ ι nfields) : Prop where
  typeExact : E[Γ] ⊢ fd.type : .sort fd.level
  levelOK : I.LevelOK fd.level

end Field

namespace RecField

variable {ι : IndSig} {nfields : Nat}

structure WF (E : Env ζ) (I : Inductive ζ ι)
    (Γ : Ctx ζ ι.nlevels 0 (ι.nparams + nfields))
    {arity : Nat} {s : Fin ι.nsorts} (fd : RecField ζ ι nfields arity s) : Prop where
  tele : WFTele E I.LevelOK Γ fd.tele
  indices :
    I.IdxWF E (Γ ++ fd.tele) s Level.param
      (fun param => .var ⟨param.val, by omega⟩) fd.indices

end RecField

namespace Ctor

variable {ι : IndSig} {s : Fin ι.nsorts}
variable {csig : CtorSig ι.nsorts}

structure WF (E : Env ζ) (I : Inductive ζ ι)
    (ctor : Ctor ζ ι s csig) : Prop where
  ordinary (f) :
    Field.WF E I
      (I.params ++ ctor.ordinaryTeleAux f.val (by omega))
      (ctor.ordinary f)
  recursive (f) :
    RecField.WF E I (I.params ++ ctor.ordinaryTele)
      (ctor.recursive f)
  targetIndices :
    I.IdxWF E (I.params ++ ctor.ordinaryTele) s Level.param
      (fun param => .var ⟨param.val, by omega⟩) ctor.targetIndices

end Ctor

namespace Inductive

variable {ι : IndSig}

structure WF (E : Env ζ) (I : Inductive ζ ι) : Prop where
  params : WFTele E (fun _ => True) .nil I.params
  indices (s) : WFTele E (fun _ => True) I.params (I.indices s)
  ctors (s ctor) : (I.ctors s ctor).WF E I

end Inductive

namespace Entry

judgement WF (E : Env ζ) : {sig : Sig} → Entry ζ sig → Prop where

  E[.nil] ⊢ t typ
  ──────────────────── «axiom» {ℓ : Nat} {t : Expr ζ ℓ 0}
  WF E (.axiom t)

  E[.nil] ⊢ e : t
  E[.nil] ⊢ t typ
  ──────────────────── «opaque» {ℓ : Nat} {e t : Expr ζ ℓ 0}
  WF E (.opaque t)

  E[.nil] ⊢ t typ
  E[.nil] ⊢ e : t
  ──────────────────── «def» {ℓ : Nat} {e t : Expr ζ ℓ 0}
  WF E (.def t e)

  (E.get ηeq).block = Eq.block
  ──────────────────── quot {ηeq : Head ζ (.inductive Eq.sig)}
  WF E (.quot ηeq)

  I.WF E
  ──────────────────── «inductive» {ι : IndSig} {I : Inductive ζ ι}
  WF E (.inductive I)

end Entry

theorem Expr.falseTy_isType (E : Env ζ) : E[.nil] ⊢ (.falseTy : Expr ζ 0 0) typ :=
  ⟨_, .forallEDF .sortDF .var⟩

namespace Env

-- TODO rename to WF
-- TODO do the TODO
inductive Ordered : {ζ : Sigs} → Env ζ → Prop
  | nil : Ordered .nil
  | snoc {ζ : Sigs} {sig : Sig} {E : Env ζ} {entry : Entry ζ sig} :
      Ordered E → Entry.WF E entry → Ordered (.snoc E entry)

theorem Ordered.ofPrefix {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
    (pre : Prefix E₁ E₂) (ho : E₂.Ordered) : E₁.Ordered := by
  induction pre with
  | refl => exact ho
  | step _ ih =>
    have .snoc ho _ := ho
    exact ih ho

/--
It is not the case that every closed type has a closed inhabitant
This is for a particular environment.
This effectively means you cannot enter new things into the environment like
inductive types, or axioms or definitions.
However definitions are admissible because of let bindings/inlining.
-/
def Con (E : Env ζ) : Prop :=
  ¬∀ t : Expr ζ 0 0, E[.nil] ⊢ t typ → ∃ e, E[.nil] ⊢ e : t

end Env

end Metalean
