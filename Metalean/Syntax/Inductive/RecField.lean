/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Basic

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ₁ ζ₂ : Sigs} {ℓ ℓ' n nfields arity : Nat}
  {ι : IndSig} {target : Fin ι.nsorts}

variable (fd : RecField ζ₁ ι nfields arity target)
  (pre : ζ₁ ⟶ ζ₂)
  (η : Head ζ₁ (.inductive ι))
  (ls : Fin ι.nlevels → Level ℓ)
  (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
  (σ : Subst ζ₁ ℓ (ι.nparams + nfields) n)
  (fieldSubst : Subst ζ₁ ℓ (ι.nparams + nfields) n)
  (ls' : Param ℓ → Level ℓ')

namespace RecField

def instantiatedTelescope :
    Ctx ζ₁ ℓ n (n + arity) :=
  Ctx.substN fieldSubst arity fd.tele{ls}

def instantiatedIndices :
    Fin (ι.nindices target) → Expr ζ₁ ℓ (n + arity) :=
  fun i => (fd.indices i){ls}.subst (fieldSubst.liftN arity)

@[simp] theorem instantiatedTelescope_id :
    fd.instantiatedTelescope ls Subst.id = fd.tele{ls} :=
  letI := Subst.category ζ₁ ℓ
  (Ctx.substFunctor _).map_id_apply _ _

@[simp] theorem instantiatedIndices_id :
    fd.instantiatedIndices ls Subst.id = fd.indices{ls} := by
  funext i
  simp [instantiatedIndices]

def instantiatedType : Expr ζ₁ ℓ n :=
  Ctx.pi
    (.ind η target ls (fun i => (ps i).wkN arity)
      (fd.instantiatedIndices ls σ))
    (fd.instantiatedTelescope ls σ)

@[simp] theorem instantiatedTelescope_map
    (fd : RecField ζ₁ ι nfields arity target)
    (ls : Fin ι.nlevels → Level ℓ) (fieldSubst : Subst ζ₁ ℓ (ι.nparams + nfields) n) :
    (fd.instantiatedTelescope ls fieldSubst).map pre =
      (fd.map pre).instantiatedTelescope ls (fieldSubst.map pre) :=
  (Ctx.map_substN pre fieldSubst arity _).trans
    (congrArg (Ctx.substN _ _) (Ctx.map_instL pre ls fd.tele))

theorem instantiatedType_of_arity_eq_zero
    (h : arity = 0)
    (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (σ : Subst ζ₁ ℓ (ι.nparams + nfields) n) :
    ∃ is : Fin (ι.nindices target) → Expr ζ₁ ℓ n,
      fd.instantiatedType η ls ps σ = .ind η target ls ps is := by
  subst h
  exact ⟨fd.instantiatedIndices ls σ, by simp [instantiatedType, instantiatedTelescope, Expr.wkN]⟩

@[simp] theorem instantiatedType_map :
    (fd.instantiatedType η ls ps σ).map pre =
      (fd.map pre).instantiatedType (η.map pre) ls
        (fun i => (ps i).map pre) (σ.map pre) := by
  refine (Ctx.map_pi pre _ _).trans (congrArg₂ Ctx.pi ?_ ?_)
  · simp [instantiatedIndices, Expr.map]
    rfl
  · exact instantiatedTelescope_map pre fd ls σ

@[simp] theorem instantiatedTelescope_instL :
    (fd.instantiatedTelescope ls fieldSubst){ls'} =
      fd.instantiatedTelescope ls{ls'} fieldSubst{ls'} := by
  simp [instantiatedTelescope, InstLevel.inst_tuple]

@[simp] theorem instantiatedIndices_instL (i : Fin (ι.nindices target)) :
    (fd.instantiatedIndices ls fieldSubst i){ls'} =
      fd.instantiatedIndices ls{ls'} fieldSubst{ls'} i := by
  simp [instantiatedIndices]

@[simp] theorem instantiatedType_instL :
    (fd.instantiatedType η ls ps fieldSubst){ls'} =
      fd.instantiatedType η ls{ls'} ps{ls'} fieldSubst{ls'} := by
  simp [instantiatedType, InstLevel.inst_tuple]

end RecField

end Metalean
