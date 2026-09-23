/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.RecField

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ₁ ζ₂ : Sigs} {ℓ ℓ' n nparams nsorts : Nat}
  {ι : IndSig} {s : Fin ι.nsorts} {csig : CtorSig ι.nsorts}
  (ctor : Ctor ζ₁ ι s csig)
  (pre : ζ₁ ⟶ ζ₂)
  (η : Head ζ₁ (.inductive ι))
  (ls : Fin ι.nlevels → Level ℓ)
  (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
  (ls' : Param ℓ → Level ℓ')

namespace CtorSig

def fieldParams {ι : IndSig} (csig : CtorSig ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n) :
    Fin ι.nparams → Expr ζ₁ ℓ (n + csig.nfields + csig.nrecFields) :=
  fun i => ((ps i).wkN csig.nfields).wkN csig.nrecFields

def fieldOrdinary (csig : CtorSig nsorts) :
    Fin csig.nfields → Expr ζ₁ ℓ (n + csig.nfields + csig.nrecFields) :=
  fun f => (Expr.var (f.natAdd n)).wkN csig.nrecFields

def fieldRecursive (csig : CtorSig nsorts) :
    Fin csig.nrecFields → Expr ζ₁ ℓ (n + csig.nfields + csig.nrecFields) :=
  fun f => .var (f.natAdd (n + csig.nfields))

@[simp] theorem fieldParams_map {ι : IndSig} (csig : CtorSig ι.nsorts)
    (pre : ζ₁ ⟶ ζ₂) (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (i : Fin ι.nparams) :
    (csig.fieldParams ps i).map pre =
      csig.fieldParams (fun i => (ps i).map pre) i := by
  simp [fieldParams]

@[simp] theorem fieldOrdinary_map (csig : CtorSig nsorts)
    (pre : ζ₁ ⟶ ζ₂) (i : Fin csig.nfields) :
    (csig.fieldOrdinary (ζ₁ := ζ₁) (ℓ := ℓ) (n := n) i).map pre =
      csig.fieldOrdinary i := by
  simp! [fieldOrdinary]

@[simp] theorem fieldRecursive_map (csig : CtorSig nsorts)
    (pre : ζ₁ ⟶ ζ₂) (i : Fin csig.nrecFields) :
    (csig.fieldRecursive (ζ₁ := ζ₁) (ℓ := ℓ) (n := n) i).map pre =
      csig.fieldRecursive i := by
  simp! [fieldRecursive]

@[simp] theorem fieldParams_instL {ι : IndSig} (csig : CtorSig ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (i : Fin ι.nparams) :
    (csig.fieldParams ps i).instL ls' =
      csig.fieldParams (fun i => (ps i).instL ls') i := by
  simp [fieldParams]

@[simp] theorem fieldOrdinary_instL (csig : CtorSig nsorts)
    (i : Fin csig.nfields) :
    (csig.fieldOrdinary (ζ₁ := ζ₁) (ℓ := ℓ) (n := n) i).instL ls' =
      csig.fieldOrdinary i := by
  simp [fieldOrdinary, Expr.instL]

@[simp] theorem fieldRecursive_instL (csig : CtorSig nsorts)
    (i : Fin csig.nrecFields) :
    (csig.fieldRecursive (ζ₁ := ζ₁) (ℓ := ℓ) (n := n) i).instL ls' =
      csig.fieldRecursive i := by
  simp! [fieldRecursive]

@[simp] theorem targetSubst_boundVars {ι : IndSig}
    (csig : CtorSig ι.nsorts) :
    Fin.append
        (fun param => (.var (param.castLE (Nat.le_add_right _ _)) :
          Expr ζ₁ ℓ (ι.nparams + csig.nfields)))
        (Expr.boundVars ι.nparams csig.nfields 0) =
      Subst.id := by
  funext v
  cases v using Fin.addCases with
  | left param => simp; rfl
  | right f => simp; rfl

theorem fieldParams_vars {ι : IndSig}
    (csig : CtorSig ι.nsorts) :
    csig.fieldParams (fun i => (.var i : Expr ζ₁ ℓ ι.nparams)) =
      fun param => (.var (param.castLE (by omega)) :
        Expr ζ₁ ℓ (ι.nparams + csig.nfields + csig.nrecFields)) := by
  funext param
  unfold fieldParams
  rw [Expr.wkN_eq_rename, Expr.wkN_eq_rename]
  rfl

theorem targetSubst_fields {ι : IndSig} (csig : CtorSig ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n) :
    Fin.append (csig.fieldParams ps) csig.fieldOrdinary =
      Subst.rename (Ren.wkN csig.nrecFields)
        (Fin.append (fun i => (ps i).wkN csig.nfields) (Expr.boundVars n csig.nfields 0)) := by
  funext v
  cases v using Fin.addCases with
  | left param =>
    simpa [fieldParams, Subst.rename] using Expr.wkN_eq_rename _ _
  | right f =>
    simp [Subst.rename]
    exact Expr.wkN_eq_rename _ _

end CtorSig

namespace Ctor

def ordinaryFieldExpr
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (field : Fin csig.nfields) : Expr ζ₁ ℓ n :=
  (((ctor.ordinary field).type).instL ls).subst
    (Fin.append ps fun prior => fds (prior.castLE field.isLt.le))

def recursiveFieldExpr
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (field : Fin csig.nrecFields) : Expr ζ₁ ℓ n :=
  (ctor.recursive field).instantiatedType η ls ps (Fin.append ps fds)

@[simp] theorem ordinaryFieldExpr_map
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (field : Fin csig.nfields) :
    (ctor.ordinaryFieldExpr ls ps fds field).map pre =
      (ctor.map pre).ordinaryFieldExpr ls
        (fun i => (ps i).map pre)
        (fun i => (fds i).map pre) field := by
  simp [ordinaryFieldExpr, map, Field.map]

@[simp] theorem recursiveFieldExpr_map
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (field : Fin csig.nrecFields) :
    (ctor.recursiveFieldExpr η ls ps fds field).map pre =
      (ctor.map pre).recursiveFieldExpr (η.map pre) ls
        (fun i => (ps i).map pre)
        (fun i => (fds i).map pre) field := by
  simp [recursiveFieldExpr, map]

@[simp] theorem ordinaryFieldExpr_instL
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (field : Fin csig.nfields) :
    (ctor.ordinaryFieldExpr ls ps fds field).instL ls' =
      ctor.ordinaryFieldExpr (fun i => (ls i).inst ls')
        (fun i => (ps i).instL ls')
        (fun i => (fds i).instL ls') field := by
  simp [ordinaryFieldExpr]

@[simp] theorem recursiveFieldExpr_instL
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (field : Fin csig.nrecFields) :
    (ctor.recursiveFieldExpr η ls ps fds field).instL ls' =
      ctor.recursiveFieldExpr η (fun i => (ls i).inst ls')
        (fun i => (ps i).instL ls')
        (fun i => (fds i).instL ls') field := by
  simp [recursiveFieldExpr]

theorem recursiveFieldExpr_eq
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (field : Fin csig.nrecFields) :
    ctor.recursiveFieldExpr η ls ps fds field =
      Ctx.pi
        (.ind η (csig.recursiveTarget field) ls
          (fun i => (ps i).wkN (csig.recursiveArity field))
          ((ctor.recursive field).instantiatedIndices ls
            (Fin.append ps fds)))
        ((ctor.recursive field).instantiatedTelescope ls
          (Fin.append ps fds)) :=
  rfl

theorem recursiveFieldExpr_eq_ind
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (field : Fin csig.nrecFields)
    (h : csig.recursiveArity field = 0) :
    ∃ is : Fin (ι.nindices (csig.recursiveTarget field)) → Expr ζ₁ ℓ n,
      ctor.recursiveFieldExpr η ls ps fds field =
        .ind η (csig.recursiveTarget field) ls ps is :=
  (ctor.recursive field).instantiatedType_of_arity_eq_zero h η ls ps _

def targetIndex
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (i : Fin (ι.nindices s)) : Expr ζ₁ ℓ n :=
  ((ctor.targetIndices i).instL ls).subst (Fin.append ps fds)

@[simp] theorem targetIndex_map
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (i : Fin (ι.nindices s)) :
    (ctor.targetIndex ls ps fds i).map pre =
      (ctor.map pre).targetIndex ls
        (fun i => (ps i).map pre)
        (fun i => (fds i).map pre) i := by
  simp [targetIndex, map]

@[simp] theorem targetIndex_instL
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (i : Fin (ι.nindices s)) :
    (ctor.targetIndex ls ps fds i).instL ls' =
      ctor.targetIndex (fun i => (ls i).inst ls')
        (fun i => (ps i).instL ls')
        (fun i => (fds i).instL ls') i := by
  simp [targetIndex]

def ordinaryFieldTeleAux
    (_η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ₁ ℓ n)
    (count : Nat) (hcount : count ≤ csig.nfields) : Ctx ζ₁ ℓ n (n + count) :=
  Ctx.substN ps count ((ctor.ordinaryTeleAux count hcount).instL ls)

def ordinaryFieldTele : Ctx ζ₁ ℓ n (n + csig.nfields) :=
  ordinaryFieldTeleAux ctor η ls ps csig.nfields le_rfl

@[simp] theorem ordinaryFieldTeleAux_entry
    (count : Nat) (hcount : count ≤ csig.nfields) (f : Fin count) :
    Ctx.entry (p := n + f.val)
        (ctor.ordinaryFieldTeleAux η ls ps count hcount)
        (by omega) (by omega) =
      (((ctor.ordinary (f.castLE hcount)).type).instL ls).subst
        (Subst.liftN ps f.val) := by
  induction f using Fin.lastInduction with
  | last count =>
    change (ctor.ordinaryFieldTeleAux η ls ps (count + 1) hcount).entry _ _ =
      (((ctor.ordinary ⟨count, by omega⟩).type).instL ls).subst (Subst.liftN ps count)
    simp [ordinaryFieldTeleAux, ordinaryTeleAux, Ctx.instL, Ctx.substN]
  | cast f ih =>
    simpa [ordinaryFieldTeleAux, ordinaryTeleAux, Ctx.instL, Ctx.substN] using ih (by omega)

def recursiveFieldTeleAux (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (count : Nat) (hcount : count ≤ csig.nrecFields) : Ctx ζ₁ ℓ n (n + count) :=
  Ctx.ofTypes fun f : Fin count =>
    (ctor.recursive (f.castLE hcount)).instantiatedType η ls ps (Fin.append ps fds)

abbrev recursiveFieldTele
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n) :
    Ctx ζ₁ ℓ n (n + csig.nrecFields) :=
  ctor.recursiveFieldTeleAux η ls ps fds csig.nrecFields le_rfl

def fieldTele
    (stop : Fin (csig.nrecFields + 1) := ⟨csig.nrecFields, Nat.lt_succ_self _⟩) :
    Ctx ζ₁ ℓ n (n + csig.nfields + stop.val) :=
  ctor.ordinaryFieldTele η ls ps ++ ctor.recursiveFieldTeleAux
    η ls (fun i => (ps i).wkN csig.nfields) (Expr.boundVars n csig.nfields 0)
    stop.val (Nat.le_of_lt_succ stop.isLt)

@[simp] theorem ordinaryFieldTeleAux_map (count : Nat)
    (hcount : count ≤ csig.nfields) :
    (ctor.ordinaryFieldTeleAux η ls ps count hcount).map pre =
      (ctor.map pre).ordinaryFieldTeleAux (η.map pre) ls
        (fun i => (ps i).map pre) count hcount :=
  (Ctx.map_substN pre ps count _).trans
    (congrArg (Ctx.substN _ _) ((Ctx.map_instL pre ls _).trans
      (congrArg (Ctx.instL ls) (ordinaryTeleAux_map pre ctor count hcount))))

@[simp] theorem ordinaryFieldTele_map :
    (ctor.ordinaryFieldTele η ls ps).map pre =
      (ctor.map pre).ordinaryFieldTele (η.map pre) ls
        fun i => (ps i).map pre :=
  ctor.ordinaryFieldTeleAux_map pre η ls ps _ _

@[simp] theorem recursiveFieldTeleAux_map
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n) (count : Nat)
    (hcount : count ≤ csig.nrecFields) :
    (ctor.recursiveFieldTeleAux η ls ps fds count hcount).map pre =
      (ctor.map pre).recursiveFieldTeleAux (η.map pre) ls
        (fun i => (ps i).map pre)
        (fun i => (fds i).map pre) count hcount := by
  refine (Ctx.ofTypes_map _ pre).trans ?_
  simp [recursiveFieldTeleAux, map]

@[simp] theorem fieldTele_map
    (stop : Fin (csig.nrecFields + 1) := ⟨csig.nrecFields, Nat.lt_succ_self _⟩) :
    (ctor.fieldTele η ls ps stop).map pre =
      (ctor.map pre).fieldTele (η.map pre) ls
        (fun i => (ps i).map pre) stop :=
  (Ctx.map_append pre _ _).trans
    (congrArg₂ Tele.append
      (ctor.ordinaryFieldTele_map pre η ls ps)
      ((ctor.recursiveFieldTeleAux_map pre η ls _ _ _ _).trans (by simp)))

@[simp] theorem ordinaryFieldTeleAux_instL
    (count : Nat) (hcount : count ≤ csig.nfields) :
    (ctor.ordinaryFieldTeleAux η ls ps count hcount).instL ls' =
      ctor.ordinaryFieldTeleAux η (fun i => (ls i).inst ls')
        (fun i => (ps i).instL ls') count hcount := by
  simp [ordinaryFieldTeleAux]
  rfl

@[simp] theorem ordinaryFieldTele_instL :
    (ctor.ordinaryFieldTele η ls ps).instL ls' =
      ctor.ordinaryFieldTele η (fun i => (ls i).inst ls')
        fun i => (ps i).instL ls' :=
  ctor.ordinaryFieldTeleAux_instL η ls ps ls' _ _

@[simp] theorem recursiveFieldTeleAux_instL
    (fds : Fin csig.nfields → Expr ζ₁ ℓ n)
    (count : Nat) (hcount : count ≤ csig.nrecFields) :
    (ctor.recursiveFieldTeleAux η ls ps fds count hcount).instL ls' =
      ctor.recursiveFieldTeleAux η (fun i => (ls i).inst ls')
        (fun i => (ps i).instL ls') (fun i => (fds i).instL ls')
        count hcount := by
  simp [recursiveFieldTeleAux]

@[simp] theorem fieldTele_instL
    (stop : Fin (csig.nrecFields + 1) := ⟨csig.nrecFields, Nat.lt_succ_self _⟩) :
    (ctor.fieldTele η ls ps stop).instL ls' =
      ctor.fieldTele η (fun i => (ls i).inst ls')
        (fun i => (ps i).instL ls') stop := by
  simp [fieldTele]

theorem targetIndex_boundVars
    (i : Fin (ι.nindices s)) :
    ctor.targetIndex ls
        (fun param => (.var (param.castLE (Nat.le_add_right _ _)) :
          Expr ζ₁ ℓ (ι.nparams + csig.nfields)))
        (Expr.boundVars ι.nparams csig.nfields 0) i =
      Expr.instL ls (ctor.targetIndices i) := by
  simp [targetIndex]

@[simp] theorem targetIndex_fields
    (i : Fin (ι.nindices s)) :
    ctor.targetIndex ls (csig.fieldParams ps) csig.fieldOrdinary i =
      (ctor.targetIndex ls (fun i => (ps i).wkN csig.nfields)
        (Expr.boundVars n csig.nfields 0) i).wkN csig.nrecFields := by
  rw [targetIndex, targetIndex, CtorSig.targetSubst_fields,
    ← Expr.subst_rename, Expr.wkN_eq_rename]

theorem targetIndex_fieldVars
    (i : Fin (ι.nindices s)) :
    ctor.targetIndex ls
        (fun param => (.var (param.castLE (by omega)) :
          Expr ζ₁ ℓ (ι.nparams + csig.nfields + csig.nrecFields)))
        csig.fieldOrdinary i =
      (Expr.instL ls (ctor.targetIndices i)).wkN csig.nrecFields := by
  rw [← csig.fieldParams_vars, ctor.targetIndex_fields,
    Expr.vars_wkN, ctor.targetIndex_boundVars]

theorem targetType_fields :
    (Expr.ind η s ls
        (fun param => (.var (param.castLE (Nat.le_add_right _ _)) :
          Expr ζ₁ ℓ (ι.nparams + csig.nfields)))
        fun i => Expr.instL ls (ctor.targetIndices i)).wkN
      csig.nrecFields =
      Expr.ind η s ls
        (csig.fieldParams fun param => (.var param : Expr ζ₁ ℓ ι.nparams))
        fun i => ctor.targetIndex ls
          (csig.fieldParams fun param => (.var param : Expr ζ₁ ℓ ι.nparams))
          csig.fieldOrdinary i := by
  rw [Expr.wkN_ind]
  congr 1
  · funext param
    congr 1
    rw [Expr.wkN_eq_rename]
    rfl
  · funext i
    rw [csig.fieldParams_vars]
    exact (ctor.targetIndex_fieldVars ls i).symm

end Ctor

end Metalean
