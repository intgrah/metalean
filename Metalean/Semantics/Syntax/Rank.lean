/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Metalean.Typing.Env
import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ ζ₁ ζ₂ : Sigs} {ℓ ℓ₁ n : Nat} {sig : Sig}

def Head.rank {ζ : Sigs} : Head ζ sig → Nat
  | @Head.here ζ _ => 2 * ζ.length + 2
  | .there η => η.rank

theorem Head.rank_le_length (η : Head ζ sig) : η.rank ≤ 2 * ζ.length := by
  induction η with
  | here => simp [rank, Sigs.length]; omega
  | there η ih => exact ih.trans (by simp [Sigs.length]; omega)

theorem Head.rank_pos (η : Head ζ sig) : 0 < η.rank := by
  induction η with
  | here => exact Nat.succ_pos _
  | there _ ih => exact ih

@[simp] theorem Head.rank_map (pre : ζ₁ ⟶ ζ₂) (η : Head ζ₁ sig) :
    (η.map pre).rank = η.rank := by
  induction pre with
  | refl => rfl
  | step _ ih => exact ih

def Expr.headRank {n : Nat} : Expr ζ ℓ n → Nat
  | .var _ => 0
  | .sort _ => 0
  | .const η _ => η.rank
  | .ind η _ _ ps is =>
    max (η.rank - 1) (max (Finset.univ.sup fun i => (ps i).headRank)
      (Finset.univ.sup fun i => (is i).headRank))
  | .ctor η _ _ _ ps fds recFds =>
    max (η.rank - 1) (max (Finset.univ.sup fun i => (ps i).headRank)
      (max (Finset.univ.sup fun i => (fds i).headRank)
        (Finset.univ.sup fun i => (recFds i).headRank)))
  | .recr η _ _ _ ps ms mins is maj =>
    max η.rank (max (Finset.univ.sup fun i => (ps i).headRank)
      (max (Finset.univ.sup fun i => (ms i).headRank)
        (max (Finset.univ.sup fun s => Finset.univ.sup fun c => (mins s c).headRank)
          (max (Finset.univ.sup fun i => (is i).headRank) maj.headRank))))
  | .quot η _ α r => max η.rank (max α.headRank r.headRank)
  | .quotMk η _ α r a => max η.rank (max α.headRank (max r.headRank a.headRank))
  | .quotLift η _ _ α r β f h a =>
    max η.rank (max α.headRank (max r.headRank (max β.headRank
      (max f.headRank (max h.headRank a.headRank)))))
  | .quotInd η _ α r β f a =>
    max η.rank (max α.headRank (max r.headRank (max β.headRank (max f.headRank a.headRank))))
  | .app f e => max f.headRank e.headRank
  | .lam t e' => max t.headRank e'.headRank
  | .forallE t t' => max t.headRank t'.headRank
  | .letE t e e' => max t.headRank (max e.headRank e'.headRank)

namespace Expr

theorem headRank_le_length (e : Expr ζ ℓ n) : e.headRank ≤ 2 * ζ.length := by
  induction e <;> simp [headRank, Finset.sup_le_iff, Head.rank_le_length,
    (Nat.sub_le _ _).trans (Head.rank_le_length _), *]

@[simp] theorem headRank_map (pre : ζ₁ ⟶ ζ₂) (e : Expr ζ₁ ℓ n) :
    (e.map pre).headRank = e.headRank := by
  induction e <;> simp [headRank, map, *]

@[simp] theorem headRank_instL (ls : Param ℓ → Level ℓ₁) (e : Expr ζ ℓ n) :
    (e.instL ls).headRank = e.headRank := by
  induction e <;> simp [headRank, instL, *]

@[simp] theorem headRank_rename {m : Nat} (ρ : Ren m n) (e : Expr ζ ℓ m) :
    (e.rename ρ).headRank = e.headRank := by
  induction e generalizing n <;> simp [headRank, rename, *]

@[simp] theorem headRank_wkN (e : Expr ζ ℓ n) (k : Nat) :
    (e.wkN k).headRank = e.headRank :=
  (congrArg headRank (wkN_eq_rename e k)).trans (headRank_rename _ e)

@[simp] theorem headRank_wkClosed (e : Expr ζ ℓ 0) : e.wkClosed (n := n).headRank = e.headRank := by
  induction n with
  | zero => rfl
  | succ n ih => exact (headRank_rename _ _).trans ih

@[simp] theorem headRank_applyBound (e : Expr ζ ℓ n) (k : Nat) :
    (e.applyBound k).headRank = e.headRank := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [applyBound, headRank, wk, wkFrom] using ih

theorem headRank_subst_le {m : Nat} (e : Expr ζ ℓ n) (σ : Subst ζ ℓ n m)
    (k : Nat) (he : e.headRank ≤ k) (hσ : ∀ v, (σ v).headRank ≤ k) :
    (e.subst σ).headRank ≤ k := by
  induction e generalizing m with
  | var v => exact hσ v
  | lam t e' iht ihe' | forallE t e' iht ihe' =>
    have hlift : ∀ v, (σ.lift v).headRank ≤ k := by
      intro v
      cases v using Fin.lastCases <;> simp [headRank, wk, wkFrom, hσ]
    exact max_le (iht σ (le_trans (le_max_left _ _) he) hσ)
      (ihe' σ.lift (le_trans (le_max_right _ _) he) hlift)
  | letE t e e' iht ihe ihe' =>
    have hlift : ∀ v, (σ.lift v).headRank ≤ k := by
      intro v
      cases v using Fin.lastCases <;> simp [headRank, wk, wkFrom, hσ]
    exact max_le (iht σ (le_trans (le_max_left _ _) he) hσ)
      (max_le (ihe σ (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) he)) hσ)
        (ihe' σ.lift (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) he)) hlift))
  | _ => simp_all [headRank, subst, Finset.sup_le_iff]

def sizeWith {n : Nat} (w : Var n → Nat) : Expr ζ ℓ n → Nat
  | .var v => w v
  | .sort _ => 1
  | .const _ _ => 1
  | .ind _ _ _ ps is =>
    (Finset.univ.sum fun i => (ps i).sizeWith w) + (Finset.univ.sum fun i => (is i).sizeWith w) + 1
  | .ctor _ _ _ _ ps fds recFds =>
    (Finset.univ.sum fun i => (ps i).sizeWith w) + (Finset.univ.sum fun i => (fds i).sizeWith w) +
      (Finset.univ.sum fun i => (recFds i).sizeWith w) + 1
  | .recr _ _ _ _ ps ms mins is maj =>
    (Finset.univ.sum fun i => (ps i).sizeWith w) + (Finset.univ.sum fun i => (ms i).sizeWith w) +
      (Finset.univ.sum fun s => Finset.univ.sum fun c => (mins s c).sizeWith w) +
      (Finset.univ.sum fun i => (is i).sizeWith w) + maj.sizeWith w + 1
  | .quot _ _ α r => α.sizeWith w + r.sizeWith w + 1
  | .quotMk _ _ α r a => α.sizeWith w + r.sizeWith w + a.sizeWith w + 1
  | .quotLift _ _ _ α r β f h a =>
    α.sizeWith w + r.sizeWith w + β.sizeWith w + f.sizeWith w + h.sizeWith w + a.sizeWith w + 1
  | .quotInd _ _ α r β f a => α.sizeWith w + r.sizeWith w + β.sizeWith w + f.sizeWith w + a.sizeWith w + 1
  | .app f e => f.sizeWith w + e.sizeWith w + 1
  | .lam t e' => t.sizeWith w + e'.sizeWith (Fin.snoc w 1) + 1
  | .forallE t t' => t.sizeWith w + t'.sizeWith (Fin.snoc w 1) + 1
  | .letE t e e' => t.sizeWith w + e.sizeWith w + e'.sizeWith (Fin.snoc w (e.sizeWith w)) + 1

def size (e : Expr ζ ℓ n) : Nat := e.sizeWith fun _ => 1

@[simp] theorem sizeWith_rename {m : Nat} (e : Expr ζ ℓ n) (ρ : Ren n m)
    (w : Var m → Nat) :
    (e.rename ρ).sizeWith w = e.sizeWith (w ∘ ρ) := by
  induction e generalizing m with
  | lam t e' iht ihe' | forallE t e' iht ihe' =>
    simp only [rename, sizeWith, iht, ihe']
    congr 1
    congr 1
    apply congrArg fun w => e'.sizeWith w
    funext v
    cases v using Fin.lastCases <;> simp [Function.comp_def]
  | letE t e e' iht ihe ihe' =>
    simp only [rename, sizeWith, iht, ihe, ihe']
    congr 1
    congr 1
    apply congrArg fun w => e'.sizeWith w
    funext v
    cases v using Fin.lastCases <;> simp [Function.comp_def]
  | _ => simp [rename, sizeWith, *]

@[simp] theorem sizeWith_subst {m : Nat} (e : Expr ζ ℓ n) (σ : Subst ζ ℓ n m)
    (w : Var m → Nat) :
    (e.subst σ).sizeWith w = e.sizeWith fun v => (σ v).sizeWith w := by
  induction e generalizing m with
  | lam t e' iht ihe' | forallE t e' iht ihe' =>
    simp only [subst, sizeWith, iht, ihe']
    congr 1
    congr 1
    apply congrArg fun w => e'.sizeWith w
    funext v
    cases v using Fin.lastCases <;> simp [sizeWith, wk, wkFrom, Function.comp_def, Ren.wkFrom]
  | letE t e e' iht ihe ihe' =>
    simp only [subst, sizeWith, iht, ihe, ihe']
    congr 1
    congr 1
    apply congrArg fun w => e'.sizeWith w
    funext v
    cases v using Fin.lastCases <;> simp [sizeWith, wk, wkFrom, Function.comp_def, Ren.wkFrom]
  | _ => simp [subst, sizeWith, *]

def measure (e : Expr ζ ℓ n) : Nat × Nat := (e.headRank, e.size)

theorem measure_lt {m : Nat} {e₁ : Expr ζ ℓ m} {e₂ : Expr ζ ℓ n}
    (hrank : e₁.headRank ≤ e₂.headRank) (hsize : e₁.size < e₂.size) :
    Prod.Lex (· < ·) (· < ·) e₁.measure e₂.measure :=
  show Prod.Lex _ _ (_, _) (_, _) from
    hrank.lt_or_eq.elim (.left _ _) fun h => h ▸ .right _ hsize

theorem measure_inst (t e : Expr ζ ℓ n) (e' : Expr ζ ℓ (n + 1)) :
    Prod.Lex (· < ·) (· < ·) (e'.inst e).measure (Expr.letE t e e').measure := by
  refine measure_lt (headRank_subst_le _ _ _ (by simp [headRank]) fun v => ?_) ?_
  · cases v using Fin.lastCases <;> simp [Subst.id, headRank]
  · simp only [size, inst, sizeWith_subst, sizeWith]
    have hw : (fun v => (Subst.id.extend e v).sizeWith fun _ => 1) =
        Fin.snoc (fun _ => 1) (e.sizeWith fun _ => 1) := by
      funext v
      cases v using Fin.lastCases <;> simp [sizeWith, Subst.id]
    rw [hw]
    exact Nat.lt_succ_of_le (Nat.le_add_left _ _)

theorem measure_lt_of_mem {m k : Nat} {e : Expr ζ ℓ n} (g : Fin k → Expr ζ ℓ m) (i : Fin k)
    (hrank : Finset.univ.sup (fun j => (g j).headRank) ≤ e.headRank)
    (hsize : Finset.univ.sum (fun j => (g j).size) < e.size) :
    Prod.Lex (· < ·) (· < ·) (g i).measure e.measure :=
  measure_lt ((Finset.le_sup (Finset.mem_univ i)).trans hrank)
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)).trans_lt hsize)

theorem measure_ctorField {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (ls : Fin ι.nlevels → Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n)
    (i : Fin ((ι.ctors s c).nfields + (ι.ctors s c).nrecFields)) :
    Prod.Lex (· < ·) (· < ·) (Fin.append fds recFds i).measure
      (ctor η s c ls ps fds recFds).measure := by
  cases i using Fin.addCases with
  | left f =>
    rw [Fin.append_left]
    exact measure_lt_of_mem fds f (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
      (by simp only [size, sizeWith]; omega)
  | right f =>
    rw [Fin.append_right]
    exact measure_lt_of_mem recFds f (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
      (by simp only [size, sizeWith]; omega)

section

variable {ι : IndSig} (η : Head ζ (.inductive ι)) (s : Fin ι.nsorts)
  (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
  (ms : Fin ι.nsorts → Expr ζ ℓ n)
  (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n)
  (is : Fin (ι.nindices s) → Expr ζ ℓ n) (maj : Expr ζ ℓ n)

theorem measure_ind_param (i : Fin ι.nparams) :
    Prod.Lex (· < ·) (· < ·) (ps i).measure (ind η s ls ps is).measure :=
  measure_lt_of_mem ps i (le_max_of_le_right (le_max_left _ _)) (by simp only [size, sizeWith]; omega)

theorem measure_recr_param (i : Fin ι.nparams) :
    Prod.Lex (· < ·) (· < ·) (ps i).measure (recr η s ls l ps ms mins is maj).measure :=
  measure_lt_of_mem ps i (le_max_of_le_right (le_max_left _ _)) (by simp only [size, sizeWith]; omega)

theorem measure_recr_motive (i : Fin ι.nsorts) :
    Prod.Lex (· < ·) (· < ·) (ms i).measure (recr η s ls l ps ms mins is maj).measure :=
  measure_lt_of_mem ms i (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
    (by simp only [size, sizeWith]; omega)

theorem measure_recr_case (s₁ : Fin ι.nsorts) (c : Fin (ι.nctors s₁)) :
    Prod.Lex (· < ·) (· < ·) (mins s₁ c).measure
      (recr η s ls l ps ms mins is maj).measure :=
  measure_lt_of_mem (mins s₁) c
    ((Finset.le_sup (f := fun s₂ => Finset.univ.sup fun c => (mins s₂ c).headRank)
      (Finset.mem_univ s₁)).trans (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
        (le_max_left _ _)))))
    ((Finset.single_le_sum (f := fun s₂ => Finset.univ.sum fun c => (mins s₂ c).size)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ s₁)).trans_lt (by simp only [size, sizeWith]; omega))

theorem measure_recr_index (i : Fin (ι.nindices s)) :
    Prod.Lex (· < ·) (· < ·) (is i).measure (recr η s ls l ps ms mins is maj).measure :=
  measure_lt_of_mem is i (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _))))) (by simp only [size, sizeWith]; omega)

theorem measure_recr_major :
    Prod.Lex (· < ·) (· < ·) maj.measure (recr η s ls l ps ms mins is maj).measure := by
  refine measure_lt (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_right _ _))))) ?_
  simp only [size, sizeWith]
  omega

end

end Expr

def Ctx.headRank {a b : Nat} : Ctx ζ ℓ a b → Nat
  | .nil => 0
  | .snoc Γ t => max Γ.headRank t.headRank

namespace Ctx

variable {a b : Nat}

theorem headRank_le_length (Γ : Ctx ζ ℓ a b) : Γ.headRank ≤ 2 * ζ.length := by
  induction Γ with
  | nil => exact Nat.zero_le _
  | snoc Γ t ih => exact max_le ih t.headRank_le_length

@[simp] theorem headRank_map (pre : ζ₁ ⟶ ζ₂) (Γ : Ctx ζ₁ ℓ a b) :
    (Γ.map pre).headRank = Γ.headRank := by
  induction Γ with
  | nil => rfl
  | snoc Γ t ih => exact congrArg₂ max ih (Expr.headRank_map pre t)

@[simp] theorem headRank_instL (ls : Param ℓ → Level ℓ₁) (Γ : Ctx ζ ℓ a b) :
    (Γ.instL ls).headRank = Γ.headRank := by
  induction Γ with
  | nil => rfl
  | snoc Γ t ih => exact congrArg₂ max ih (Expr.headRank_instL ls t)

@[simp] theorem headRank_pi (Δ : Ctx ζ ℓ a b) (e : Expr ζ ℓ b) :
    (Δ.pi e).headRank = max Δ.headRank e.headRank := by
  induction Δ with
  | nil => simp [headRank]
  | snoc Δ t ih =>
    change (Ctx.pi (.forallE t e) Δ).headRank = _
    rw [ih]
    simp [headRank, Expr.headRank, max_assoc]

@[simp] theorem headRank_lam (Δ : Ctx ζ ℓ a b) (e : Expr ζ ℓ b) :
    (Δ.lam e).headRank = max Δ.headRank e.headRank := by
  induction Δ with
  | nil => simp [headRank]
  | snoc Δ t ih =>
    change (Ctx.lam (.lam t e) Δ).headRank = _
    rw [ih]
    simp [headRank, Expr.headRank, max_assoc]

end Ctx

variable {ι : IndSig} {s : Fin ι.nsorts} {nfields : Nat}
  {csig : CtorSig ι.nsorts}

def Field.headRank (fd : Field ζ ι nfields) : Nat :=
  fd.type.headRank

def RecField.headRank {arity : Nat} {target : Fin ι.nsorts}
    (fd : RecField ζ ι nfields arity target) : Nat :=
  max fd.tele.headRank (Finset.univ.sup fun i => (fd.indices i).headRank)

theorem RecField.tele_headRank_le {arity : Nat} {target : Fin ι.nsorts}
    (fd : RecField ζ ι nfields arity target) :
    fd.tele.headRank ≤ fd.headRank :=
  le_max_left _ _

theorem RecField.indices_headRank_le {arity : Nat} {target : Fin ι.nsorts}
    (fd : RecField ζ ι nfields arity target) (i : Fin (ι.nindices target)) :
    (fd.indices i).headRank ≤ fd.headRank :=
  (Finset.le_sup (f := fun i => (fd.indices i).headRank) (Finset.mem_univ i)).trans
    (le_max_right fd.tele.headRank _)

def Ctor.headRank (ctor : Ctor ζ ι s csig) : Nat :=
  max (Finset.univ.sup fun f => (ctor.ordinary f).headRank)
    (max (Finset.univ.sup fun f => (ctor.recursive f).headRank)
      (Finset.univ.sup fun i => (ctor.targetIndices i).headRank))

def Inductive.headRank (I : Inductive ζ ι) : Nat :=
  max I.params.headRank
    (max (Finset.univ.sup fun s => (I.indices s).headRank)
      (Finset.univ.sup fun s => Finset.univ.sup fun c => (I.ctors s c).headRank))

theorem Inductive.headRank_ctors_le (I : Inductive ζ ι) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) :
    (I.ctors s c).headRank ≤ I.headRank :=
  have hinner (g : Fin (ι.nctors s) → Nat) : g c ≤ Finset.univ.sup g :=
    Finset.le_sup (Finset.mem_univ c)
  have houter (g : Fin ι.nsorts → Nat) : g s ≤ Finset.univ.sup g :=
    Finset.le_sup (Finset.mem_univ s)
  le_trans (hinner fun c => (I.ctors s c).headRank)
    (le_trans (houter fun s => Finset.univ.sup fun c => (I.ctors s c).headRank)
      (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem Field.headRank_le_length (fd : Field ζ ι nfields) :
    fd.headRank ≤ 2 * ζ.length :=
  fd.type.headRank_le_length

theorem RecField.headRank_le_length {arity : Nat} {target : Fin ι.nsorts}
    (fd : RecField ζ ι nfields arity target) :
    fd.headRank ≤ 2 * ζ.length :=
  max_le fd.tele.headRank_le_length
    (Finset.sup_le fun i _ => (fd.indices i).headRank_le_length)

theorem Ctor.headRank_le_length (ctor : Ctor ζ ι s csig) : ctor.headRank ≤ 2 * ζ.length :=
  max_le (Finset.sup_le fun f _ => (ctor.ordinary f).headRank_le_length)
    (max_le (Finset.sup_le fun f _ => (ctor.recursive f).headRank_le_length)
      (Finset.sup_le fun i _ => (ctor.targetIndices i).headRank_le_length))

theorem Ctor.headRank_ordinaryTeleAux_le (ctor : Ctor ζ ι s csig) (count : Nat)
    (hcount : count ≤ csig.nfields) :
    Ctx.headRank (ctor.ordinaryTeleAux count hcount) ≤ ctor.headRank := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    exact max_le (ih (by omega))
      ((Finset.le_sup (f := fun f => (ctor.ordinary f).headRank)
        (Finset.mem_univ ⟨count, by omega⟩)).trans (le_max_left _ _))

theorem Inductive.headRank_le_length (I : Inductive ζ ι) : I.headRank ≤ 2 * ζ.length :=
  max_le I.params.headRank_le_length
    (max_le (Finset.sup_le fun s _ => (I.indices s).headRank_le_length)
      (Finset.sup_le fun s _ => Finset.sup_le fun c _ => (I.ctors s c).headRank_le_length))

@[simp] theorem Field.headRank_map (pre : ζ₁ ⟶ ζ₂)
    (fd : Field ζ₁ ι nfields) : (fd.map pre).headRank = fd.headRank :=
  Expr.headRank_map pre fd.type

@[simp] theorem RecField.headRank_map {arity : Nat} {target : Fin ι.nsorts}
    (pre : ζ₁ ⟶ ζ₂) (fd : RecField ζ₁ ι nfields arity target) :
    (fd.map pre).headRank = fd.headRank :=
  congrArg₂ max (Ctx.headRank_map pre fd.tele)
    (Finset.sup_congr rfl fun i _ => Expr.headRank_map pre (fd.indices i))

@[simp] theorem Ctor.headRank_map (pre : ζ₁ ⟶ ζ₂) (ctor : Ctor ζ₁ ι s csig) :
    (ctor.map pre).headRank = ctor.headRank :=
  congrArg₂ max (Finset.sup_congr rfl fun f _ => Field.headRank_map pre (ctor.ordinary f))
    (congrArg₂ max (Finset.sup_congr rfl fun f _ => RecField.headRank_map pre (ctor.recursive f))
      (Finset.sup_congr rfl fun i _ => Expr.headRank_map pre (ctor.targetIndices i)))

@[simp] theorem Inductive.headRank_map (pre : ζ₁ ⟶ ζ₂) (I : Inductive ζ₁ ι) :
    (I.map pre).headRank = I.headRank :=
  congrArg₂ max (Ctx.headRank_map pre I.params)
    (congrArg₂ max (Finset.sup_congr rfl fun s _ => Ctx.headRank_map pre (I.indices s))
      (Finset.sup_congr rfl fun s _ =>
        Finset.sup_congr rfl fun c _ => Ctor.headRank_map pre (I.ctors s c)))

theorem Env.get_block_headRank_lt (E : Env ζ) (η : Head ζ (.inductive ι)) :
    (E.get η).block.headRank < η.rank - 1 := by
  induction E with
  | nil => cases η
  | @snoc ζ _ E entry ih =>
    cases η with
    | here =>
      cases entry with
      | «inductive» I =>
        change (I.map _).headRank < 2 * ζ.length + 1
        rw [Inductive.headRank_map]
        exact Nat.lt_succ_of_le I.headRank_le_length
    | there η =>
      simpa [Env.get, Entry.weakenEnv, Head.rank, Head.position, dsimp% (Entry.blockNatTrans _).naturality_apply] using ih η

theorem Env.get_defValue_headRank_lt {nlevels : Nat} (E : Env ζ)
    (η : Head ζ (.const .def nlevels)) : (E.get η).defValue.headRank < η.rank := by
  induction E with
  | nil => cases η
  | @snoc ζ _ E entry ih =>
    cases η with
    | here =>
      cases entry with
      | «def» t e =>
        change (e.map _).headRank < 2 * ζ.length + 2
        rw [Expr.headRank_map]
        exact lt_of_le_of_lt e.headRank_le_length (by omega)
    | there η =>
      simpa [Env.get, Entry.weakenEnv, Head.rank, Head.position, dsimp% (Entry.defValueNatTrans _).naturality_apply] using ih η

theorem Expr.measure_const_def {nlevels : Nat} {E : Env ζ} (η : Head ζ (.const .def nlevels))
    (ls : Fin nlevels → Level ℓ) :
    Prod.Lex (· < ·) (· < ·) (((E.get η).defValue.instL ls).wkClosed (n := n)).measure
      (Expr.const η ls : Expr ζ ℓ n).measure :=
  .left _ _ (by simpa [Expr.measure, Expr.headRank] using E.get_defValue_headRank_lt η)

section RecursorRank

variable {m r : Nat}

theorem Expr.headRank_apps_le {e : Expr ζ ℓ n} {k : Nat} {args : Fin k → Expr ζ ℓ n}
    (he : e.headRank ≤ r) (hargs : ∀ i, (args i).headRank ≤ r) : (e.apps args).headRank ≤ r := by
  induction k with
  | zero => simpa using he
  | succ k ih =>
    rw [Expr.apps_last]
    exact max_le (ih fun i => hargs i.castSucc) (hargs (Fin.last k))

theorem Expr.headRank_ind_le {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
    {ls : Fin ι.nlevels → Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ n}
    {is : Fin (ι.nindices s) → Expr ζ ℓ n} (hη : η.rank - 1 ≤ r)
    (hps : ∀ i, (ps i).headRank ≤ r) (his : ∀ i, (is i).headRank ≤ r) :
    (Expr.ind η s ls ps is).headRank ≤ r :=
  max_le hη (max_le (Finset.sup_le fun i _ => hps i) (Finset.sup_le fun i _ => his i))

theorem Expr.headRank_ctor_le {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
    {ls : Fin ι.nlevels → Level ℓ} {ps : Fin ι.nparams → Expr ζ ℓ n}
    {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n} {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}
    (hη : η.rank - 1 ≤ r) (hps : ∀ i, (ps i).headRank ≤ r) (hfds : ∀ i, (fds i).headRank ≤ r)
    (hrecFds : ∀ i, (recFds i).headRank ≤ r) :
    (Expr.ctor η s c ls ps fds recFds).headRank ≤ r :=
  max_le hη (max_le (Finset.sup_le fun i _ => hps i)
    (max_le (Finset.sup_le fun i _ => hfds i) (Finset.sup_le fun i _ => hrecFds i)))

theorem Expr.headRank_motiveResult_le {k : Nat} {e maj : Expr ζ ℓ n} {is : Fin k → Expr ζ ℓ n}
    (he : e.headRank ≤ r) (his : ∀ i, (is i).headRank ≤ r) (hmaj : maj.headRank ≤ r) :
    (Inductive.motiveResult e is maj).headRank ≤ r :=
  max_le (Expr.headRank_apps_le he his) hmaj

theorem Expr.headRank_var_le (v : Var n) : (Expr.var v : Expr ζ ℓ n).headRank ≤ r :=
  Nat.zero_le _

theorem Head.lt_rank_of_le {sig : Sig} {η : Head ζ sig} (h : r ≤ η.rank - 1) : r < η.rank :=
  lt_of_le_of_lt h (Nat.sub_lt η.rank_pos Nat.one_pos)

theorem Fin.headRank_append_le {a b : Nat} {σ₁ : Fin a → Expr ζ ℓ n} {σ₂ : Fin b → Expr ζ ℓ n}
    (h₁ : ∀ i, (σ₁ i).headRank ≤ r) (h₂ : ∀ j, (σ₂ j).headRank ≤ r) (v : Fin (a + b)) :
    (Fin.append σ₁ σ₂ v).headRank ≤ r := by
  cases v using Fin.addCases with
  | left i => simpa using h₁ i
  | right j => simpa using h₂ j

theorem Subst.headRank_liftN_le {σ : Subst ζ ℓ n m} (hσ : ∀ v, (σ v).headRank ≤ r) (k : Nat)
    (v : Fin (n + k)) : (σ.liftN k v).headRank ≤ r := by
  induction k with
  | zero => exact hσ v
  | succ k ih =>
    cases v using Fin.lastCases with
    | last => simp [Subst.liftN, Expr.headRank]
    | cast v => simpa [Subst.liftN, Expr.wk, Expr.wkFrom] using ih v

theorem Ctx.headRank_append_le {a b c : Nat} {Γ : Ctx ζ ℓ a b} {Δ : Ctx ζ ℓ b c}
    (hΓ : Γ.headRank ≤ r) (hΔ : Δ.headRank ≤ r) : Ctx.headRank (Γ ++ Δ) ≤ r := by
  induction Δ with
  | nil => exact hΓ
  | snoc Δ t ih => exact max_le (ih (le_trans (le_max_left _ _) hΔ)) (le_trans (le_max_right _ _) hΔ)

theorem Ctx.headRank_ofTypes_le {k : Nat} {types : Fin k → Expr ζ ℓ n}
    (h : ∀ i, (types i).headRank ≤ r) : (Ctx.ofTypes types).headRank ≤ r := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih => exact max_le (ih fun i => h i.castSucc) (by simpa using h (Fin.last k))

theorem Ctx.headRank_substN_le (σ : Subst ζ ℓ n m) {k : Nat} {Θ : Ctx ζ ℓ n (n + k)}
    (hΘ : Θ.headRank ≤ r) (hσ : ∀ v, (σ v).headRank ≤ r) : (Ctx.substN σ k Θ).headRank ≤ r := by
  induction Θ using Tele.addInduction with
  | nil => exact Nat.zero_le _
  | snoc k Θ t ih =>
    exact max_le (ih (le_trans (le_max_left _ _) hΘ))
      (Expr.headRank_subst_le t _ r (le_trans (le_max_right _ _) hΘ) (Subst.headRank_liftN_le hσ k))

theorem Inductive.headRank_params_le (I : Inductive ζ ι) : I.params.headRank ≤ I.headRank :=
  le_max_left _ _

theorem Inductive.headRank_indices_le (I : Inductive ζ ι) (s : Fin ι.nsorts) :
    (I.indices s).headRank ≤ I.headRank :=
  (Finset.le_sup (f := fun s => (I.indices s).headRank) (Finset.mem_univ s)).trans
    ((le_max_left _ _).trans (le_max_right _ _))

theorem Ctor.headRank_recursive_le (ctor : Ctor ζ ι s csig) (f : Fin csig.nrecFields) :
    (ctor.recursive f).headRank ≤ ctor.headRank :=
  (Finset.le_sup (f := fun f => (ctor.recursive f).headRank) (Finset.mem_univ f)).trans
    ((le_max_left _ _).trans (le_max_right _ _))

theorem Ctor.headRank_targetIndices_le (ctor : Ctor ζ ι s csig) (i : Fin (ι.nindices s)) :
    (ctor.targetIndices i).headRank ≤ ctor.headRank :=
  (Finset.le_sup (f := fun i => (ctor.targetIndices i).headRank) (Finset.mem_univ i)).trans
    ((le_max_right _ _).trans (le_max_right _ _))

variable {arity : Nat} {target : Fin ι.nsorts} {fd : RecField ζ ι nfields arity target}
  {ls : Fin ι.nlevels → Level ℓ} {σ : Subst ζ ℓ (ι.nparams + nfields) n}

theorem RecField.headRank_instantiatedTelescope_le (hfd : fd.headRank ≤ r)
    (hσ : ∀ v, (σ v).headRank ≤ r) : (fd.instantiatedTelescope ls σ).headRank ≤ r :=
  Ctx.headRank_substN_le σ (by simpa using fd.tele_headRank_le.trans hfd) hσ

theorem RecField.headRank_instantiatedIndices_le (hfd : fd.headRank ≤ r)
    (hσ : ∀ v, (σ v).headRank ≤ r) (i : Fin (ι.nindices target)) :
    (fd.instantiatedIndices ls σ i).headRank ≤ r :=
  Expr.headRank_subst_le _ _ r (by simpa using (fd.indices_headRank_le i).trans hfd)
    (Subst.headRank_liftN_le hσ arity)

theorem RecField.headRank_instantiatedType_le {η : Head ζ (.inductive ι)}
    {ps : Fin ι.nparams → Expr ζ ℓ n} (hfd : fd.headRank ≤ r) (hη : η.rank - 1 ≤ r)
    (hps : ∀ p, (ps p).headRank ≤ r) (hσ : ∀ v, (σ v).headRank ≤ r) :
    (fd.instantiatedType η ls ps σ).headRank ≤ r := by
  rw [RecField.instantiatedType, Ctx.headRank_pi]
  exact max_le (headRank_instantiatedTelescope_le hfd hσ)
    (Expr.headRank_ind_le hη (fun p => by simpa using hps p) (headRank_instantiatedIndices_le hfd hσ))

theorem RecField.headRank_ihType_le {ms : Fin ι.nsorts → Expr ζ ℓ n} {e : Expr ζ ℓ n}
    (hfd : fd.headRank ≤ r) (hms : ∀ t, (ms t).headRank ≤ r) (hσ : ∀ v, (σ v).headRank ≤ r)
    (he : e.headRank ≤ r) : (fd.ihType ls ms σ e).headRank ≤ r := by
  rw [RecField.ihType, Ctx.headRank_pi]
  exact max_le (headRank_instantiatedTelescope_le hfd hσ)
    (Expr.headRank_motiveResult_le (by simpa using hms target)
      (headRank_instantiatedIndices_le hfd hσ) (by simpa using he))

variable {I : Inductive ζ ι} {η : Head ζ (.inductive ι)} {l : Level ℓ}
  {c : Fin (ι.nctors s)} {ps : Fin ι.nparams → Expr ζ ℓ n} {ms : Fin ι.nsorts → Expr ζ ℓ n}
  (hI : I.headRank ≤ r) (hη : η.rank - 1 ≤ r) (hps : ∀ p, (ps p).headRank ≤ r)
  (hms : ∀ t, (ms t).headRank ≤ r)

include hI

theorem Inductive.headRank_recursive_le (f : Fin (ι.ctors s c).nrecFields) :
    ((I.ctors s c).recursive f).headRank ≤ r :=
  ((I.ctors s c).headRank_recursive_le f).trans ((I.headRank_ctors_le s c).trans hI)

include hps in
theorem Inductive.headRank_indexTele_le : (I.indexTele ls s ps).headRank ≤ r :=
  Ctx.headRank_substN_le ps (by simpa using (I.headRank_indices_le s).trans hI) hps

include hη hps in
theorem Inductive.headRank_motiveTele_le : (I.motiveTele η ls ps s).headRank ≤ r :=
  max_le (headRank_indexTele_le hI hps)
    (Expr.headRank_ind_le hη (fun p => by simpa using hps p) fun _ => Expr.headRank_var_le _)

include hη hps in
theorem Inductive.headRank_motiveType_le : (I.motiveType η ls ps l s).headRank ≤ r := by
  rw [Inductive.motiveType, Ctx.headRank_pi]
  exact max_le (headRank_motiveTele_le hI hη hps) (Nat.zero_le _)

include hη hps in
theorem Inductive.headRank_fieldTele_le : ((I.ctors s c).fieldTele η ls ps).headRank ≤ r := by
  refine Ctx.headRank_append_le (Ctx.headRank_substN_le ps ?_ hps) ?_
  · simpa using ((I.ctors s c).headRank_ordinaryTeleAux_le _ _).trans ((I.headRank_ctors_le s c).trans hI)
  · exact Ctx.headRank_ofTypes_le fun f => RecField.headRank_instantiatedType_le
      (headRank_recursive_le hI _) hη (fun p => by simpa using hps p)
      (Fin.headRank_append_le (fun p => by simpa using hps p)
        fun _ => by simp [Expr.boundVars, Expr.headRank])

include hη hps hms in
theorem Inductive.headRank_caseFnType_le : (I.caseFnType η ls ps ms s c).headRank ≤ r := by
  have hparams (p : Fin ι.nparams) : ((ι.ctors s c).fieldParams ps p).headRank ≤ r := by
    simpa [CtorSig.fieldParams] using hps p
  have hsubst (v : Fin (ι.nparams + (ι.ctors s c).nfields)) :
      (Fin.append ((ι.ctors s c).fieldParams ps) (ι.ctors s c).fieldOrdinary v).headRank ≤ r :=
    Fin.headRank_append_le hparams (fun _ => by simp [CtorSig.fieldOrdinary, Expr.headRank]) v
  have hcase (v : Fin (ι.nparams + (ι.ctors s c).nfields)) :
      (Fin.append ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary v).headRank ≤ r :=
    Fin.headRank_append_le (fun p => by simpa [CtorSig.caseParams] using hparams p)
      (fun _ => by simp [CtorSig.caseOrdinary, CtorSig.fieldOrdinary, Expr.headRank]) v
  have hindex (i : Fin (ι.nindices s)) :
      ((I.ctors s c).targetIndex ls ((ι.ctors s c).caseParams ps) (ι.ctors s c).caseOrdinary i).headRank ≤
        r := by
    refine Expr.headRank_subst_le _ _ r ?_ hcase
    simpa using ((I.ctors s c).headRank_targetIndices_le i).trans ((I.headRank_ctors_le s c).trans hI)
  have hih (f : Fin (ι.ctors s c).nrecFields) : ((I.ctors s c).ihType ls ps ms f).headRank ≤ r := by
    unfold Ctor.ihType Ctor.ihTypeWith
    exact RecField.headRank_ihType_le (headRank_recursive_le hI f) (fun t => by simpa using hms t) hsubst
      (Expr.headRank_var_le _)
  rw [Inductive.caseFnType, Ctx.headRank_pi]
  refine max_le (Ctx.headRank_append_le (headRank_fieldTele_le hI hη hps)
    (Ctx.headRank_ofTypes_le fun f => hih _)) (Expr.headRank_motiveResult_le (by simpa using hms s) hindex
      (Expr.headRank_ctor_le hη (fun p => by simpa [CtorSig.caseParams] using hparams p)
        (fun _ => by simp [CtorSig.caseOrdinary, CtorSig.fieldOrdinary, Expr.headRank])
        fun _ => by simp [CtorSig.caseRecursive, CtorSig.fieldRecursive, Expr.headRank]))

include hη in
theorem Inductive.headRank_recrTele_le : (I.recrTele η s ls l).headRank ≤ r := by
  refine max_le (Ctx.headRank_append_le (Ctx.headRank_append_le (Ctx.headRank_append_le
    (by simpa using I.headRank_params_le.trans hI) ?_) ?_) ?_) ?_
  · exact Ctx.headRank_ofTypes_le fun t =>
      headRank_motiveType_le hI hη fun _ => Expr.headRank_var_le _
  · refine Ctx.headRank_ofTypes_le fun tag => ?_
    obtain ⟨⟨t, c⟩, rfl⟩ : ∃ point, Fin.encodeSigma ι.nctors point = tag :=
      ⟨_, Fin.encodeSigma_decodeSigma ..⟩
    rw [Fin.decodeSigma_encodeSigma]
    exact headRank_caseFnType_le hI hη (fun _ => Expr.headRank_var_le _)
      fun _ => Expr.headRank_var_le _
  · exact headRank_indexTele_le hI fun _ => Expr.headRank_var_le _
  · exact Expr.headRank_ind_le hη (fun p => by simp [Expr.headRank]) fun _ => Expr.headRank_var_le _

end RecursorRank

end Metalean
