/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Ctx

@[expose] public section

namespace Metalean

variable {ζ : Sigs}
  {ℓ n m cut cutPos d a b k nsorts nparams nfields : Nat}
  {ι : IndSig} {s : Fin ι.nsorts}

namespace Subst

def wkFrom (cut : Nat) : Subst ζ ℓ n (n + 1) := fun v => .var (Ren.wkFrom cut v)

end Subst

namespace Ctx

def wkFrom {ζ : Sigs} {ℓ a : Nat} (cut : Nat) {b : Nat} :
    Ctx ζ ℓ a b → Ctx ζ ℓ (a + 1) (b + 1)
  | .nil => .nil
  | .snoc Γ A => .snoc (wkFrom cut Γ) (A.wkFrom cut)

def insert (Γ : Ctx ζ ℓ 0 cut) (t : Expr ζ ℓ cut)
    (Δ : Ctx ζ ℓ cut n) : Ctx ζ ℓ 0 (n + 1) :=
  Γ.snoc t ++ Δ.wkFrom cut

end Ctx

namespace Expr

theorem wkFrom_eq_subst (cut : Nat) (e : Expr ζ ℓ n) :
    e.wkFrom cut = e.subst (Subst.wkFrom cut) :=
  (subst_vars _ e).symm

theorem wkN_eq_subst (e : Expr ζ ℓ n) (k : Nat) :
    e.wkN k = e.subst fun v => .var (Ren.wkN k v) := by
  simp [wkN_eq_rename]

@[simp] theorem wkFrom_var (cut : Nat) (v : Var n) :
    (Expr.var v : Expr ζ ℓ n).wkFrom cut =
      if v.val < cut then .var v.castSucc else .var v.succ := by
  simp [wkFrom, rename, Ren.wkFrom]
  split <;> rfl

@[simp] theorem wkFrom_wkFrom (h : cut ≤ d) (e : Expr ζ ℓ n) :
    (e.wkFrom d).wkFrom cut = (e.wkFrom cut).wkFrom (d + 1) := by
  simp [wkFrom, Ren.wkFrom_comm h]

@[simp] theorem subst_wkFrom (σ : Subst ζ ℓ m n) (e : Expr ζ ℓ m) :
    (e.subst σ).wkFrom cut = e.subst fun v => (σ v).wkFrom cut := by
  simp [wkFrom]
  congr 1

theorem wkClosed_of_rename {f : (n : Nat) → Expr ζ ℓ n}
    (hf : ∀ {m k : Nat} (ρ : Ren m k), (f m).rename ρ = f k) :
    (n : Nat) → (f 0).wkClosed (n := n) = f n
  | 0 => rfl
  | n + 1 => by
    rw [wkClosed, wkClosed_of_rename hf n]
    exact hf _

@[simp] theorem wkClosed_wkFrom (e : Expr ζ ℓ 0) :
    {n : Nat} → cut ≤ n → e.wkClosed (n := n).wkFrom cut =
      e.wkClosed (n := n + 1)
  | 0, h => by
      obtain rfl : cut = 0 := Nat.eq_zero_of_le_zero h
      rfl
  | n + 1, h => by
      by_cases hc : cut = n + 1
      · subst cut
        rfl
      · have hcn : cut ≤ n := by omega
        change (e.wkClosed (n := n).wkFrom n).wkFrom cut =
          e.wkClosed (n := n + 1).wk
        rw [wkFrom_wkFrom hcn, wkClosed_wkFrom e hcn]
        rfl

end Expr

namespace Expr

@[simp] theorem wkFrom_sort (l : Level ℓ) :
    (Expr.sort l : Expr ζ ℓ n).wkFrom cut = .sort l := rfl

@[simp] theorem wkFrom_var' (cut : Nat) (v : Var n) :
    (Expr.var v : Expr ζ ℓ n).wkFrom cut = .var (Ren.wkFrom cut v) := by
  simp [Ren.wkFrom]
  split <;> rfl

@[simp] theorem var_wkFrom_ge (v : Var n) (h : cut ≤ v.val) :
    (Expr.var v : Expr ζ ℓ n).wkFrom cut = .var v.succ := by
  simp [h]

@[simp] theorem last_wkFrom (h : cut ≤ n) :
    (Expr.var (Fin.last n) : Expr ζ ℓ (n + 1)).wkFrom cut =
      .var (Fin.last (n + 1)) := by
  simp [var_wkFrom_ge (Fin.last n) (by simp [Fin.last]; omega)]

@[simp] theorem wkFrom_app (f e : Expr ζ ℓ n) :
    (Expr.app f e).wkFrom cut = Expr.app (f.wkFrom cut) (e.wkFrom cut) := rfl

@[simp] theorem wkFrom_apps (η : Expr ζ ℓ n)
    (args : Fin k → Expr ζ ℓ n) :
    (η.apps args).wkFrom cut =
      (η.wkFrom cut).apps fun i => (args i).wkFrom cut := by
  induction k generalizing η with
  | zero => rfl
  | succ k ih =>
    rw [apps_succ, ih, wkFrom_app, apps_succ]

@[simp] theorem wkFrom_lam (h : cut ≤ n) (t : Expr ζ ℓ n)
    (e' : Expr ζ ℓ (n + 1)) :
    (Expr.lam t e').wkFrom cut = Expr.lam (t.wkFrom cut) (e'.wkFrom cut) := by
  simp [wkFrom, rename, Ren.wkFrom_lift cut h]

@[simp] theorem wkFrom_forallE (h : cut ≤ n) (t : Expr ζ ℓ n)
    (e' : Expr ζ ℓ (n + 1)) :
    (Expr.forallE t e').wkFrom cut =
      Expr.forallE (t.wkFrom cut) (e'.wkFrom cut) := by
  simp [wkFrom, rename, Ren.wkFrom_lift cut h]

@[simp] theorem wkFrom_letE (h : cut ≤ n) (t v : Expr ζ ℓ n)
    (e' : Expr ζ ℓ (n + 1)) :
    (Expr.letE t v e').wkFrom cut =
      Expr.letE (t.wkFrom cut) (v.wkFrom cut) (e'.wkFrom cut) := by
  simp [wkFrom, rename, Ren.wkFrom_lift cut h]

@[simp] theorem wk_wkFrom (h : cut ≤ n) (e : Expr ζ ℓ n) :
    e.wk.wkFrom cut = (e.wkFrom cut).wk :=
  wkFrom_wkFrom h e

end Expr

namespace Expr

theorem wkFrom_subst (σ : Subst ζ ℓ (m + 1) n) (e : Expr ζ ℓ m) :
    (e.wkFrom cut).subst σ =
      e.subst fun v => σ (Ren.wkFrom cut v) := by
  simp [wkFrom]
  congr 1

@[simp] theorem inst_wkFrom (h : cut ≤ n) (t' : Expr ζ ℓ (n + 1))
    (e : Expr ζ ℓ n) :
    (t'.inst e).wkFrom cut = (t'.wkFrom cut).inst (e.wkFrom cut) := by
  change (t'.subst _).wkFrom cut = (t'.wkFrom cut).subst _
  rw [subst_wkFrom, wkFrom_subst]
  congr 1
  funext v
  change Expr.wkFrom cut (dite _ _ _) = dite _ _ _
  by_cases hv : v.val < n
  · have hs : (Ren.wkFrom cut v).val < n + 1 := by
      by_cases hc : v.val < cut
      · simp [Ren.wkFrom, hc]
      · simpa [Ren.wkFrom, hc] using hv
    rw [dite_eq_left hv]
    change _ = if h : (Ren.wkFrom cut v).val < n + 1 then _ else _
    rw [dite_eq_left hs]
    simp [Subst.id]
    by_cases hc : v.val < cut
    · rw [ite_eq_left hc]
      apply congrArg Expr.var
      apply Fin.ext
      simp [Ren.wkFrom, hc]
    · rw [ite_eq_right hc]
      apply congrArg Expr.var
      apply Fin.ext
      simp [Ren.wkFrom, hc]
  · have hs : ¬(Ren.wkFrom cut v).val < n + 1 := by
      have hvn : v.val = n := by omega
      rw [Ren.wkFrom_of_ge v (by omega)]
      simp [hvn]
    rw [dite_eq_right hv]
    change _ = if h : (Ren.wkFrom cut v).val < n + 1 then _ else _
    rw [dite_eq_right hs]
    simp

@[simp] theorem wkFrom_const {kind : ConstKind} {nlevels : Nat}
    (η : Head ζ (.const kind nlevels)) (ls : Fin nlevels → Level ℓ) :
    (Expr.const η ls : Expr ζ ℓ n).wkFrom cutPos = .const η ls := rfl

@[simp] theorem wkFrom_ind (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) :
    (Expr.ind η s ls ps is).wkFrom cutPos =
      .ind η s ls (fun i => (ps i).wkFrom cutPos)
        fun i => (is i).wkFrom cutPos := rfl

@[simp] theorem wkFrom_ctor {d : Nat} (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n) :
    (Expr.ctor η s c ls ps fds recFds).wkFrom d =
      .ctor η s c ls (fun i => (ps i).wkFrom d)
        (fun i => (fds i).wkFrom d)
        fun i => (recFds i).wkFrom d := rfl

@[simp] theorem wkFrom_recr {d : Nat} (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (l : Level ℓ) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (ms : Fin ι.nsorts → Expr ζ ℓ n)
    (mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n)
    (maj : Expr ζ ℓ n) :
    (Expr.recr η s ls l ps ms mins is maj).wkFrom d =
      .recr η s ls l
        (fun i => (ps i).wkFrom d)
        (fun s => (ms s).wkFrom d)
        (fun s c => (mins s c).wkFrom d)
        (fun i => (is i).wkFrom d) (maj.wkFrom d) := rfl

@[simp] theorem wkFrom_quot (η : Head ζ .quot) (l : Level ℓ)
    (α r : Expr ζ ℓ n) :
    (Expr.quot η l α r).wkFrom cutPos =
      .quot η l (α.wkFrom cutPos) (r.wkFrom cutPos) := rfl

@[simp] theorem wkFrom_quotMk (η : Head ζ .quot) (l : Level ℓ)
    (α r x : Expr ζ ℓ n) :
    (Expr.quotMk η l α r x).wkFrom cutPos =
      .quotMk η l (α.wkFrom cutPos) (r.wkFrom cutPos) (x.wkFrom cutPos) := rfl

@[simp] theorem wkFrom_quotLift (η : Head ζ .quot) (l₁ l₂ : Level ℓ)
    (α r β f h a : Expr ζ ℓ n) :
    (Expr.quotLift η l₁ l₂ α r β f h a).wkFrom cutPos =
      .quotLift η l₁ l₂ (α.wkFrom cutPos) (r.wkFrom cutPos) (β.wkFrom cutPos)
        (f.wkFrom cutPos) (h.wkFrom cutPos) (a.wkFrom cutPos) := rfl

@[simp] theorem wkFrom_quotInd (η : Head ζ .quot) (l : Level ℓ)
    (α r β f a : Expr ζ ℓ n) :
    (Expr.quotInd η l α r β f a).wkFrom cutPos =
      .quotInd η l (α.wkFrom cutPos) (r.wkFrom cutPos)
        (β.wkFrom cutPos) (f.wkFrom cutPos) (a.wkFrom cutPos) := rfl

end Expr

namespace Ctx

@[simp] theorem get_snoc (Γ : Ctx ζ ℓ 0 n) (t : Expr ζ ℓ n)
    (v : Var (n + 1)) (h : v.val ≠ n) :
    (Γ.snoc t).get v = (Γ.get (v.castLT (by omega))).wk := by
  simp [get, h]

@[simp] theorem get_castSucc (Γ : Ctx ζ ℓ 0 n) (t : Expr ζ ℓ n) (v : Var n) :
    (Γ.snoc t).get v.castSucc = (Γ.get v).wk := by
  simp [get, v.isLt.ne]

@[simp] theorem get_append (Γ : Ctx ζ ℓ 0 n) (Δ : Ctx ζ ℓ n (n + k))
    (v : Var n) :
    Ctx.get (v.castAdd k) (Γ ++ Δ) = (Γ.get v).wkN k := by
  induction Δ using Tele.addInduction with
  | nil => rfl
  | snoc k Δ A ih =>
    rw [Tele.append_snoc, get_snoc _ _ _ (by simp; omega)]
    change (Ctx.get (v.castAdd k) (Γ ++ Δ)).wk = _
    rw [ih]
    rfl

theorem get_insert (Γ₀ : Ctx ζ ℓ 0 cutPos) (t : Expr ζ ℓ cutPos)
    {n : Nat} (Δ : Ctx ζ ℓ cutPos n) (v : Var n) :
    Ctx.get (Ren.wkFrom cutPos v) (Γ₀.insert t Δ) =
      (Ctx.get v (Γ₀ ++ Δ)).wkFrom cutPos := by
  induction Δ with
  | nil =>
    rw [insert, Ctx.wkFrom, Ren.wkFrom_of_lt v v.isLt]
    exact Γ₀.get_snoc t v.castSucc (Nat.ne_of_lt v.isLt)
  | @snoc m Δ t₁ ih =>
    rw [insert, Ctx.wkFrom, Tele.append_snoc, Tele.append_snoc]
    have hcm : cutPos ≤ m := Tele.le Δ
    by_cases hv : v.val = m
    · have hs : (Ren.wkFrom cutPos v).val = m + 1 := by
        rw [Ren.wkFrom_of_ge v (by omega)]
        change v.val + 1 = m + 1
        omega
      rw [Ctx.get, Ctx.get, dite_eq_left hs, dite_eq_left hv]
      exact (t₁.wk_wkFrom hcm).symm
    · have hlt : v.val < m := by omega
      have hs : (Ren.wkFrom cutPos v).val ≠ m + 1 := by
        by_cases hc : v.val < cutPos <;> simp [Ren.wkFrom, hc] <;> omega
      have hb : (Ren.wkFrom cutPos v).val < m + 1 := by
        by_cases hc : v.val < cutPos
        · simp [Ren.wkFrom, hc]
        · simpa [Ren.wkFrom, hc] using hlt
      have he : (Ren.wkFrom cutPos v).castLT hb = Ren.wkFrom cutPos (v.castLT hlt) := by
        ext
        by_cases hc : v.val < cutPos <;> simp [Ren.wkFrom, hc]
      rw [Ctx.get, Ctx.get, dite_eq_right hs, dite_eq_right hv, he]
      change ((Γ₀.insert t Δ).get (Ren.wkFrom cutPos (v.castLT hlt))).wk = _
      rw [ih (v.castLT hlt)]
      exact (Expr.wk_wkFrom hcm _).symm

@[simp] theorem insert_snoc (Γ : Ctx ζ ℓ 0 cutPos) (t : Expr ζ ℓ cutPos)
    (Δ : Ctx ζ ℓ cutPos n) (t₁ : Expr ζ ℓ n) :
    Γ.insert t (Δ.snoc t₁) = (Γ.insert t Δ).snoc (t₁.wkFrom cutPos) := rfl

@[simp] theorem insert_nil (Γ : Ctx ζ ℓ 0 n) (t : Expr ζ ℓ n) :
    Γ.insert t (.nil : Ctx ζ ℓ n n) = Γ.snoc t := rfl

end Ctx

@[simp] theorem Expr.inst_rename (ρ : Ren n m) (e' : Expr ζ ℓ (n + 1))
    (e : Expr ζ ℓ n) :
    (e'.inst e).rename ρ = (e'.rename ρ.lift).inst (e.rename ρ) := by
  simp [Expr.inst]
  congr 1
  funext v
  cases v using Fin.lastCases <;> simp [Subst.rename, Subst.precomp, Subst.id, Expr.rename]

theorem Expr.var_wk {ℓ n : Nat} (v : Var n) : (Expr.var v : Expr ζ ℓ n).wk = .var v.castSucc := by
  simp [Expr.wk, Expr.wkFrom, Expr.rename, Ren.wkFrom, v.isLt]

end Metalean
