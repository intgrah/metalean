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
  simp [wkFrom, Ren.wkFrom]
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

end Expr

namespace Expr

@[simp] theorem wkFrom_sort (l : Level ℓ) :
    (Expr.sort l : Expr ζ ℓ n).wkFrom cut = .sort l := rfl

@[simp] theorem wkFrom_lam (h : cut ≤ n) (t : Expr ζ ℓ n)
    (e' : Expr ζ ℓ (n + 1)) :
    (Expr.lam t e').wkFrom cut = Expr.lam (t.wkFrom cut) (e'.wkFrom cut) := by
  simp [wkFrom, Ren.wkFrom_lift cut h]

@[simp] theorem wkFrom_forallE (h : cut ≤ n) (t : Expr ζ ℓ n)
    (e' : Expr ζ ℓ (n + 1)) :
    (Expr.forallE t e').wkFrom cut =
      Expr.forallE (t.wkFrom cut) (e'.wkFrom cut) := by
  simp [wkFrom, Ren.wkFrom_lift cut h]

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

@[simp] theorem wkFrom_ind (η : Head ζ (.inductive ι))
    (s : Fin ι.nsorts) (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) :
    (Expr.ind η s ls ps is).wkFrom cutPos =
      .ind η s ls (fun i => (ps i).wkFrom cutPos)
        fun i => (is i).wkFrom cutPos := rfl

@[simp] theorem wkFrom_quot (η : Head ζ .quot) (l : Level ℓ)
    (α r : Expr ζ ℓ n) :
    (Expr.quot η l α r).wkFrom cutPos =
      .quot η l (α.wkFrom cutPos) (r.wkFrom cutPos) := rfl

end Expr

namespace Ctx

@[simp] theorem get_snoc (Γ : Ctx ζ ℓ 0 n) (t : Expr ζ ℓ n)
    (v : Var (n + 1)) (h : v.val ≠ n) :
    (Γ.snoc t).get v = (Γ.get (v.castLT (by omega))).wk := by
  simp! [h]

@[simp] theorem get_castSucc (Γ : Ctx ζ ℓ 0 n) (t : Expr ζ ℓ n) (v : Var n) :
    (Γ.snoc t).get v.castSucc = (Γ.get v).wk := by
  simp [v.isLt.ne]

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
    rw [Ren.wkFrom_of_lt v v.isLt]
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
        · simp [hc]
        · simpa [Ren.wkFrom, hc] using hlt
      have he : (Ren.wkFrom cutPos v).castLT hb = Ren.wkFrom cutPos (v.castLT hlt) := by
        ext
        by_cases hc : v.val < cutPos <;> simp [Ren.wkFrom, hc]
      rw [Ctx.get, Ctx.get, dite_eq_right hs, dite_eq_right hv, he]
      change ((Γ₀.insert t Δ).get (Ren.wkFrom cutPos (v.castLT hlt))).wk = _
      rw [ih (v.castLT hlt)]
      exact (Expr.wk_wkFrom hcm _).symm

end Ctx

@[simp] theorem Expr.var_wk {ℓ n : Nat} (v : Var n) : (Expr.var v : Expr ζ ℓ n).wk = .var v.castSucc := by
  simp [Expr.wk, Expr.wkFrom]

end Metalean
