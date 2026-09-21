/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Inductive.Iota
public import Metalean.Syntax.Quot
public import Metalean.Syntax.Weakening

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ : Sigs}
variable {ℓ n m p a b k count nsorts nparams nfields arity : Nat}
variable {ι : IndSig} {s target : Fin ι.nsorts}
variable {csig : CtorSig ι.nsorts}
variable (I : Inductive ζ ι) (ctor : Ctor ζ ι s csig)
variable (η : Head ζ (.inductive ι)) (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ)
variable (ps : Fin ι.nparams → Expr ζ ℓ m) (ms : Fin ι.nsorts → Expr ζ ℓ m)
variable (mins : (t : Fin ι.nsorts) → Fin (ι.nctors t) → Expr ζ ℓ m)
variable (σ : Subst ζ ℓ m n)

@[simp] theorem Expr.subst_appList (e : Expr ζ ℓ m) (args : List (Expr ζ ℓ m)) :
    (e.appList args).subst σ =
      (e.subst σ).appList (args.map fun arg => arg.subst σ) :=
  letI := Subst.category ζ ℓ
  Expr.appSubstHom.listFold.naturality_apply σ ⟨e, args⟩ |>.symm

@[simp] theorem Expr.subst_app (f e : Expr ζ ℓ m) :
    (f.app e).subst σ = (f.subst σ).app (e.subst σ) := rfl

@[simp] theorem Expr.inst_app (f e : Expr ζ ℓ (n + 1)) (value : Expr ζ ℓ n) :
    (f.app e).inst value = (f.inst value).app (e.inst value) := rfl

@[simp] theorem Expr.subst_apps (e : Expr ζ ℓ m) (args : Fin k → Expr ζ ℓ m) :
    (e.apps args).subst σ =
      (e.subst σ).apps fun i => (args i).subst σ :=
  letI := Subst.category ζ ℓ
  (Expr.appSubstHom.finFold k).naturality_apply σ ⟨e, args⟩ |>.symm

@[simp] theorem Expr.subst_forallE (t : Expr ζ ℓ m) (t' : Expr ζ ℓ (m + 1)) :
    (t.forallE t').subst σ =
      (t.subst σ).forallE (t'.subst σ.lift) := rfl

@[simp] theorem Expr.subst_sort (l : Level ℓ) :
    (Expr.sort l : Expr ζ ℓ m).subst σ = .sort l := rfl

@[simp] theorem Expr.subst_quot (η : Head ζ .quot) (l : Level ℓ) (α r : Expr ζ ℓ m) :
    (Expr.quot η l α r).subst σ =
      .quot η l (α.subst σ) (r.subst σ) := rfl

@[simp] theorem Expr.inst_wk (e₁ e₂ : Expr ζ ℓ n) : e₁.wk.inst e₂ = e₁ := by
  change (e₁.wkFrom n).subst _ = e₁
  rw [Expr.wkFrom_subst]
  have hσ : ((fun v => (Subst.id.extend e₂) (Ren.wkFrom n v)) : Subst ζ ℓ n n) =
      Subst.id := by
    funext v
    simp
  rw [hσ, Expr.subst_id]

theorem Expr.inst_subst (σ : Subst ζ ℓ n p) (t' : Expr ζ ℓ (n + 1)) (e : Expr ζ ℓ n) :
    (t'.inst e).subst σ = (t'.subst σ.lift).inst (e.subst σ) := by
  change (t'.subst _).subst σ = (t'.subst _).subst _
  rw [Expr.subst_subst, Expr.subst_subst]
  congr 1
  funext v
  cases v using Fin.lastCases with
  | last => simp [Subst.comp, Expr.subst]
  | cast v =>
    simpa [Subst.comp, Subst.id, Expr.subst, Expr.inst] using
      (Expr.inst_wk (σ v) (e.subst σ)).symm

@[simp] theorem Expr.wkN_subst (σ : Subst ζ ℓ n p) (e : Expr ζ ℓ n) (k : Nat) :
    (e.wkN k).subst (σ.liftN k) = (e.subst σ).wkN k :=
  letI := Subst.category ζ ℓ
  ((Subst.wkNNatTrans k).naturality_apply σ e).symm

@[simp] theorem Ctx.ofTypes_substN {k : Nat} (types : Fin k → Expr ζ ℓ n)
    (σ : Subst ζ ℓ n p) :
    Ctx.substN σ k (Ctx.ofTypes types) = Ctx.ofTypes fun i => (types i).subst σ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Ctx.substN, ih]

@[simp] theorem Expr.wkN_subst_append (e : Expr ζ ℓ m) (σ : Subst ζ ℓ m n)
    (xs : Fin k → Expr ζ ℓ n) :
    (e.wkN k).subst (Fin.append σ xs) = e.subst σ := by
  rw [Expr.wkN_eq_rename, Expr.rename_subst]
  have hσ : Subst.precomp (Fin.append σ xs) (Ren.wkN k) = σ := by
    funext v
    simp [Subst.precomp, Ren.wkN]
  rw [hσ]

@[simp] theorem Expr.wkN_subst_id_append (e : Expr ζ ℓ n)
    (xs : Fin k → Expr ζ ℓ n) :
    (e.wkN k).subst (Fin.append Subst.id xs) = e := by
  rw [Expr.wkN_subst_append, Expr.subst_id]

theorem Expr.subst_closed (e : Expr ζ ℓ 0) (σ : Subst ζ ℓ 0 n) :
    e.subst σ = e.wkClosed (n := n) := by
  induction n with
  | zero => rw [show σ = Subst.id from Subsingleton.elim _ _]; exact Expr.subst_id e
  | succ n ih =>
    rw [show σ = fun v => ((![] : Subst ζ ℓ 0 n) v).wkFrom n from Subsingleton.elim _ _]
    exact (Expr.subst_wkFrom _ e).symm.trans (congrArg (Expr.wkFrom n) (ih _))

@[simp]
theorem Expr.wkClosed_subst (e : Expr ζ ℓ 0) (σ : Subst ζ ℓ m n) :
    e.wkClosed.subst σ = e.wkClosed := by
  induction m with
  | zero => exact Expr.subst_closed e σ
  | succ m ih =>
    change (e.wkClosed (n := m).wkFrom m).subst σ = _
    rw [Expr.wkFrom_subst]
    exact ih _

@[simp] theorem Subst.liftN_var (σ : Subst ζ ℓ n p) {k : Nat} (j : Fin k) :
    (σ.liftN k) (j.natAdd n) = .var (j.natAdd p) := by
  induction k with
  | zero => exact absurd j.isLt (by omega)
  | succ k ih =>
    cases j using Fin.lastCases with
    | last => simp
    | cast j =>
        change (σ.liftN k).lift (Fin.natAdd n j).castSucc = _
        rw [Subst.lift_castSucc, ih j]
        simp [Expr.wk]

@[simp] theorem Subst.liftN_castLE (v : Fin m) (k : Nat) :
    σ.liftN k (v.castLE (by omega)) = (σ v).wkN k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hv : v.castLE (show m ≤ m + (k + 1) by omega) =
          (v.castLE (show m ≤ m + k by omega)).castSucc := rfl
      rw [Subst.liftN, hv, Subst.lift_castSucc, ih, Expr.wkN]

@[simp] theorem Subst.liftN_castAdd (σ : Subst ζ ℓ n m) (v : Fin n) (k : Nat) :
    σ.liftN k (v.castAdd k) = (σ v).wkN k :=
  Subst.liftN_castLE σ v k

@[simp] theorem Expr.applyBound_subst (e : Expr ζ ℓ m) (k : Nat) :
    (e.applyBound k).subst (σ.liftN k) = (e.subst σ).applyBound k := by
  induction k with
  | zero => rfl
  | succ k ih => simp! [wk_subst_lift, ih, applyBound]

theorem Expr.boundVars_subst (count suffix : Nat) :
    (fun i => (Expr.boundVars m count suffix i).subst
      ((σ.liftN count).liftN suffix)) =
      (Expr.boundVars n count suffix : Fin count → Expr ζ ℓ (n + count + suffix)) := by
  funext i
  simp! [Expr.boundVars]

@[simp] theorem Subst.append_comp
    (ps : Fin a → Expr ζ ℓ m) (tail : Fin b → Expr ζ ℓ m)
    (σ : Subst ζ ℓ m n) :
    Subst.comp (Fin.append ps tail) σ =
      Fin.append (fun i => (ps i).subst σ)
        fun i => (tail i).subst σ :=
  Fin.append_comp ps tail (Expr.subst σ)

@[simp] theorem Subst.precomp_liftN_wkN (extra : Nat) :
    (σ.liftN extra).precomp (Ren.wkN extra) =
      σ.rename (Ren.wkN extra) := by
  funext v
  simp [Subst.precomp, Subst.rename, Ren.wkN, Expr.wkN_eq_rename]

@[simp] theorem Expr.wkN_subst_case (e : Expr ζ ℓ n)
    (csig : CtorSig nsorts)
    (fds : Fin csig.nfields → Expr ζ ℓ n)
    (recFds ihs : Fin csig.nrecFields → Expr ζ ℓ n) :
    (((e.wkN csig.nfields).wkN csig.nrecFields).wkN csig.nrecFields).subst
        (csig.caseSubst fds recFds ihs) = e := by
  rw [Expr.wkN_eq_rename, Expr.wkN_eq_rename, Expr.wkN_eq_rename,
    Expr.rename_rename, Expr.rename_rename,
    Expr.rename_subst]
  have hσ : Subst.precomp (csig.caseSubst fds recFds ihs)
      (Ren.comp
        (Ren.comp (Ren.wkN csig.nrecFields) (Ren.wkN csig.nrecFields))
        (Ren.wkN csig.nfields)) =
      (Subst.id : Subst ζ ℓ n n) := by
    funext v
    simp [Subst.precomp, CtorSig.caseSubst, Ren.comp, Ren.wkN]
  rw [hσ, Expr.subst_id]

theorem Expr.wk_subst_extend (σ : Subst ζ ℓ n m) (e₁ : Expr ζ ℓ n)
    (e₂ : Expr ζ ℓ m) :
    e₁.wk.subst (σ.extend e₂) = e₁.subst σ := by
  rw [show e₁.wk = e₁.wkFrom n from rfl, Expr.wkFrom_subst]
  congr 1
  funext v
  simp

def Subst.wk : Subst ζ ℓ n (n + 1) := fun v => .var v.castSucc

theorem Expr.subst_wk (e : Expr ζ ℓ n) : e.subst Subst.wk = e.wk := by
  rw [Expr.wk, Expr.wkFrom_eq_subst]
  congr 1
  funext v
  simp [Subst.wk, Subst.wkFrom]

theorem Expr.wk_subst (e : Expr ζ ℓ n) (σ : Subst ζ ℓ (n + 1) m) :
    e.wk.subst σ = e.subst (Subst.wk.comp σ) := by
  simp [← Expr.subst_wk]

@[simp] theorem Subst.wk_comp_apply (σ : Subst ζ ℓ (n + 1) m) (v : Var n) :
    Subst.wk.comp σ v = σ v.castSucc :=
  rfl

@[simp] theorem Subst.extend_wk_comp (σ : Subst ζ ℓ (n + 1) m) :
    (Subst.wk.comp σ).extend (σ (Fin.last n)) = σ :=
  Fin.snoc_init_self σ

theorem Ctx.entry_substN (k : Nat) (Γ : Ctx ζ ℓ m (m + k)) (j : Nat) (hb : n ≤ n + j)
    (hp : n + j < n + k) (hb' : m ≤ m + j) (hp' : m + j < m + k) :
    Ctx.entry (Ctx.substN σ k Γ) hb hp =
      (Ctx.entry Γ hb' hp').subst (σ.liftN j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    have .snoc Γ t := Γ
    by_cases hjk : j = k
    · subst j
      simp [Ctx.substN]
    · change (if _ : n + j = n + k then _
            else Ctx.entry (Ctx.substN σ k Γ) hb (by omega)) =
          (if _ : m + j = m + k then _
            else Ctx.entry Γ hb' (by lia)).subst (σ.liftN j)
      rw [dite_eq_right (show n + j ≠ n + k by omega),
        dite_eq_right (show m + j ≠ m + k by omega)]
      exact ih Γ (by omega) (by omega)

theorem Ctx.get_subst (Γ : Ctx ζ ℓ 0 n) (σ : Subst ζ ℓ n m) (v : Var n)
    (p : Nat) (hp : p < n) (hv : v.val = p) :
    (Γ.get v).subst σ =
      (Γ.entry (Nat.zero_le p) hp).subst
        fun w : Var p => σ (w.castLE (by omega)) := by
  induction Γ with
  | nil => omega
  | @snoc c Γ t ih =>
    change (if _ : v.val = c then t.wk
      else (Ctx.get (v.castLT (by omega)) Γ).wk).subst σ =
      (if h : p = c then h.symm ▸ t
        else Ctx.entry Γ (Nat.zero_le p) (by omega)).subst _
    by_cases h : p = c
    · subst h
      simp [hv, Expr.wk_subst]
      rfl
    · rw [dite_eq_right (show ¬v.val = c by omega), dite_eq_right h,
        Expr.wk_subst,
        ih (σ := Subst.wk.comp σ)
          (v := v.castLT (by omega)) (by omega) hv]
      rfl

@[simp] theorem Subst.lift_comp_extend (σ₁ : Subst ζ ℓ n m)
    (σ₂ : Subst ζ ℓ m p) (e : Expr ζ ℓ p) :
    σ₁.lift.comp (σ₂.extend e) = (σ₁.comp σ₂).extend e := by
  funext v
  cases v using Fin.lastCases with
  | last => simp [Subst.comp, Expr.subst]
  | cast v => simp [Subst.comp, Expr.wk_subst_extend]

theorem Ctx.get_eq_entry_rename (Γ : Ctx ζ ℓ 0 n) (v : Var n) (p : Nat) (hp : p < n)
    (hv : v.val = p) :
    Γ.get v = (Γ.entry (Nat.zero_le p) hp).rename fun slot : Var p => slot.castLE (by omega) := by
  have hsubst := Ctx.get_subst Γ Subst.id v p hp hv
  rw [Expr.subst_id] at hsubst
  exact hsubst.trans (Expr.subst_vars _ _)

theorem Expr.inst_subst_lift (σ : Subst ζ ℓ n p) (e' : Expr ζ ℓ (n + 1)) (e : Expr ζ ℓ p) :
    (e'.subst σ.lift).inst e = e'.subst (σ.extend e) := by
  simp [inst]

@[simp] theorem Subst.liftN_comp_append (σ₁ : Subst ζ ℓ n m)
    (σ₂ : Subst ζ ℓ m p) (xs : Fin k → Expr ζ ℓ p) :
    (σ₁.liftN k).comp (Fin.append σ₂ xs) =
      Fin.append (σ₁.comp σ₂) xs := by
  funext v
  cases v using Fin.addCases <;> simp [Subst.comp, Expr.subst]

@[simp] theorem Ctx.substN₂_append (Γ : Ctx ζ ℓ m (m + a))
    (Δ : Ctx ζ ℓ (m + a) (m + a + b)) :
    Ctx.substN₂ σ a b (Γ ++ Δ) =
      Ctx.substN σ a Γ ++ Ctx.substN (σ.liftN a) b Δ :=
  congrArg (fun ⟨Γ, Δ⟩ => Ctx.substN σ a Γ ++ Ctx.substN (σ.liftN a) b Δ)
    (Tele.split_append (Nat.le_add_right m a) Γ Δ)

@[simp] theorem Ctx.substN₃_append (Γ : Ctx ζ ℓ m (m + a + b))
    (Δ : Ctx ζ ℓ (m + a + b) (m + a + b + k)) :
    Ctx.substN₃ σ a b k (Γ ++ Δ) =
      Ctx.substN₂ σ a b Γ ++
        Ctx.substN ((σ.liftN a).liftN b) k Δ :=
  congrArg (fun ⟨Γ, Δ⟩ => Ctx.substN₂ σ a b Γ ++ Ctx.substN ((σ.liftN a).liftN b) k Δ)
    (Tele.split_append ((Nat.le_add_right m a).trans (Nat.le_add_right _ b)) Γ Δ)

@[simp] theorem Ctx.pi_subst {k : Nat} (Δ : Ctx ζ ℓ m (m + k)) (e : Expr ζ ℓ (m + k)) :
    (Ctx.pi e Δ).subst σ =
      Ctx.pi (e.subst (σ.liftN k)) (Ctx.substN σ k Δ) :=
  letI := Subst.category ζ ℓ
  ((Ctx.foldSubstHom Expr.forallSubstHom k).naturality_apply σ ⟨Δ, e⟩).symm

@[simp] theorem Ctx.pi_subst₂ (Δ : Ctx ζ ℓ m (m + a + b)) (e : Expr ζ ℓ (m + a + b)) :
    (Ctx.pi e Δ).subst σ =
      Ctx.pi (e.subst ((σ.liftN a).liftN b))
        (Ctx.substN₂ σ a b Δ) :=
  letI := Subst.category ζ ℓ
  ((Ctx.foldSubstHom₂ Expr.forallSubstHom a b).naturality_apply σ ⟨Δ, e⟩).symm

@[simp] theorem Ctx.pi_subst₃ (Δ : Ctx ζ ℓ m (m + a + b + k))
    (e : Expr ζ ℓ (m + a + b + k)) :
    (Ctx.pi e Δ).subst σ =
      Ctx.pi (e.subst (((σ.liftN a).liftN b).liftN k))
        (Ctx.substN₃ σ a b k Δ) :=
  letI := Subst.category ζ ℓ
  ((Ctx.foldSubstHom₃ Expr.forallSubstHom a b k).naturality_apply σ ⟨Δ, e⟩).symm

@[simp] theorem Ctx.lam_subst {k : Nat} (Δ : Ctx ζ ℓ m (m + k)) (e : Expr ζ ℓ (m + k)) :
    (Δ.lam e).subst σ =
      (Ctx.substN σ k Δ).lam (e.subst (σ.liftN k)) :=
  letI := Subst.category ζ ℓ
  ((Ctx.foldSubstHom Expr.lamSubstHom k).naturality_apply σ ⟨Δ, e⟩).symm

@[simp] theorem Ctx.lam_subst₂ (Δ : Ctx ζ ℓ m (m + a + b)) (e : Expr ζ ℓ (m + a + b)) :
    (Δ.lam e).subst σ =
      (Ctx.substN₂ σ a b Δ).lam (e.subst ((σ.liftN a).liftN b)) :=
  letI := Subst.category ζ ℓ
  ((Ctx.foldSubstHom₂ Expr.lamSubstHom a b).naturality_apply σ ⟨Δ, e⟩).symm

@[simp] theorem Ctx.lam_subst₃ (Δ : Ctx ζ ℓ m (m + a + b + k))
    (e : Expr ζ ℓ (m + a + b + k)) :
    (Δ.lam e).subst σ =
      (Ctx.substN₃ σ a b k Δ).lam
        (e.subst (((σ.liftN a).liftN b).liftN k)) :=
  letI := Subst.category ζ ℓ
  ((Ctx.foldSubstHom₃ Expr.lamSubstHom a b k).naturality_apply σ ⟨Δ, e⟩).symm

@[simp] theorem Inductive.paramType_subst (f : Fin ι.nparams) (σ : Subst ζ ℓ m n) :
    (I.paramType ls ps f).subst σ =
      I.paramType ls (fun i => (ps i).subst σ) f := by
  simp [paramType]

@[simp] theorem Inductive.indexType_subst (s : Fin ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ ℓ m) (is : Fin (ι.nindices s) → Expr ζ ℓ m)
    (f : Fin (ι.nindices s)) (σ : Subst ζ ℓ m n) :
    (I.indexType ls s ps is f).subst σ =
      I.indexType ls s (fun i => (ps i).subst σ)
        (fun i => (is i).subst σ) f := by
  simp [indexType]

@[simp] theorem Ctor.targetIndex_subst (fds : Fin csig.nfields → Expr ζ ℓ m)
    (index : Fin (ι.nindices s)) (σ : Subst ζ ℓ m n) :
    (ctor.targetIndex ls ps fds index).subst σ =
      ctor.targetIndex ls (fun i => (ps i).subst σ)
        (fun i => (fds i).subst σ) index := by
  simp [targetIndex]

@[simp] theorem RecField.instantiatedTelescope_subst
    (fd : RecField ζ ι a arity target)
    (ls : Fin ι.nlevels → Level ℓ) (fieldSubst : Subst ζ ℓ (ι.nparams + a) m)
    (σ : Subst ζ ℓ m n) :
    Ctx.substN σ arity (fd.instantiatedTelescope ls fieldSubst) =
      fd.instantiatedTelescope ls (fieldSubst.comp σ) :=
  letI := Subst.category ζ ℓ
  ((Ctx.substFunctor arity).map_comp_apply fieldSubst σ (fd.tele.instL ls)).symm

@[simp] theorem RecField.instantiatedIndices_subst
    (fd : RecField ζ ι a arity target)
    (ls : Fin ι.nlevels → Level ℓ) (fieldSubst : Subst ζ ℓ (ι.nparams + a) m)
    (σ : Subst ζ ℓ m n) (i : Fin (ι.nindices target)) :
    (fd.instantiatedIndices ls fieldSubst i).subst (σ.liftN arity) =
      fd.instantiatedIndices ls (fieldSubst.comp σ) i := by
  simp [instantiatedIndices]

@[simp] theorem RecField.instantiatedType_subst
    (fd : RecField ζ ι a arity target)
    (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ m)
    (fieldSubst : Subst ζ ℓ (ι.nparams + a) m)
    (σ : Subst ζ ℓ m n) :
    (fd.instantiatedType η ls ps fieldSubst).subst σ =
      fd.instantiatedType η ls (fun i => (ps i).subst σ)
        (fieldSubst.comp σ) := by
  simp! [instantiatedType]

@[simp] theorem Ctor.ordinaryFieldExpr_subst (fds : Fin csig.nfields → Expr ζ ℓ m)
    (field : Fin csig.nfields) (σ : Subst ζ ℓ m n) :
    (ctor.ordinaryFieldExpr ls ps fds field).subst σ =
      ctor.ordinaryFieldExpr ls (fun i => (ps i).subst σ)
        (fun i => (fds i).subst σ) field := by
  simp [ordinaryFieldExpr]

@[simp] theorem Ctor.recursiveFieldExpr_subst (fds : Fin csig.nfields → Expr ζ ℓ m)
    (field : Fin csig.nrecFields) (σ : Subst ζ ℓ m n) :
    (ctor.recursiveFieldExpr η ls ps fds field).subst σ =
      ctor.recursiveFieldExpr η ls (fun i => (ps i).subst σ)
        (fun i => (fds i).subst σ) field := by
  simp [recursiveFieldExpr]

theorem Subst.liftN_eq_append {a : Nat} (σ : Subst ζ ℓ a m) (count : Nat) :
    σ.liftN count =
      Fin.append (fun p => (σ p).wkN count) (Expr.boundVars m count 0) := by
  funext v
  cases v using Fin.addCases with
  | left p => simp
  | right f => rw [Subst.liftN_var, Fin.append_right]; rfl

@[simp] theorem Ctor.ordinaryFieldTeleAux_subst (count : Nat)
    (hcount : count ≤ csig.nfields) (σ : Subst ζ ℓ m n) :
    (ctor.ordinaryFieldTeleAux η ls ps count hcount).substN σ count =
      ctor.ordinaryFieldTeleAux η ls (fun i => (ps i).subst σ)
        count hcount :=
  letI := Subst.category ζ ℓ
  ((Ctx.substFunctor count).map_comp_apply (X := ι.nparams) ps σ _).symm

@[simp] theorem Ctor.recursiveFieldTeleAux_subst
    (fds : Fin csig.nfields → Expr ζ ℓ m) (count : Nat)
    (hcount : count ≤ csig.nrecFields) (σ : Subst ζ ℓ m n) :
    (ctor.recursiveFieldTeleAux η ls ps fds count hcount).substN σ count =
      ctor.recursiveFieldTeleAux η ls (fun i => (ps i).subst σ)
        (fun i => (fds i).subst σ) count hcount := by
  simp [recursiveFieldTeleAux]

@[simp] theorem Ctor.fieldTele_subst
    (stop : Fin (csig.nrecFields + 1) := ⟨csig.nrecFields, Nat.lt_succ_self _⟩) :
    Ctx.substN₂ σ csig.nfields stop.val
        (ctor.fieldTele η ls ps stop) =
      ctor.fieldTele η ls (fun i => (ps i).subst σ) stop := by
  unfold Ctor.fieldTele Ctor.ordinaryFieldTele
  rw [Ctx.substN₂_append, Ctor.recursiveFieldTeleAux_subst]
  erw [Expr.boundVars_subst σ csig.nfields 0]
  simp

@[simp] theorem Inductive.motiveResult_subst
    (motive : Expr ζ ℓ m) (is : Fin k → Expr ζ ℓ m)
    (maj : Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (motiveResult motive is maj).subst σ =
      motiveResult (motive.subst σ)
        (fun i => (is i).subst σ) (maj.subst σ) := by
  simp [motiveResult]

@[simp] theorem RecField.ihType_subst
    (recFd : RecField ζ ι a arity target)
    (ls : Fin ι.nlevels → Level ℓ)
    (ms : Fin ι.nsorts → Expr ζ ℓ m)
    (fieldSubst : Subst ζ ℓ (ι.nparams + a) m)
    (r : Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (recFd.ihType ls ms fieldSubst r).subst σ =
      recFd.ihType ls
        (fun s => (ms s).subst σ)
        (fieldSubst.comp σ) (r.subst σ) := by
  simp [ihType]

@[simp] theorem RecField.iotaIH_subst
    (recFd : RecField ζ ι a arity target)
    (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Level ℓ) (l : Level ℓ)
    (ps : Fin ι.nparams → Expr ζ ℓ m)
    (ms : Fin ι.nsorts → Expr ζ ℓ m)
    (mins : (s : Fin ι.nsorts) →
      Fin (ι.nctors s) → Expr ζ ℓ m)
    (fieldSubst : Subst ζ ℓ (ι.nparams + a) m)
    (r : Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (recFd.iotaIH η ls l ps ms mins fieldSubst r).subst σ =
      recFd.iotaIH η ls l (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ)
        (fun s ctor => (mins s ctor).subst σ)
        (fieldSubst.comp σ) (r.subst σ) := by
  simp! [iotaIH]

@[simp] theorem CtorSig.fieldParams_subst {ι : IndSig}
    (csig : CtorSig ι.nsorts) (ps : Fin ι.nparams → Expr ζ ℓ m)
    (σ : Subst ζ ℓ m n) (i : Fin ι.nparams) :
    (csig.fieldParams ps i).subst (csig.liftFieldSubst σ) =
      csig.fieldParams (fun i => (ps i).subst σ) i := by
  simp! [fieldParams, liftFieldSubst]

@[simp] theorem CtorSig.fieldOrdinary_subst (csig : CtorSig nsorts)
    (σ : Subst ζ ℓ m n) (i : Fin csig.nfields) :
    (csig.fieldOrdinary (ζ₁ := ζ) (ℓ := ℓ) (n := m) i).subst
        (csig.liftFieldSubst σ) =
      csig.fieldOrdinary (n := n) i := by
  simp! [fieldOrdinary, liftFieldSubst]

@[simp] theorem CtorSig.fieldRecursive_subst (csig : CtorSig nsorts)
    (σ : Subst ζ ℓ m n) (i : Fin csig.nrecFields) :
    (csig.fieldRecursive (ζ₁ := ζ) (ℓ := ℓ) (n := m) i).subst
        (csig.liftFieldSubst σ) =
      csig.fieldRecursive (n := n) i := by
  simp! [fieldRecursive, liftFieldSubst]

@[simp] theorem CtorSig.caseParams_subst {ι : IndSig}
    (csig : CtorSig ι.nsorts) (ps : Fin ι.nparams → Expr ζ ℓ m)
    (σ : Subst ζ ℓ m n) (i : Fin ι.nparams) :
    (csig.caseParams ps i).subst (csig.liftCaseSubst σ) =
      csig.caseParams (fun i => (ps i).subst σ) i :=
  letI := Subst.category ζ ℓ
  ((Subst.wkNNatTrans _).naturality_apply (csig.liftFieldSubst σ) _).symm.trans
    (congrArg (Expr.wkN · _) (csig.fieldParams_subst ps σ i))

@[simp] theorem CtorSig.caseOrdinary_subst (csig : CtorSig nsorts)
    (σ : Subst ζ ℓ m n) (i : Fin csig.nfields) :
    (csig.caseOrdinary (ζ₁ := ζ) (ℓ := ℓ) (n := m) i).subst
        (csig.liftCaseSubst σ) =
      csig.caseOrdinary (n := n) i :=
  letI := Subst.category ζ ℓ
  ((Subst.wkNNatTrans _).naturality_apply (csig.liftFieldSubst σ) _).symm.trans
    (congrArg (Expr.wkN · _) (csig.fieldOrdinary_subst σ i))

@[simp] theorem CtorSig.caseRecursive_subst (csig : CtorSig nsorts)
    (σ : Subst ζ ℓ m n) (i : Fin csig.nrecFields) :
    (csig.caseRecursive (ζ₁ := ζ) (ℓ := ℓ) (n := m) i).subst
        (csig.liftCaseSubst σ) =
      csig.caseRecursive (n := n) i :=
  letI := Subst.category ζ ℓ
  ((Subst.wkNNatTrans _).naturality_apply (csig.liftFieldSubst σ) _).symm.trans
    (congrArg (Expr.wkN · _) (csig.fieldRecursive_subst σ i))

@[simp] theorem CtorSig.caseParams_subst_case {ι : IndSig}
    (csig : CtorSig ι.nsorts) (ps : Fin ι.nparams → Expr ζ ℓ n)
    (fds : Fin csig.nfields → Expr ζ ℓ n)
    (recFds ihs : Fin csig.nrecFields → Expr ζ ℓ n)
    (i : Fin ι.nparams) :
    (csig.caseParams ps i).subst (csig.caseSubst fds recFds ihs) =
      ps i :=
  Expr.wkN_subst_case (ps i) csig fds recFds ihs

@[simp] theorem CtorSig.caseOrdinary_subst_case (csig : CtorSig nsorts)
    (fds : Fin csig.nfields → Expr ζ ℓ n)
    (recFds ihs : Fin csig.nrecFields → Expr ζ ℓ n)
    (i : Fin csig.nfields) :
    (csig.caseOrdinary i).subst (csig.caseSubst fds recFds ihs) =
      fds i := by
  simp! [caseOrdinary, fieldOrdinary, caseSubst]

@[simp] theorem CtorSig.caseRecursive_subst_case (csig : CtorSig nsorts)
    (fds : Fin csig.nfields → Expr ζ ℓ n)
    (recFds ihs : Fin csig.nrecFields → Expr ζ ℓ n)
    (i : Fin csig.nrecFields) :
    (csig.caseRecursive i).subst (csig.caseSubst fds recFds ihs) =
      recFds i := by
  simp! [caseRecursive, fieldRecursive, caseSubst]

@[simp] theorem Ctor.ihTypeWith_subst (ps : Fin ι.nparams → Expr ζ ℓ m)
    (fds : Fin csig.nfields → Expr ζ ℓ m) (recFds : Fin csig.nrecFields → Expr ζ ℓ m)
    (f : Fin csig.nrecFields) (σ : Subst ζ ℓ m n) :
    (ctor.ihTypeWith ls ms ps fds recFds f).subst σ =
      ctor.ihTypeWith ls
        (fun s => (ms s).subst σ)
        (fun i => (ps i).subst σ) (fun i => (fds i).subst σ)
        (fun i => (recFds i).subst σ) f := by
  simp [Ctor.ihTypeWith]

@[simp] theorem Ctor.ihType_subst (f : Fin csig.nrecFields) (σ : Subst ζ ℓ m n) :
    (ctor.ihType ls ps ms f).subst (csig.liftFieldSubst σ) =
      ctor.ihType ls (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ) f := by
  unfold Ctor.ihType Ctor.ihTypeWith
  rw [RecField.ihType_subst]
  congr 1
  · funext s
    simp [CtorSig.liftFieldSubst]
  · rw [Subst.append_comp]
    congr 1
    · funext param
      exact csig.fieldParams_subst ps σ param
    · funext fds
      exact csig.fieldOrdinary_subst σ fds
  · exact csig.fieldRecursive_subst σ f

@[simp] theorem Ctor.iotaIH_subst (fds : Fin csig.nfields → Expr ζ ℓ m)
    (recFds : Fin csig.nrecFields → Expr ζ ℓ m) (f : Fin csig.nrecFields)
    (σ : Subst ζ ℓ m n) :
    (ctor.iotaIH η ls l ps ms mins fds recFds f).subst σ =
      ctor.iotaIH η ls l (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ)
        (fun s c => (mins s c).subst σ)
        (fun i => (fds i).subst σ)
        (fun i => (recFds i).subst σ) f := by
  unfold Ctor.iotaIH
  simp

@[simp] theorem Inductive.iotaIHs_subst (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ m)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ m)
    (f : Fin (ι.ctors s c).nrecFields) (σ : Subst ζ ℓ m n) :
    (I.iotaIHs η ls l ps ms mins s c fds recFds f).subst σ =
      I.iotaIHs η ls l (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ)
        (fun s c => (mins s c).subst σ) s c
        (fun i => (fds i).subst σ)
        (fun i => (recFds i).subst σ) f :=
  Ctor.iotaIH_subst _ η ls l ps ms mins fds recFds f σ

@[simp] theorem Inductive.iotaRhs_subst (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ m)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (I.iotaRhs η ls l ps ms mins s c fds recFds).subst σ =
      I.iotaRhs η ls l (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ)
        (fun s c => (mins s c).subst σ) s c
        (fun i => (fds i).subst σ)
        fun i => (recFds i).subst σ := by
  unfold Inductive.iotaRhs
  simp

@[simp] theorem Ctor.ihTeleAux_subst (count : Nat)
    (hcount : count ≤ csig.nrecFields) (σ : Subst ζ ℓ m n) :
    Ctx.substN (csig.liftFieldSubst σ) count
        (ctor.ihTeleAux ls ps ms count hcount) =
      ctor.ihTeleAux ls (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ) count hcount := by
  simp [Ctor.ihTeleAux]

@[simp] theorem Ctor.ihTele_subst :
    Ctx.substN (csig.liftFieldSubst σ) csig.nrecFields
        (ctor.ihTele ls ps ms) =
      ctor.ihTele ls (fun i => (ps i).subst σ)
        fun s => (ms s).subst σ :=
  ctor.ihTeleAux_subst ls ps ms _ _ σ

@[simp] theorem Inductive.caseTele_subst (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (σ : Subst ζ ℓ m n) :
    Ctx.substN₃ σ (ι.ctors s c).nfields
        (ι.ctors s c).nrecFields
        (ι.ctors s c).nrecFields
        (I.caseTele η ls ps ms s c) =
      I.caseTele η ls (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ) s c := by
  unfold Inductive.caseTele
  rw [Ctx.substN₃_append, Ctor.fieldTele_subst]
  change
    (I.ctors s c).fieldTele η ls (fun i => (ps i).subst σ) ++
      Ctx.substN ((ι.ctors s c).liftFieldSubst σ)
        (ι.ctors s c).nrecFields ((I.ctors s c).ihTele ls ps ms) = _
  rw [Ctor.ihTele_subst]

@[simp] theorem Inductive.indexTele_subst (s : Fin ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    Ctx.substN σ (ι.nindices s) (I.indexTele ls s ps) =
      I.indexTele ls s fun i => (ps i).subst σ :=
  letI := Subst.category ζ ℓ
  ((Ctx.substFunctor (ι.nindices s)).map_comp_apply (X := ι.nparams) ps σ _).symm

@[simp] theorem Inductive.indexTele_entry_subst (s : Fin ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ ℓ m) (σ : Subst ζ ℓ m n)
    (is : Fin (ι.nindices s) → Expr ζ ℓ n) (index : Fin (ι.nindices s)) :
    ((I.indexTele ls s ps).entry (by omega) (by omega)).subst
        (Fin.append σ fun previous =>
          is (previous.castLE index.isLt.le)) =
      I.indexType ls s (fun p => (ps p).subst σ) is index := by
  unfold Inductive.indexTele Inductive.indexType
  rw [Ctx.entry_substN _ _ _ index.val (by omega) (by omega) (by omega) (by omega),
    Expr.subst_subst, Subst.liftN_comp_append]
  congr 1
  rw [← Ctx.entry_instL]
  exact congrArg (Expr.instL ls)
    (Eq.symm (Ctx.proj_eq_entry index (I.indices s)))

@[simp] theorem Inductive.indexTele_get (s : Fin ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ ℓ n) (Γ : Ctx ζ ℓ 0 n) (index : Fin (ι.nindices s)) :
    Ctx.get ⟨n + index.val, by omega⟩
        (Γ ++ I.indexTele ls s ps) =
      I.indexType ls s
        (fun p => (ps p).wkN (ι.nindices s))
        (fun i => .var ⟨n + i.val, by omega⟩) index := by
  rw [← Expr.subst_id (Ctx.get ⟨n + index.val, by omega⟩ (Γ ++ I.indexTele ls s ps)),
    Ctx.get_subst _ Subst.id _ (n + index.val) (by omega) rfl,
    Ctx.entry_append_right Γ (I.indexTele ls s ps) (Nat.zero_le _) (by omega) (by omega)]
  have hσ :
      (fun w : Fin (n + index.val) =>
        (.var (w.castLE (by omega)) :
          Expr ζ ℓ (n + ι.nindices s))) =
      Fin.append (fun v : Fin n => (.var (v.castAdd (ι.nindices s)) :
          Expr ζ ℓ (n + ι.nindices s))) fun i => .var ⟨n + i.val, by omega⟩ := by
    funext v
    by_cases hv : v.val < n
    · have heq : v = (⟨v.val, hv⟩ : Fin n).castAdd index.val := rfl
      rw [heq, Fin.append_left]
      rfl
    · have hi : v.val - n < index.val := by omega
      have heq : v = Fin.natAdd n ⟨v.val - n, hi⟩ := Fin.ext (by simp; omega)
      rw [heq, Fin.append_right]
      rfl
  change Expr.subst (fun w => (.var (w.castLE (by omega)) :
      Expr ζ ℓ (n + ι.nindices s))) _ = _
  rw [hσ]
  erw [I.indexTele_entry_subst ls s ps
    (fun v => .var (v.castAdd (ι.nindices s)))
    (fun i => .var ⟨n + i.val, by omega⟩) index]
  congr 2
  funext p
  rw [Expr.wkN_eq_rename]
  exact Expr.subst_vars (Ren.wkN (ι.nindices s)) (ps p)

@[simp] theorem Inductive.params_get (param : Fin ι.nparams) :
    Ctx.get param (Ctx.instL ls I.params) =
      I.paramType ls Expr.var param := by
  rw [← Expr.subst_id (Ctx.get param (Ctx.instL ls I.params)),
    Ctx.get_subst _ Subst.id param param.val param.isLt rfl,
    ← Ctx.entry_instL]
  rfl

@[simp] theorem Inductive.motiveTele_subst (s : Fin ι.nsorts) (σ : Subst ζ ℓ m n) :
    Ctx.substN σ (ι.nindices s + 1)
        (I.motiveTele η ls ps s) =
      I.motiveTele η ls (fun i => (ps i).subst σ) s := by
  change (Ctx.substN σ (ι.nindices s) (I.indexTele ls s ps)).snoc
      ((Expr.ind η s ls
        (fun i => (ps i).wkN (ι.nindices s))
        (fun index => .var ⟨m + index.val, by omega⟩)).subst
          (σ.liftN (ι.nindices s))) = _
  rw [indexTele_subst]
  exact congr(Tele.snoc (I.indexTele ls s fun i => (ps i).subst σ)
    (Expr.ind η s ls $(funext fun i => Expr.wkN_subst σ (ps i) _) $(funext (Subst.liftN_var σ))))

@[simp] theorem Inductive.motiveType_subst (l : Level ℓ) (s : Fin ι.nsorts)
    (σ : Subst ζ ℓ m n) :
    (I.motiveType η ls ps l s).subst σ =
      I.motiveType η ls (fun i => (ps i).subst σ) l s := by
  unfold Inductive.motiveType
  rw [Ctx.pi_subst₂]
  change Ctx.pi (.sort l)
      ((Ctx.substN σ (ι.nindices s)
        (I.indexTele ls s ps)).snoc _) = _
  rw [indexTele_subst]
  congr 1
  refine congr(Tele.snoc (I.indexTele ls s fun i => (ps i).subst σ)
    (Expr.ind η s ls
      $(funext fun param => Expr.wkN_subst σ (ps param) _)
      $(funext (Subst.liftN_var σ))))

@[simp] theorem Inductive.caseType_subst (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (σ : Subst ζ ℓ m n) :
    (I.caseType η ls ps ms s c).subst
        ((ι.ctors s c).liftCaseSubst σ) =
      I.caseType η ls (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ)
        s c := by
  unfold Inductive.caseType
  rw [Inductive.motiveResult_subst]
  congr 1
  · simp [CtorSig.liftCaseSubst]
  · funext index
    rw [Ctor.targetIndex_subst]
    congr 1
    · funext param
      exact (ι.ctors s c).caseParams_subst ps σ param
    · funext fds
      exact (ι.ctors s c).caseOrdinary_subst σ fds
  · simp [Expr.subst]

@[simp] theorem Inductive.caseFnType_subst (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (σ : Subst ζ ℓ m n) :
    (I.caseFnType η ls ps ms s c).subst σ =
      I.caseFnType η ls (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ) s c := by
  unfold Inductive.caseFnType
  rw [Ctx.pi_subst₃, Inductive.caseTele_subst]
  change Ctx.pi
      ((I.caseType η ls ps ms s c).subst
        ((ι.ctors s c).liftCaseSubst σ)) _ = _
  rw [Inductive.caseType_subst]

theorem Inductive.paramType_eq_get_subst (ps : Fin ι.nparams → Expr ζ ℓ n)
    (f : Fin ι.nparams) :
    ((I.params.get f).instL ls).subst ps = I.paramType ls ps f := by
  rw [Ctx.get_instL, Ctx.get_subst _ ps f f.val f.isLt rfl, ← Ctx.entry_instL]
  rfl

theorem Inductive.indexType_eq_get_subst (s : Fin ι.nsorts)
    (ps : Fin ι.nparams → Expr ζ ℓ n) (is : Fin (ι.nindices s) → Expr ζ ℓ n)
    (f : Fin (ι.nindices s)) :
    ((Ctx.get (Fin.natAdd ι.nparams f)
          (I.params ++ I.indices s)).instL ls).subst
        (Fin.append ps is) =
      I.indexType ls s ps is f := by
  have hsub : (fun w : Var (Fin.natAdd ι.nparams f).val =>
      Fin.append ps is (w.castLE (by omega))) =
      Fin.append ps fun previous : Fin f.val =>
        is (previous.castLE f.isLt.le) := by
    funext w
    exact Fin.append_castLE_right ps is f.isLt.le w
  rw [Ctx.get_instL,
    Ctx.get_subst _ _ (Fin.natAdd ι.nparams f) _ (by omega) rfl,
    ← Ctx.entry_instL,
    Ctx.entry_append_right I.params (I.indices s) (by omega) (by simp)
      (by omega),
    hsub, indexType, Ctx.proj_eq_entry]

@[simp] theorem Inductive.iotaLhs_subst (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ m)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (I.iotaLhs η ls l ps ms mins s c fds recFds).subst σ =
      I.iotaLhs η ls l (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ)
        (fun s c => (mins s c).subst σ) s c
        (fun i => (fds i).subst σ)
        fun i => (recFds i).subst σ := by
  simp! [iotaLhs]

@[simp] theorem Inductive.iotaType_subst (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ m)
    (recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (I.iotaType η ls ps ms s c fds recFds).subst σ =
      I.iotaType η ls (fun i => (ps i).subst σ)
        (fun s => (ms s).subst σ)
        s c (fun i => (fds i).subst σ)
        fun i => (recFds i).subst σ := by
  simp [iotaType, Expr.subst]

@[simp] theorem Quot.compatType_subst
    (eqHead : Head ζ (.inductive Eq.sig)) (l : Level ℓ)
    (α r β f : Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (compatType eqHead l α r β f).subst σ =
      compatType eqHead l (α.subst σ) (r.subst σ)
        (β.subst σ) (f.subst σ) := by
  simp! [compatType, eqApp, Expr.wk_subst_lift, Subst.lift, Fin.last]
  constructor
  · simp [Expr.wk]
  · constructor
    · funext i
      split
      · simp [Expr.wk_subst_lift]
      · simp [Expr.wk_subst_lift]
        change (σ.liftN 3) ⟨m, by omega⟩ = _
        exact Subst.liftN_var σ ⟨0, by omega⟩
    · simp [Expr.wk]

@[simp] theorem Quot.minorQuotMk_subst (η : Head ζ .quot) (l : Level ℓ)
    (α r : Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (minorQuotMk η l α r).subst σ.lift =
      minorQuotMk η l (α.subst σ) (r.subst σ) := by
  simp! [minorQuotMk, Expr.wk_subst_lift]

@[simp] theorem Quot.minorQuotMk_inst (η : Head ζ .quot) (l : Level ℓ) (α r a : Expr ζ ℓ m) :
    (minorQuotMk η l α r).inst a = .quotMk η l α r a := by
  simp [minorQuotMk, Expr.inst, Expr.subst, Expr.wk_subst_extend]

@[simp] theorem Quot.minorType_subst (η : Head ζ .quot) (l : Level ℓ)
    (α r β : Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (minorType η l α r β).subst σ =
      minorType η l (α.subst σ) (r.subst σ) (β.subst σ) := by
  simp [minorType, Expr.wk_subst_lift]

@[simp] theorem Quot.relType_subst (α : Expr ζ ℓ m)
    (σ : Subst ζ ℓ m n) :
    (relType α).subst σ = relType (α.subst σ) := by
  simp [relType, Expr.wk_subst_lift]

@[simp] theorem Quot.motiveType_subst (η : Head ζ .quot) (l : Level ℓ)
    (α r : Expr ζ ℓ m) (σ : Subst ζ ℓ m n) :
    (motiveType η l α r).subst σ =
      motiveType η l (α.subst σ) (r.subst σ) := by
  simp [motiveType]

theorem Expr.inst_wkFrom_last (t' : Expr ζ ℓ (n + 1)) :
    (t'.wkFrom n).inst (.var (Fin.last n)) = t' := by
  change (t'.wkFrom n).subst _ = t'
  rw [Expr.wkFrom_subst]
  have : (fun v : Var (n + 1) => (Subst.id.extend (Expr.var (Fin.last n))) (Ren.wkFrom n v))
      = (Subst.id : Subst ζ ℓ (n + 1) (n + 1)) := by
    funext v
    cases v using Fin.lastCases with
    | last => simp [Subst.id]
    | cast v =>
        simp

  rw [this, Expr.subst_id]

theorem Subst.wkFrom_eq_lift_wk :
    (Subst.wkFrom n : Subst ζ ℓ (n + 1) (n + 2)) = Subst.wk.lift := by
  funext v
  cases v using Fin.lastCases with
  | last => simp [Subst.wkFrom]
  | cast v => simp [Subst.wkFrom, Subst.wk, Expr.var_wk]

def Subst.Renames (Γ₁ : Ctx ζ ℓ 0 n) (Γ₂ : Ctx ζ ℓ 0 m) (σ : Subst ζ ℓ n m) : Prop :=
  ∀ v, ∃ w, σ v = .var w ∧ Γ₂.get w = (Γ₁.get v).subst σ

theorem Subst.Renames.lift {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m} {σ : Subst ζ ℓ n m}
    {t : Expr ζ ℓ n} (h : Subst.Renames Γ₁ Γ₂ σ) :
    Subst.Renames (Γ₁.snoc t) (Γ₂.snoc (t.subst σ)) σ.lift := fun v => by
  cases v using Fin.lastCases with
  | last =>
    exact ⟨Fin.last m, Subst.lift_last σ, by rw [Ctx.get_last, Ctx.get_last, Expr.wk_subst_lift]⟩
  | cast v =>
    have ⟨w, hw, htype⟩ := h v
    refine ⟨w.castSucc, ?_, ?_⟩
    · rw [Subst.lift_castSucc, hw]
      simp [Expr.wk]
    · rw [Γ₂.get_snoc (t.subst σ) w.castSucc (Nat.ne_of_lt w.isLt),
        Γ₁.get_snoc t v.castSucc (Nat.ne_of_lt v.isLt), Expr.wk_subst_lift]
      exact congrArg Expr.wk htype

theorem Subst.renames_wkFrom {cut : Nat} (Γ₀ : Ctx ζ ℓ 0 cut) (t : Expr ζ ℓ cut)
    (Δ : Ctx ζ ℓ cut n) :
    Subst.Renames (Γ₀ ++ Δ) (Γ₀.insert t Δ) (Subst.wkFrom cut) := fun v =>
  ⟨Ren.wkFrom cut v, rfl, (Ctx.get_insert Γ₀ t Δ v).trans (Expr.wkFrom_eq_subst cut _)⟩

end Metalean
