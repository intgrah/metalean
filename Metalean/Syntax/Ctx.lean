/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Expr.Application
public import Metalean.Tele
import Metalean.Meta.DeriveFunctor

@[expose] public section

namespace Metalean

open CategoryTheory MonoidalCategory

variable {ζ ζ₁ ζ₂ : Sigs} {ℓ ℓ' n m p a b d k : Nat}

abbrev Ctx (ζ : Sigs) (ℓ : Nat) := Tele (Expr ζ ℓ)

namespace Ctx

attribute [local instance] Level.category

def get {n : Nat} (v : Var n) : Ctx ζ ℓ 0 n → Expr ζ ℓ n
  | .nil => nomatch v
  | .snoc (b := m) Γ t =>
    if h : v.val = m then t.wk else (Ctx.get (v.castLT (by omega)) Γ).wk

def substN (σ : Subst ζ ℓ m n) : (k : Nat) →
    Ctx ζ ℓ m (m + k) → Ctx ζ ℓ n (n + k)
  | 0, _ => .nil
  | k + 1, .snoc Γ t => .snoc (Ctx.substN σ k Γ) (t.subst (σ.liftN k))

@[simp] theorem substN_zero (σ : Subst ζ ℓ m n) (Δ : Ctx ζ ℓ m (m + 0)) :
    Δ.substN σ 0 = .nil :=
  rfl

@[reducible] def substFunctor (k : Nat) : @Functor Nat (Subst.category ζ ℓ) Type _ :=
  letI := Subst.category ζ ℓ
  { obj n := Ctx ζ ℓ n (n + k)
    map σ := ↾substN σ k
    map_id := by
      intro n
      ext Δ
      induction Δ using Tele.addInduction with
      | nil => rfl
      | snoc k Δ t ih =>
        exact congrArg₂ Tele.snoc ih ((Subst.shift k ⋙ Subst.functor ζ ℓ).map_id_apply _ t)
    map_comp := by
      intro m n p σ₁ σ₂
      ext Δ
      induction Δ using Tele.addInduction with
      | nil => rfl
      | snoc k Δ t ih =>
        exact congrArg₂ Tele.snoc ih ((Subst.shift k ⋙ Subst.functor ζ ℓ).map_comp_apply σ₁ σ₂ t) }

@[reducible] def substFunctor₂ (a b : Nat) : @Functor Nat (Subst.category ζ ℓ) Type _ :=
  letI := Subst.category ζ ℓ
  { __ := (substFunctor a ⊗ (Subst.shift a ⋙ substFunctor b)).copyObj
      (fun n => Ctx ζ ℓ n (n + a + b))
      (fun n => Tele.appendIso (Nat.le_add_right n a) b)
    obj n := Ctx ζ ℓ n (n + a + b) }

def substN₂ (σ : Subst ζ ℓ m n) (a b : Nat) :
    Ctx ζ ℓ m (m + a + b) → Ctx ζ ℓ n (n + a + b) :=
  letI := Subst.category ζ ℓ
  (substFunctor₂ a b).map σ

@[reducible] def substFunctor₃ (a b k : Nat) : @Functor Nat (Subst.category ζ ℓ) Type _ :=
  letI := Subst.category ζ ℓ
  { __ := (substFunctor₂ a b ⊗ (Subst.shift a ⋙ Subst.shift b ⋙ substFunctor k)).copyObj
      (fun n => Ctx ζ ℓ n (n + a + b + k))
      (fun n => Tele.appendIso ((Nat.le_add_right n a).trans (Nat.le_add_right _ b)) k)
    obj n := Ctx ζ ℓ n (n + a + b + k) }

def substN₃ (σ : Subst ζ ℓ m n) (a b k : Nat) :
    Ctx ζ ℓ m (m + a + b + k) → Ctx ζ ℓ n (n + a + b + k) :=
  letI := Subst.category ζ ℓ
  (substFunctor₃ a b k).map σ

abbrev nil : Ctx ζ ℓ a a := #t[]

abbrev snoc : Ctx ζ ℓ a b → Expr ζ ℓ b → Ctx ζ ℓ a (b + 1) :=
  Tele.snoc

@[reducible] def map (pre : ζ₁ ⟶ ζ₂) (Γ : Ctx ζ₁ ℓ a b) : Ctx ζ₂ ℓ a b :=
  Tele.map (fun _ e => e.map pre) Γ

@[reducible, functor] def functor (ℓ a b : Nat) : Sigs ⥤ Type where
  __ := Functor.pi' (Expr.functor ℓ) ⋙ Tele.functor a b
  obj ζ := Ctx ζ ℓ a b
  map pre := ↾map pre

@[simp] theorem map_append (pre : ζ₁ ⟶ ζ₂)
    (Γ : Ctx ζ₁ ℓ a b) (Δ : Ctx ζ₁ ℓ b n) :
    Ctx.map pre (Γ ++ Δ) = Γ.map pre ++ Δ.map pre :=
  @Functor.map_comp _ (Tele.category _) _ (Tele.category _) (Tele.mapFunctor fun _ => ↾Expr.map pre) _ _ _ Γ Δ

@[simp] theorem get_map (pre : ζ₁ ⟶ ζ₂) (v : Var n)
    (Γ : Ctx ζ₁ ℓ 0 n) :
    (Γ.map pre).get v = (Γ.get v).map pre := by
  induction Γ with
  | nil => exact Fin.elim0 v
  | snoc Γ t ih =>
      simp!
      split
      · simp
      · exact (congrArg Expr.wk (ih _)).trans (Expr.map_wk pre _).symm

def weakenEnv {sig : Sig} (Γ : Ctx ζ ℓ a b) : Ctx (.snoc ζ sig) ℓ a b :=
  Γ.map (.step .refl)

@[simp] theorem map_step {sig : Sig} (pre : ζ₁ ⟶ ζ₂)
    (Γ : Ctx ζ₁ ℓ a b) :
    (Γ.map pre).weakenEnv (sig := sig) = Γ.map (.step pre) :=
  ((functor ℓ a b).map_comp_apply pre (.step (𝟙 ζ₂)) Γ).symm

@[reducible] def levelFunctor (ζ : Sigs) (a b : Nat) : @Functor Nat Level.category Type _ :=
  Functor.pi' (fun n => (Expr.family n).obj ζ) ⋙ Tele.functor a b

def instL (ls : Param ℓ → Level ℓ') : Ctx ζ ℓ a b → Ctx ζ ℓ' a b :=
  Tele.map fun _ => Expr.instL ls

@[simp] theorem map_instL (pre : ζ₁ ⟶ ζ₂)
    (ls : Param ℓ → Level ℓ') (Γ : Ctx ζ₁ ℓ a b) :
    (Γ.instL ls).map pre = (Γ.map pre).instL ls := by
  induction Γ with
  | nil => rfl
  | snoc Γ t ih => exact congrArg₂ Tele.snoc ih (t.map_instL pre ls)

@[simp] theorem map_substN (pre : ζ₁ ⟶ ζ₂)
    (σ : Subst ζ₁ ℓ m n) (k : Nat) (Δ : Ctx ζ₁ ℓ m (m + k)) :
    (Δ.substN σ k).map pre = (Δ.map pre).substN (σ.map pre) k := by
  induction Δ using Tele.addInduction with
  | nil => rfl
  | snoc k Δ t ih => exact congrArg₂ Tele.snoc ih (by simp)

def proj : {k : Nat} → (f : Fin k) → Ctx ζ ℓ a (a + k) → Expr ζ ℓ (a + f)
  | 0, f, _ => nomatch f
  | k + 1, f, .snoc Γ t =>
      if h : f.val = k then cast (by rw [h]; rfl) t
      else Γ.proj (f.castLT (by omega))

@[simp] theorem proj_last (Γ : Ctx ζ ℓ a (a + k)) (t : Expr ζ ℓ (a + k)) :
    (Γ.snoc t).proj (Fin.last k) = t := by
  simp [proj]

@[simp] theorem proj_castSucc (Γ : Ctx ζ ℓ a (a + k)) (t : Expr ζ ℓ (a + k))
    (f : Fin k) :
    (Γ.snoc t).proj f.castSucc = Γ.proj f := by
  simp [proj, f.isLt.ne]

@[simp] theorem map_proj (pre : ζ₁ ⟶ ζ₂) (f : Fin k)
    (Γ : Ctx ζ₁ ℓ a (a + k)) :
    (Γ.proj f).map pre = (Γ.map pre).proj f := by
  induction f using Fin.lastInduction with
  | last k => cases Γ; simp
  | cast f ih => cases Γ; simp [ih]

@[reducible] def piHom (ℓ a b : Nat) :=
  Tele.foldNatTrans (Expr.functor ℓ) (Expr.functor ℓ)
    (fun n => ((flipFunctor _ _ _).map (Expr.forallHom n)).app ℓ) a b

@[reducible] def lamHom (ℓ a b : Nat) :=
  Tele.foldNatTrans (Expr.functor ℓ) (Expr.functor ℓ)
    (fun n => ((flipFunctor _ _ _).map (Expr.lamHom n)).app ℓ) a b

@[reducible] def piLevelHom (ζ : Sigs) (a b : Nat) :=
  Tele.foldNatTrans (fun n => (Expr.family n).obj ζ) (fun n => (Expr.family n).obj ζ)
    (fun n => (Expr.forallHom n).app ζ) a b

@[reducible] def lamLevelHom (ζ : Sigs) (a b : Nat) :=
  Tele.foldNatTrans (fun n => (Expr.family n).obj ζ) (fun n => (Expr.family n).obj ζ)
    (fun n => (Expr.lamHom n).app ζ) a b

@[reducible] def foldSubstHom
    (α : letI := Subst.category ζ ℓ; Subst.functor ζ ℓ ⊗ (Subst.shift 1 ⋙ Subst.functor ζ ℓ) ⟶ Subst.functor ζ ℓ)
    (k : Nat) :
    letI := Subst.category ζ ℓ
    substFunctor k ⊗ (Subst.shift k ⋙ Subst.functor ζ ℓ) ⟶ Subst.functor ζ ℓ :=
  letI := Subst.category ζ ℓ
  { app _ := ↾fun ⟨Δ, e⟩ => Tele.foldr (fun {d} t e => α.app d ⟨t, e⟩) e Δ
    naturality := by
      intro m n σ
      ext ⟨Δ, e⟩
      induction Δ using Tele.addInduction with
      | nil => rfl
      | snoc k Δ t ih =>
        exact (congrArg
          (fun e => Tele.foldr (fun {d} t e => α.app d ⟨t, e⟩) e (substN σ k Δ))
          (α.naturality_apply ((Subst.shift k).map σ) ⟨t, e⟩)).trans (ih (α.app _ ⟨t, e⟩)) }

@[reducible] def foldSubstHom₂
    (α : letI := Subst.category ζ ℓ; Subst.functor ζ ℓ ⊗ (Subst.shift 1 ⋙ Subst.functor ζ ℓ) ⟶ Subst.functor ζ ℓ)
    (a b : Nat) :
    letI := Subst.category ζ ℓ
    substFunctor₂ a b ⊗ (Subst.shift a ⋙ Subst.shift b ⋙ Subst.functor ζ ℓ) ⟶ Subst.functor ζ ℓ := by
  letI := Subst.category ζ ℓ
  let β :=
    ((substFunctor a ⊗ (Subst.shift a ⋙ substFunctor b)).isoCopyObj
      (fun n => Ctx ζ ℓ n (n + a + b))
      (fun n => Tele.appendIso (Nat.le_add_right n a) b)).inv ▷
        (Subst.shift a ⋙ Subst.shift b ⋙ Subst.functor ζ ℓ) ≫
      (α_ _ _ _).hom ≫
      substFunctor a ◁ Functor.whiskerLeft (Subst.shift a) (foldSubstHom α b) ≫
      foldSubstHom α a
  have h (n) : β.app n = ↾fun ⟨Δ, e⟩ => Tele.foldr (fun {d} t e => α.app d ⟨t, e⟩) e Δ := by
    ext ⟨Δ, e⟩
    let parts := Tele.split (Nat.le_add_right n a) b Δ
    exact (Tele.foldr_append (fun {d} t e => α.app d ⟨t, e⟩) e parts.1 parts.2).symm.trans
      (congrArg (Tele.foldr (fun {d} t e => α.app d ⟨t, e⟩) e) (Tele.append_split (Nat.le_add_right n a) Δ))
  exact
    { app _ := ↾fun ⟨Δ, e⟩ => Tele.foldr (fun {d} t e => α.app d ⟨t, e⟩) e Δ
      naturality X Y σ :=
        (congr(_ ≫ $((h Y).symm))).trans ((β.naturality σ).trans congr($(h X) ≫ _)) }

@[reducible] def foldSubstHom₃
    (α : letI := Subst.category ζ ℓ; Subst.functor ζ ℓ ⊗ (Subst.shift 1 ⋙ Subst.functor ζ ℓ) ⟶ Subst.functor ζ ℓ)
    (a b k : Nat) :
    letI := Subst.category ζ ℓ
    substFunctor₃ a b k ⊗ (Subst.shift a ⋙ Subst.shift b ⋙ Subst.shift k ⋙ Subst.functor ζ ℓ) ⟶
      Subst.functor ζ ℓ := by
  letI := Subst.category ζ ℓ
  let β :=
    ((substFunctor₂ a b ⊗ (Subst.shift a ⋙ Subst.shift b ⋙ substFunctor k)).isoCopyObj
      (fun n => Ctx ζ ℓ n (n + a + b + k))
      (fun n => Tele.appendIso ((Nat.le_add_right n a).trans (Nat.le_add_right _ b)) k)).inv ▷
        (Subst.shift a ⋙ Subst.shift b ⋙ Subst.shift k ⋙ Subst.functor ζ ℓ) ≫
      (α_ _ _ _).hom ≫
      substFunctor₂ a b ◁ Functor.whiskerLeft (Subst.shift a ⋙ Subst.shift b) (foldSubstHom α k) ≫
      foldSubstHom₂ α a b
  have h (n) : β.app n = ↾fun ⟨Δ, e⟩ => Tele.foldr (fun {d} t e => α.app d ⟨t, e⟩) e Δ := by
    ext ⟨Δ, e⟩
    let parts := Tele.split ((Nat.le_add_right n a).trans (Nat.le_add_right _ b)) k Δ
    exact (Tele.foldr_append (fun {d} t e => α.app d ⟨t, e⟩) e parts.1 parts.2).symm.trans
      (congrArg (Tele.foldr (fun {d} t e => α.app d ⟨t, e⟩) e)
        (Tele.append_split ((Nat.le_add_right n a).trans (Nat.le_add_right _ b)) Δ))
  exact
    { app _ := ↾fun ⟨Δ, e⟩ => Tele.foldr (fun {d} t e => α.app d ⟨t, e⟩) e Δ
      naturality X Y σ :=
        (congr(_ ≫ $((h Y).symm))).trans ((β.naturality σ).trans congr($(h X) ≫ _)) }

def pi : Expr ζ ℓ n → Ctx ζ ℓ a n → Expr ζ ℓ a := Tele.foldr Expr.forallE
def lam : Expr ζ ℓ n → Ctx ζ ℓ a n → Expr ζ ℓ a := Tele.foldr Expr.lam

@[simp] theorem pi_nil (e : Expr ζ ℓ n) : Ctx.nil.pi e = e := rfl
@[simp] theorem lam_nil (e : Expr ζ ℓ n) : Ctx.nil.lam e = e := rfl

@[simp] theorem map_pi (pre : ζ₁ ⟶ ζ₂) (e : Expr ζ₁ ℓ n)
    (Γ : Ctx ζ₁ ℓ a n) :
    (Γ.pi e).map pre = (Γ.map pre).pi (e.map pre) :=
  ((piHom ℓ a n).naturality_apply pre ⟨Γ, e⟩).symm

@[simp] theorem map_lam (pre : ζ₁ ⟶ ζ₂) (e : Expr ζ₁ ℓ n)
    (Γ : Ctx ζ₁ ℓ a n) :
    (Γ.lam e).map pre = (Γ.map pre).lam (e.map pre) :=
  ((lamHom ℓ a n).naturality_apply pre ⟨Γ, e⟩).symm

def entry {m : Nat} : Ctx ζ ℓ b m → b ≤ p → p < m → Expr ζ ℓ p
  | .nil => by omega
  | .snoc (b := c) Δ t => fun hb hp =>
      if h : p = c then h.symm ▸ t else Δ.entry hb (by omega)

@[simp] theorem entry_snoc_self (Δ : Ctx ζ ℓ a b) (t : Expr ζ ℓ b) (hb : a ≤ b)
    (hp : b < b + 1) :
    (Δ.snoc t).entry hb hp = t := by
  simp [entry]

@[simp] theorem entry_snoc_of_lt (Δ : Ctx ζ ℓ a b) (t : Expr ζ ℓ b) (hb : a ≤ p)
    (hp : p < b + 1) (hlt : p < b) :
    (Δ.snoc t).entry hb hp = Δ.entry hb hlt := by
  simp [entry, show p ≠ b by omega]

theorem ext {a k : Nat} (Δ₁ Δ₂ : Ctx ζ ℓ a (a + k))
    (h : ∀ (p : Nat) (hp : a ≤ p) (hp' : p < a + k), Δ₁.entry hp hp' = Δ₂.entry hp hp') :
    Δ₁ = Δ₂ := by
  induction k with
  | zero =>
    cases Δ₁ with
    | nil =>
      cases Δ₂ with
      | nil => rfl
      | snoc Γ _ => exact absurd Γ.le (Nat.not_succ_le_self _)
    | snoc Γ _ => exact absurd Γ.le (Nat.not_succ_le_self _)
  | succ k ih =>
    have .snoc Γ₁ t₁ := Δ₁
    have .snoc Γ₂ t₂ := Δ₂
    have htop := h (a + k) (Nat.le_add_right a k) (by omega)
    rw [entry_snoc_self, entry_snoc_self] at htop
    refine congrArg₂ Tele.snoc (ih Γ₁ Γ₂ fun p hp hp' => ?_) htop
    have hp₂ := h p hp (by omega)
    rwa [entry_snoc_of_lt _ _ _ _ hp', entry_snoc_of_lt _ _ _ _ hp'] at hp₂

@[simp] theorem get_last (Γ : Ctx ζ ℓ 0 n) (t : Expr ζ ℓ n) :
    (Γ.snoc t).get (Fin.last n) = t.wk := by
  change dite _ _ _ = _
  simp

@[simp] theorem entry_map (pre : ζ₁ ⟶ ζ₂)
    (Γ : Ctx ζ₁ ℓ a b) (ha : a ≤ p) (hp : p < b) :
    (Γ.entry ha hp).map pre = (Γ.map pre).entry ha hp := by
  induction Γ with
  | nil => omega
  | @snoc b Γ t ih =>
    by_cases h : p = b
    · subst p
      simp!
    · simp! [h, ih]

@[simp] theorem entry_instL (levelSubst : Param ℓ → Level ℓ')
    (Γ : Ctx ζ ℓ a b) (ha : a ≤ p) (hp : p < b) :
    (Γ.entry ha hp).instL levelSubst = (Γ.instL levelSubst).entry ha hp := by
  induction Γ with
  | nil => omega
  | @snoc b Γ t ih =>
    by_cases h : p = b
    · subst p
      simp! [instL]
    · simp! [instL, h, ih]

theorem proj_eq_entry (f : Fin k) (Γ : Ctx ζ ℓ a (a + k)) :
    Γ.proj f = Γ.entry (by omega) (by omega) := by
  induction f using Fin.lastInduction with
  | last k =>
    have .snoc Γ t := Γ
    simp!
  | cast f ih =>
    have .snoc Γ t := Γ
    simpa! [f.isLt.ne] using ih Γ

@[simp] theorem entry_append_left (Γ : Ctx ζ ℓ a b)
    (Δ : Ctx ζ ℓ b d) (ha : a ≤ p) (hp : p < b) (hp' : p < d) :
    Ctx.entry (Γ ++ Δ) ha hp' = Γ.entry ha hp := by
  induction Δ with
  | nil => rfl
  | @snoc d Δ t ih =>
    have hpd : p < d := hp.trans_le (Tele.le Δ)
    simp! [hpd.ne]
    exact ih hpd

-- TODO ha is admissible via Γ.le.trans hb
theorem entry_append_right (Γ : Ctx ζ ℓ a b)
    (Δ : Ctx ζ ℓ b d) (ha : a ≤ p) (hb : b ≤ p) (hp : p < d) :
    Ctx.entry (Γ ++ Δ) ha hp = Δ.entry hb hp := by
  induction Δ with
  | nil => omega
  | @snoc d Δ t ih =>
    by_cases h : p = d
    · simp! [h]
    · simp! [h]
      exact ih (by omega)

theorem get_instL (levelSubst : Param ℓ → Level ℓ') (Γ : Ctx ζ ℓ 0 n) (v : Var n) :
    (Γ.get v).instL levelSubst = (Γ.instL levelSubst).get v := by
  induction Γ with
  | nil => exact Fin.elim0 v
  | @snoc n Γ t ih =>
    simp! [instL]
    split
    · exact Expr.instL_wk levelSubst t
    · exact (Expr.instL_wk levelSubst _).trans (congrArg Expr.wk (ih _))

@[simp] theorem instL_instL (levelSubst₁ : Param ℓ → Level ℓ')
    (levelSubst₂ : Param ℓ' → Level k)
    (Γ : Ctx ζ ℓ a b) :
    (Γ.instL levelSubst₁).instL levelSubst₂ =
      Γ.instL fun p => (levelSubst₁ p).inst levelSubst₂ :=
  ((levelFunctor ζ a b).map_comp_apply levelSubst₁ levelSubst₂ Γ).symm

@[simp] theorem instL_substN (levelSubst : Param ℓ → Level ℓ') (σ : Subst ζ ℓ m n)
    {k : Nat} (Δ : Ctx ζ ℓ m (m + k)) :
    (Δ.substN σ k).instL levelSubst =
      (Δ.instL levelSubst).substN (Subst.instL levelSubst σ) k := by
  induction Δ using Tele.addInduction with
  | nil => rfl
  | snoc k Δ t ih => exact congrArg₂ Tele.snoc ih (by simp)

@[simp] theorem pi_instL (levelSubst : Param ℓ → Level ℓ') (Δ : Ctx ζ ℓ a b)
    (e : Expr ζ ℓ b) :
    (Δ.pi e).instL levelSubst = (Δ.instL levelSubst).pi (e.instL levelSubst) :=
  ((piLevelHom ζ a b).naturality_apply levelSubst ⟨Δ, e⟩).symm

@[simp] theorem lam_instL (levelSubst : Param ℓ → Level ℓ') (Δ : Ctx ζ ℓ a b)
    (e : Expr ζ ℓ b) :
    (Δ.lam e).instL levelSubst = (Δ.instL levelSubst).lam (e.instL levelSubst) :=
  ((lamLevelHom ζ a b).naturality_apply levelSubst ⟨Δ, e⟩).symm

@[simp] theorem instL_append (levelSubst : Param ℓ → Level ℓ') (Γ : Ctx ζ ℓ a b)
    (Δ : Ctx ζ ℓ b k) :
    instL levelSubst (Γ ++ Δ) = Γ.instL levelSubst ++ Δ.instL levelSubst :=
  @Functor.map_comp _ (Tele.category _) _ (Tele.category _) (Tele.mapFunctor fun n => ((Expr.family n).obj ζ).map levelSubst) _ _ _ Γ Δ

@[simp] theorem instL_param (Γ : Ctx ζ ℓ a b) : Γ.instL Level.param = Γ :=
  (levelFunctor ζ a b).map_id_apply ℓ Γ

@[simp] def ofTypes : {k : Nat} → (Fin k → Expr ζ ℓ n) → Ctx ζ ℓ n (n + k)
  | 0 => fun _ => .nil
  | k + 1 => fun types =>
    (ofTypes fun i => types i.castSucc).snoc ((types (Fin.last k)).wkN k)

@[simp] theorem ofTypes_map {k : Nat} (types : Fin k → Expr ζ₁ ℓ n)
    (pre : ζ₁ ⟶ ζ₂) :
    (ofTypes types).map pre = ofTypes fun i => (types i).map pre := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg₂ Tele.snoc (ih fun i => types i.castSucc)
      (Expr.map_wkN pre (types (Fin.last k)) k)

@[simp] theorem ofTypes_instL {k : Nat} (types : Fin k → Expr ζ ℓ n)
    (ls : Param ℓ → Level ℓ') :
    (ofTypes types).instL ls = ofTypes fun i => (types i).instL ls := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact congrArg₂ Tele.snoc (ih fun i => types i.castSucc)
      (Expr.wkN_instL ls (types (Fin.last k)) k)

@[simp] theorem entry_ofTypes {k : Nat} (types : Fin k → Expr ζ ℓ n) (f : Fin k) :
    (ofTypes types).entry (p := n + f.val) (by omega) (by omega) =
      (types f).wkN f.val := by
  induction f using Fin.lastInduction with
  | last k => simp!
  | cast f ih =>
    simpa! [f.isLt.ne] using ih fun i => types i.castSucc

@[simp] theorem get_append_ofTypes {k : Nat} (Γ : Ctx ζ ℓ 0 n)
    (types : Fin k → Expr ζ ℓ n) (f : Fin k) :
    get (Fin.natAdd n f) (Γ ++ ofTypes types) = (types f).wkN k := by
  induction f using Fin.lastInduction with
  | last k => simp!
  | cast f ih =>
    simp! [f.isLt.ne]
    exact congrArg Expr.wk (ih fun i => types i.castSucc)

end Ctx

end Metalean
