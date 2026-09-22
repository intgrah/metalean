/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Category
public import Metalean.TypeTheory.NaturalModel.Defs

@[expose] public noncomputable section

namespace Metalean

open CategoryTheory Opposite TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ Γ₁ Γ₂ : CtxCat E ℓ}

@[ext] structure Ty.Repr (Γ : CtxCat E ℓ) where
  term : Expr ζ ℓ Γ.as.len
  wf : E[Γ.as.ctx] ⊢ term typ

namespace Ty

instance Repr.setoid (Γ : CtxCat E ℓ) : Setoid (Repr Γ) where
  r A B := E[Γ.as.ctx] ⊢ A.term ≡ B.term typ
  iseqv := ⟨fun A => A.wf.typeEq, TypeEq.symm, TypeEq.trans⟩

def Element (Γ : CtxCat E ℓ) := Quotient (Repr.setoid Γ)

def reindex (σ : Γ₂.as ⟶ Γ₁.as) : Element Γ₁ → Element Γ₂ :=
  Quotient.map
    (fun A => ⟨RawCtx.expr.map σ.op A.term, A.wf.substitution σ.typed⟩)
    (fun _ _ h => h.substitution σ.typed)

@[reducible] def functor : (RawCtx E ℓ)ᵒᵖ ⥤ Type where
  obj Γ := Element ⟨Γ.unop⟩
  map σ := ↾reindex σ.unop
  map_id Γ := by
    apply ConcreteCategory.hom_ext
    intro A
    obtain ⟨A⟩ := A
    exact congrArg (⟦·⟧) (Repr.ext (RawCtx.expr.map_id_apply Γ A.term))
  map_comp σ₁ σ₂ := by
    apply ConcreteCategory.hom_ext
    intro A
    obtain ⟨A⟩ := A
    exact congrArg (⟦·⟧) (Repr.ext (RawCtx.expr.map_comp_apply σ₁ σ₂ A.term))

end Ty

@[implicit_reducible] def Ty (E : Env ζ) (ℓ : Nat) : (CtxCat E ℓ)ᵒᵖ ⥤ Type :=
  (CategoryTheory.Quotient.lift (RawCtx.homRel E ℓ) Ty.functor.rightOp fun _ Γ₁ _ _ h =>
    Quiver.Hom.unop_inj (ConcreteCategory.hom_ext _ _ fun A => by
      obtain ⟨A⟩ := A
      exact Quotient.sound (TypeEq.substitution_congr Γ₁.wf h A.wf.typeEq))).leftOp

notation:max "Ty_" Γ:max => Functor.obj (Metalean.Ty _ _) (Opposite.op Γ)

namespace Ty

def elim {β : Sort*} (A : Ty_ Γ) (f : (T : Repr Γ) → A = ⟦T⟧ → β)
    (hf : ∀ T₁ T₂ (h₁ : A = ⟦T₁⟧) (h₂ : A = ⟦T₂⟧), f T₁ h₁ = f T₂ h₂) : β :=
  Quotient.pliftOn A f fun _ _ _ _ _ => hf _ _ _ _

theorem elim_eq {β : Sort*} (A : Ty_ Γ) (f : (T : Repr Γ) → A = ⟦T⟧ → β)
    (hf : ∀ T₁ T₂ (h₁ : A = ⟦T₁⟧) (h₂ : A = ⟦T₂⟧), f T₁ h₁ = f T₂ h₂)
    (T : Repr Γ) (h : A = ⟦T⟧) : elim A f hf = f T h := by
  subst h
  rfl

def ofTyping (Γ : RawCtx E ℓ) {t : Expr ζ ℓ Γ.len} {u : Level ℓ}
    (ht : E[Γ.ctx] ⊢ t : .sort u) : Ty_ (⟨Γ⟩ : CtxCat E ℓ) :=
  ⟦⟨t, u, ht⟩⟧

end Ty

@[simp] theorem Ty.map_ofTyping {t : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}
    (ht : E[Γ₁.as.ctx] ⊢ t : .sort u) (σ : Γ₂.as ⟶ Γ₁.as) :
    (Ty E ℓ).map (RawCtx.toCtx.map σ).op (ofTyping Γ₁.as ht) =
      ofTyping Γ₂.as (ht.substitution σ.typed) :=
  rfl

@[ext] structure Tm.Repr (Γ : CtxCat E ℓ) where
  ty : Expr ζ ℓ Γ.as.len
  val : Expr ζ ℓ Γ.as.len
  tyWF : E[Γ.as.ctx] ⊢ ty typ
  valWF : E[Γ.as.ctx] ⊢ val : ty

namespace Tm

instance Repr.setoid (Γ : CtxCat E ℓ) : Setoid (Repr Γ) where
  r p q := E[Γ.as.ctx] ⊢ p.ty ≡ q.ty typ ∧ E[Γ.as.ctx] ⊢ p.val ≡ q.val : p.ty
  iseqv := {
    refl p := ⟨p.tyWF.typeEq, p.valWF⟩
    symm | ⟨hty, hval⟩ => ⟨hty.symm, hty.conv hval.symm⟩
    trans := fun ⟨hpqTy, hpqVal⟩ ⟨hqrTy, hqrVal⟩ =>
      ⟨hpqTy.trans hqrTy, hpqVal.trans (hpqTy.symm.conv hqrVal)⟩
    }

def Element (Γ : CtxCat E ℓ) := Quotient (Repr.setoid Γ)

def type : Element Γ → Ty.Element Γ :=
  Quotient.lift (fun p => ⟦⟨p.ty, p.tyWF⟩⟧)
    fun _ _ h => Quotient.sound h.1

def reindex (σ : Γ₂.as ⟶ Γ₁.as) (a : Element Γ₁) : Element Γ₂ :=
  Quotient.map (sa := Repr.setoid Γ₁) (sb := Repr.setoid Γ₂)
    (fun p => ⟨RawCtx.expr.map σ.op p.ty, RawCtx.expr.map σ.op p.val,
      p.tyWF.substitution σ.typed, p.valWF.substitution σ.typed⟩)
    (fun _ _ ⟨hA, ha⟩ => ⟨hA.substitution σ.typed, ha.substitution σ.typed⟩) a

@[reducible] def functor : (RawCtx E ℓ)ᵒᵖ ⥤ Type where
  obj Γ := Element ⟨Γ.unop⟩
  map σ := ↾reindex σ.unop
  map_id Γ := by
    ext ⟨ty, val, tyWF, valWF⟩
    exact congrArg (⟦·⟧) <|
      Repr.ext (RawCtx.expr.map_id_apply Γ ty) (RawCtx.expr.map_id_apply Γ val)
  map_comp σ₁ σ₂ := by
    ext ⟨p⟩
    exact congrArg (⟦·⟧) <|
      Repr.ext (RawCtx.expr.map_comp_apply σ₁ σ₂ p.ty)
        (RawCtx.expr.map_comp_apply σ₁ σ₂ p.val)

end Tm

@[implicit_reducible] def Tm (E : Env ζ) (ℓ : Nat) : (CtxCat E ℓ)ᵒᵖ ⥤ Type :=
  (CategoryTheory.Quotient.lift (RawCtx.homRel E ℓ) Tm.functor.rightOp fun _ Γ₁ _ _ h => by
    apply Quiver.Hom.unop_inj
    ext ⟨p⟩
    exact Quotient.sound ⟨TypeEq.substitution_congr Γ₁.wf h p.tyWF.typeEq,
      Defeq.substitution_congr Γ₁.wf h p.valWF⟩).leftOp

def Tm.typing (E : Env ζ) (ℓ : Nat) : Tm E ℓ ⟶ Ty E ℓ where
  app _ := ↾Tm.type
  naturality := by
    intro ⟨Γ₁⟩ ⟨Γ₂⟩ ⟨σ⟩
    obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
    exact ConcreteCategory.hom_ext _ _ fun a => by
      obtain ⟨p⟩ := a
      rfl

notation:max "Tm_" Γ:max => Functor.obj (Tm _ _) (Opposite.op Γ)

namespace Tm

@[simp] theorem type_map (σ : Γ₂ ⟶ Γ₁) (n : Tm_ Γ₁) :
    type ((Tm E ℓ).map σ.op n) = (Ty E ℓ).map σ.op (type n) :=
  NatTrans.naturality_apply (Tm.typing E ℓ) σ.op n

def label (Γ : RawCtx E ℓ) {t e : Expr ζ ℓ Γ.len} (he : E[Γ.ctx] ⊢ e : t) : Tm_ (⟨Γ⟩ : CtxCat E ℓ) :=
  ⟦⟨t, e, he.regular, he⟩⟧

@[simp] theorem type_label {Γ : RawCtx E ℓ} {t e : Expr ζ ℓ Γ.len} (he : E[Γ.ctx] ⊢ e : t) :
    type (label Γ he) = ⟦⟨t, he.regular⟩⟧ :=
  rfl

theorem label_eq {Γ : RawCtx E ℓ} {t₁ e₁ t₂ e₂ : Expr ζ ℓ Γ.len}
    {he₁ : E[Γ.ctx] ⊢ e₁ : t₁} {he₂ : E[Γ.ctx] ⊢ e₂ : t₂}
    (ht : E[Γ.ctx] ⊢ t₁ ≡ t₂ typ) (he : E[Γ.ctx] ⊢ e₁ ≡ e₂ : t₁) : label Γ he₁ = label Γ he₂ :=
  Quotient.sound ⟨ht, he⟩

def elim {β : Sort*} (n : Tm_ Γ) (T : Ty.Repr Γ) (hn : type n = ⟦T⟧)
    (f : (e : Expr ζ ℓ Γ.as.len) → E[Γ.as.ctx] ⊢ e : T.term → β)
    (hf : ∀ e₁ e₂ (h₁ : E[Γ.as.ctx] ⊢ e₁ : T.term) (h₂ : E[Γ.as.ctx] ⊢ e₂ : T.term),
      E[Γ.as.ctx] ⊢ e₁ ≡ e₂ : T.term → f e₁ h₁ = f e₂ h₂) : β :=
  Quotient.pliftOn n (fun R hR => f R.val (TypeEq.conv (Quotient.exact ((congrArg type hR).symm.trans hn)) R.valWF))
    fun _ _ h₁ _ h => hf _ _ _ _ <|
      TypeEq.conv (Quotient.exact ((congrArg type h₁).symm.trans hn)) h.2

theorem exists_label (n : Tm_ Γ) (T : Ty.Repr Γ) (hn : type n = ⟦T⟧) :
    ∃ e, ∃ he : E[Γ.as.ctx] ⊢ e : T.term, n = label Γ.as he := by
  obtain ⟨R, rfl⟩ := Quotient.exists_rep n
  have hty : E[Γ.as.ctx] ⊢ R.ty ≡ T.term typ := Quotient.exact hn
  exact ⟨R.val, hty.conv R.valWF, Quotient.sound ⟨hty, R.valWF⟩⟩

theorem subsingleton_of_prop {P : Expr ζ ℓ Γ₁.as.len} {u : Level ℓ}
    (hP : E[Γ₁.as.ctx] ⊢ P : .sort u) (hu : u = .zero) (σ : Γ₂ ⟶ Γ₁) :
    {n : Tm_ Γ₂ | type n = (Ty E ℓ).map σ.op (Ty.ofTyping Γ₁.as hP)}.Subsingleton := by
  obtain ⟨σ, rfl⟩ := RawCtx.toCtx.map_surjective σ
  subst hu
  intro n₁ h₁ n₂ h₂
  have hPσ := hP.substitution σ.typed
  have ⟨e₁, he₁, hn₁⟩ := exists_label n₁ ⟨_, _, hPσ⟩ h₁
  have ⟨e₂, he₂, hn₂⟩ := exists_label n₂ ⟨_, _, hPσ⟩ h₂
  exact hn₁.trans ((label_eq (.ofDefEq hPσ) (Defeq.proofIrrel hPσ he₁ he₂)).trans hn₂.symm)

def varLabel (Γ : CtxCat E ℓ) (v : Var Γ.as.len) : Tm_ Γ :=
  label Γ.as (Γ.as.wf.var v)

theorem label_eq_var {Γ : CtxCat E ℓ} {t e : Expr ζ ℓ Γ.as.len} {v : Var Γ.as.len}
    (he : E[Γ.as.ctx] ⊢ e : t) (h : e = .var v) : label Γ.as he = varLabel Γ v := by
  subst e
  exact label_eq he.var_inv he

@[simp] theorem map_label {t e : Expr ζ ℓ Γ₁.as.len} (he : E[Γ₁.as.ctx] ⊢ e : t)
    (σ : Γ₂.as ⟶ Γ₁.as) :
    (Tm E ℓ).map (RawCtx.toCtx.map σ).op (label Γ₁.as he) =
      label Γ₂.as (he.substitution σ.typed) :=
  rfl

@[simp] theorem map_varLabel (σ : Γ₂.as ⟶ Γ₁.as) (v : Var Γ₁.as.len) :
    (Tm E ℓ).map (RawCtx.toCtx.map σ).op (varLabel Γ₁ v) = label Γ₂.as (σ.typed v) :=
  map_label (Γ₁.as.wf.var v) σ

theorem hom_ext (σ₁ σ₂ : Γ₁ ⟶ Γ₂)
    (h : ∀ v, (Tm E ℓ).map σ₁.op (varLabel Γ₂ v) = (Tm E ℓ).map σ₂.op (varLabel Γ₂ v)) :
    σ₁ = σ₂ := by
  obtain ⟨σ₁⟩ := σ₁
  obtain ⟨σ₂⟩ := σ₂
  exact (RawCtx.toCtx_map_eq_iff σ₁ σ₂).mpr fun v =>
    (Quotient.exact ((map_varLabel σ₁ v).symm.trans ((h v).trans (map_varLabel σ₂ v)))).2

def rawBinderVar (Γ : RawCtx E ℓ) {t : Expr ζ ℓ Γ.len} {u : Level ℓ}
    (ht : E[Γ.ctx] ⊢ t : .sort u) : Tm_ (CtxCat.extension ⟨Γ⟩ ht) :=
  varLabel (CtxCat.extension ⟨Γ⟩ ht) (Fin.last Γ.len)

end Tm

end Metalean
