module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Quotient
public import Metalean.TypeTheory.NaturalModel.Defs
public import Metalean.Strong.Context
public import Metalean.Strong.Substitution
public import Metalean.Syntax.Substitution
public import Metalean.Strong.Telescope

@[expose] public section

namespace Metalean

open CategoryTheory Limits TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ n m p : Nat}
variable {Γ₁ : Ctx ζ ℓ 0 n} {Γ₂ : Ctx ζ ℓ 0 m} {Γ₃ : Ctx ζ ℓ 0 p}

structure RawCtx (E : Env ζ) (ℓ : Nat) where
  {len : Nat}
  ctx : Ctx ζ ℓ 0 len
  wf : E[ctx] ⊢ₛ ok

namespace RawCtx

abbrev snoc (Γ : RawCtx E ℓ) {t : Expr ζ ℓ Γ.len} (ht : E[Γ.ctx] ⊢ₛ t typ) : RawCtx E ℓ where
  ctx := Γ.ctx.snoc t
  wf := Γ.wf.snoc ht

structure Hom (Γ₁ Γ₂ : RawCtx E ℓ) where
  subst : Subst ζ ℓ Γ₂.len Γ₁.len
  typed : E[Γ₁.ctx] ⊢ₛ subst ⊣ Γ₂.ctx

namespace Hom

variable {Γ₁ Γ₂ : RawCtx E ℓ}

@[ext] theorem ext {σ₁ σ₂ : Hom Γ₁ Γ₂} (h : σ₁.subst = σ₂.subst) : σ₁ = σ₂ := by
  cases σ₁
  cases σ₂
  cases h
  rfl

end Hom

instance : Category (RawCtx E ℓ) where
  Hom := Hom
  id Γ := ⟨Subst.id, .id Γ.wf⟩
  comp σ₁ σ₂ := ⟨Subst.comp σ₂.subst σ₁.subst, σ₂.typed.comp σ₁.typed⟩
  id_comp σ := Hom.ext ((Subst.category ζ ℓ).comp_id σ.subst)
  comp_id σ := Hom.ext ((Subst.category ζ ℓ).id_comp σ.subst)
  assoc σ₁ σ₂ σ₃ := Hom.ext ((Subst.category ζ ℓ).assoc σ₃.subst σ₂.subst σ₁.subst).symm

@[reducible] def substitution : @Functor (RawCtx E ℓ)ᵒᵖ _ Nat (Subst.category ζ ℓ) :=
  letI := Subst.category ζ ℓ
  { obj Γ := Γ.unop.len, map σ := σ.unop.subst }

abbrev expr : (RawCtx E ℓ)ᵒᵖ ⥤ Type :=
  letI := Subst.category ζ ℓ
  substitution ⋙ Subst.functor ζ ℓ

namespace Hom

variable {Γ₁ Γ₂ Γ₃ : RawCtx E ℓ}

def snoc (σ : Γ₁ ⟶ Γ₂) {e : Expr ζ ℓ Γ₁.len} {t : Expr ζ ℓ Γ₂.len}
    (ht : E[Γ₂.ctx] ⊢ₛ t typ)
    (he : E[Γ₁.ctx] ⊢ₛ e : t.subst σ.subst) :
    Γ₁ ⟶ Γ₂.snoc ht where
  subst := σ.subst.extend e
  typed := σ.typed.extend he

def one {t e : Expr ζ ℓ Γ₂.len} (ht : E[Γ₂.ctx] ⊢ₛ t typ) (he : E[Γ₂.ctx] ⊢ₛ e : t) :
    Γ₂ ⟶ Γ₂.snoc ht where
  subst := Subst.id.extend e
  typed := SubstWFStrong.inst Γ₂.wf he

def lift (σ : Γ₁ ⟶ Γ₂) {t : Expr ζ ℓ Γ₂.len} (ht : E[Γ₂.ctx] ⊢ₛ t typ) :
    Γ₁.snoc (ht.substitution σ.typed) ⟶ Γ₂.snoc ht where
  subst := σ.subst.lift
  typed := σ.typed.lift ht

@[simp] theorem id_subst : Hom.subst (𝟙 Γ₂) = Subst.id := rfl

@[simp] theorem snoc_subst (σ : Γ₁ ⟶ Γ₂) {t : Expr ζ ℓ Γ₂.len} (ht : E[Γ₂.ctx] ⊢ₛ t typ)
    {e : Expr ζ ℓ Γ₁.len} (he : E[Γ₁.ctx] ⊢ₛ e : t.subst σ.subst) :
    (σ.snoc ht he).subst = σ.subst.extend e := rfl

@[simp] theorem one_subst {t e : Expr ζ ℓ Γ₂.len} (ht : E[Γ₂.ctx] ⊢ₛ t typ)
    (he : E[Γ₂.ctx] ⊢ₛ e : t) :
    (one ht he).subst = Subst.id.extend e := rfl

def IsRenaming (r : Γ₁ ⟶ Γ₂) : Prop :=
  ∀ v, ∃ w, r.subst v = .var w

theorem IsRenaming.id : IsRenaming (𝟙 Γ₂) :=
  fun v => ⟨v, rfl⟩

theorem IsRenaming.comp {r₁ : Γ₁ ⟶ Γ₂} {r₂ : Γ₂ ⟶ Γ₃} (h₁ : IsRenaming r₁)
    (h₂ : IsRenaming r₂) : IsRenaming (r₁ ≫ r₂) := fun v =>
  have ⟨w, hw⟩ := h₂ v
  have ⟨x, hx⟩ := h₁ w
  ⟨x, show (r₂.subst v).subst r₁.subst = _ by rw [hw]; exact hx⟩

end Hom

def homRel (E : Env ζ) (ℓ : Nat) : HomRel (RawCtx E ℓ) := fun {Γ₁ Γ₂} σ₁ σ₂ =>
  E[Γ₁.ctx] ⊢ₛ σ₁.subst ≡ σ₂.subst ⊣ Γ₂.ctx

instance : Congruence (homRel E ℓ) where
  equivalence {_ Γ₂} :=
    ⟨fun σ => σ.typed, fun h => h.symm Γ₂.wf, fun h₁ h₂ => h₁.trans Γ₂.wf h₂⟩
  comp_left {_ Y _} σ {_ _} h := h.comp Y.wf σ.typed
  comp_right {_ Y _} {_ _} σ h := SubstEqStrong.comp Y.wf σ.typed h

end RawCtx

section Quotient

abbrev CtxCat (E : Env ζ) (ℓ : Nat) := Quotient (RawCtx.homRel E ℓ)

abbrev RawCtx.toCtx : RawCtx E ℓ ⥤ CtxCat E ℓ := Quotient.functor (RawCtx.homRel E ℓ)

theorem RawCtx.toCtx_map_eq_iff {Γ₁ Γ₂ : RawCtx E ℓ} (σ₁ σ₂ : Γ₁ ⟶ Γ₂) :
    toCtx.map σ₁ = toCtx.map σ₂ ↔ E[Γ₁.ctx] ⊢ₛ σ₁.subst ≡ σ₂.subst ⊣ Γ₂.ctx :=
  Quotient.functor_map_eq_iff (RawCtx.homRel E ℓ) σ₁ σ₂

abbrev CtxCat.nil (E : Env ζ) (ℓ : Nat) : CtxCat E ℓ := ⟨.nil, .nil⟩

def CtxCat.toNil (Γ : CtxCat E ℓ) : Γ ⟶ CtxCat.nil E ℓ :=
  RawCtx.toCtx.map ⟨Fin.elim0, fun v => v.elim0⟩

theorem CtxCat.hom_nil_eq {Γ : CtxCat E ℓ} (σ₁ σ₂ : Γ ⟶ CtxCat.nil E ℓ) : σ₁ = σ₂ := by
  induction σ₁ using Quot.ind
  induction σ₂ using Quot.ind
  exact congrArg _ (RawCtx.Hom.ext (funext fun v => v.elim0))

instance : HasTerminal (CtxCat E ℓ) :=
  have : IsTerminal (CtxCat.nil E ℓ) :=
    .ofUniqueHom CtxCat.toNil fun _ _ => CtxCat.hom_nil_eq _ _
  this.hasTerminal

def RawCtx.Hom.convert (Γ : RawCtx E ℓ) {t₁ t₂ : Expr ζ ℓ Γ.len}
    (h : E[Γ.ctx] ⊢ₛ t₁ ≡ t₂ typ) :
    RawCtx.Hom (Γ.snoc h.isType.2) (Γ.snoc h.isType.1) where
  subst := Subst.id
  typed := (SubstWFStrong.id (Γ.wf.snoc h.isType.1)).snocConv h

abbrev CtxCat.extension (Γ : CtxCat E ℓ) {t : Expr ζ ℓ Γ.as.len}
    {u : Level ℓ} (ht : E[Γ.as.ctx] ⊢ₛ t : .sort u) : CtxCat E ℓ :=
  ⟨Γ.as.snoc ⟨u, ht⟩⟩

end Quotient

end Metalean
