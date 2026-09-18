/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Level.Relevance
public import Metalean.TypeTheory.Syntactic.Pi.Type

@[expose] public section

namespace Metalean

open CategoryTheory TypeTheory TypeTheory.NaturalModel

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat} {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ} {k : Nat}

structure IndCode (Γ₁ : CtxCat E ℓ) where
  {ι : IndSig}
  η : Head ζ (.inductive ι)
  s : Fin ι.nsorts
  ls : Fin ι.nlevels → Level ℓ
  params : Fin ι.nparams → Tm_ Γ₁
  indices : Fin (ι.nindices s) → Tm_ Γ₁

structure QuotCode (Γ₁ : CtxCat E ℓ) where
  η : Head ζ .quot
  level : Level ℓ
  carrier : Tm_ Γ₁
  relation : Tm_ Γ₁

structure IndHead (ζ : Sigs) where
  {ι : IndSig}
  η : Head ζ (.inductive ι)
  s : Fin ι.nsorts
deriving DecidableEq

structure CtorHead (ζ : Sigs) where
  {ι : IndSig}
  η : Head ζ (.inductive ι)
  s : Fin ι.nsorts
  c : Fin (ι.nctors s)
deriving DecidableEq

abbrev IndHead.nctors (head : IndHead ζ) : Nat := head.ι.nctors head.s

abbrev IndCode.toIndHead (code : IndCode Γ₁) : IndHead ζ := ⟨code.η, code.s⟩

abbrev IndCode.ctorHead (code : IndCode Γ₁) (c : Fin code.toIndHead.nctors) :
    CtorHead ζ :=
  ⟨code.η, code.s, c⟩

abbrev CtorHead.sig (head : CtorHead ζ) : CtorSig head.ι.nsorts := head.ι.ctors head.s head.c

abbrev CtorHead.arity (head : CtorHead ζ) : Nat := head.sig.nfields + head.sig.nrecFields

abbrev CtorHead.toIndHead (head : CtorHead ζ) : IndHead ζ := ⟨head.η, head.s⟩

abbrev CtorHead.IsStructural (E : Env ζ) (head : CtorHead ζ) : Prop :=
  (E.get head.η).block.IsStructure head.s head.c

inductive Shape (Γ₁ : CtxCat E ℓ) : Type where
  | bot
  | sort (level : Level ℓ)
  | forallE (label : Ty.Pair Γ₁) (dom : Shape Γ₁) (k : Nat) (names : Fin k → Tm_ Γ₁)
      (ins outs : Fin k → Shape Γ₁)
  | lam (k : Nat) (names : Fin k → Tm_ Γ₁) (ins outs : Fin k → Shape Γ₁)
  | ind (code : IndCode Γ₁) (ctorTypes : Fin code.toIndHead.nctors → Shape Γ₁)
  | ctor (head : CtorHead ζ) (names : Fin head.arity → Tm_ Γ₁)
      (fields : Fin head.arity → Shape Γ₁)
  | struct (head : CtorHead ζ) (hstruct : head.IsStructural E)
      (fields : Fin head.arity → Shape Γ₁)
  | quot (code : QuotCode Γ₁)
  | quotMk (η : Head ζ .quot) (name : Tm_ Γ₁) (value : Shape Γ₁)

namespace IndCode

@[reducible] def map (arg : (Tm_ Γ₁) → Tm_ Γ₂) (code : IndCode Γ₁) :
    IndCode Γ₂ :=
  ⟨code.η, code.s, code.ls, fun i => arg (code.params i), fun i => arg (code.indices i)⟩

@[simp] theorem map_id (code : IndCode Γ₁) : code.map id = code := rfl

@[simp] theorem map_map (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (arg' : (Tm_ Γ₂) → Tm_ Γ₃) (code : IndCode Γ₁) :
    (code.map arg).map arg' = code.map (arg' ∘ arg) := rfl

noncomputable def rel (code : IndCode Γ₁) : Bool :=
  ((E.get code.η).block.level.inst code.ls).rel

@[simp] theorem rel_map (arg : (Tm_ Γ₁) → Tm_ Γ₂) (code : IndCode Γ₁) :
    (code.map arg).rel = code.rel := rfl

@[simp] theorem map_hom_id (code : IndCode Γ₁) :
    code.map ((Tm E ℓ).map (𝟙 Γ₁).op) = code := by
  simp [map]

theorem map_comp_hom (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) (code : IndCode Γ₁) :
    code.map ((Tm E ℓ).map (σ₂ ≫ σ₁).op) =
      (code.map ((Tm E ℓ).map σ₁.op)).map ((Tm E ℓ).map σ₂.op) :=
  congrArg code.map (funext fun x => (Tm E ℓ).map_comp_apply σ₁.op σ₂.op x)

end IndCode

namespace QuotCode

def map (arg : (Tm_ Γ₁) → Tm_ Γ₂) (code : QuotCode Γ₁) : QuotCode Γ₂ :=
  ⟨code.η, code.level, arg code.carrier, arg code.relation⟩

@[simp] theorem map_id (code : QuotCode Γ₁) : code.map id = code := rfl

@[simp] theorem map_map (arg : (Tm_ Γ₁) → Tm_ Γ₂)
    (arg' : (Tm_ Γ₂) → Tm_ Γ₃) (code : QuotCode Γ₁) :
    (code.map arg).map arg' = code.map (arg' ∘ arg) := rfl

@[simp] theorem map_hom_id (code : QuotCode Γ₁) :
    code.map ((Tm E ℓ).map (𝟙 Γ₁).op) = code := by
  simp [map]

theorem map_comp_hom (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) (code : QuotCode Γ₁) :
    code.map ((Tm E ℓ).map (σ₂ ≫ σ₁).op) =
      (code.map ((Tm E ℓ).map σ₁.op)).map ((Tm E ℓ).map σ₂.op) :=
  congrArg code.map (funext fun x => (Tm E ℓ).map_comp_apply σ₁.op σ₂.op x)

end QuotCode

namespace Shape

def map (arg : (Tm_ Γ₁) → Tm_ Γ₂) (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) : Shape Γ₁ → Shape Γ₂
  | .bot => .bot
  | .sort r => .sort r
  | .forallE label a k names ins outs =>
    .forallE (pi label) (map arg pi a) k (fun i => arg (names i))
      (fun i => map arg pi (ins i)) fun i => map arg pi (outs i)
  | .lam k names ins outs =>
    .lam k (fun i => arg (names i)) (fun i => map arg pi (ins i))
      fun i => map arg pi (outs i)
  | .ind code ctorTypes => .ind (code.map arg) fun c => map arg pi (ctorTypes c)
  | .ctor head names fields => .ctor head (fun i => arg (names i)) fun i => map arg pi (fields i)
  | .struct head hstruct fields => .struct head hstruct fun i => map arg pi (fields i)
  | .quot code => .quot (code.map arg)
  | .quotMk η name value => .quotMk η (arg name) (map arg pi value)

end Shape

structure Graph (Γ₁ : CtxCat E ℓ) where
  size : Nat
  names : Fin size → Tm_ Γ₁
  ins : Fin size → Shape Γ₁
  outs : Fin size → Shape Γ₁

namespace Graph

def map (arg : (Tm_ Γ₁) → Tm_ Γ₂) (pi : Ty.Pair Γ₁ → Ty.Pair Γ₂) (g : Graph Γ₁) : Graph Γ₂ :=
  ⟨g.size, fun i => arg (g.names i), fun i => (g.ins i).map arg pi,
    fun i => (g.outs i).map arg pi⟩

def nil : Graph Γ₁ := ⟨0, Fin.elim0, Fin.elim0, Fin.elim0⟩

def single (label : Tm_ Γ₁) (x y : Shape Γ₁) : Graph Γ₁ :=
  ⟨1, fun _ => label, fun _ => x, fun _ => y⟩

def append (f g : Graph Γ₁) : Graph Γ₁ :=
  ⟨f.size + g.size, Fin.append f.names g.names, Fin.append f.ins g.ins, Fin.append f.outs g.outs⟩

@[simp] theorem append_names_left (f g : Graph Γ₁) (i : Fin f.size) :
    (f.append g).names (Fin.castAdd g.size i) = f.names i := Fin.append_left _ _ i

@[simp] theorem append_names_right (f g : Graph Γ₁) (i : Fin g.size) :
    (f.append g).names (Fin.natAdd f.size i) = g.names i := Fin.append_right _ _ i

@[simp] theorem append_ins_left (f g : Graph Γ₁) (i : Fin f.size) :
    (f.append g).ins (Fin.castAdd g.size i) = f.ins i := Fin.append_left _ _ i

@[simp] theorem append_ins_right (f g : Graph Γ₁) (i : Fin g.size) :
    (f.append g).ins (Fin.natAdd f.size i) = g.ins i := Fin.append_right _ _ i

@[simp] theorem append_outs_left (f g : Graph Γ₁) (i : Fin f.size) :
    (f.append g).outs (Fin.castAdd g.size i) = f.outs i := Fin.append_left _ _ i

@[simp] theorem append_outs_right (f g : Graph Γ₁) (i : Fin g.size) :
    (f.append g).outs (Fin.natAdd f.size i) = g.outs i := Fin.append_right _ _ i

end Graph

namespace Shape

@[match_pattern] abbrev pi (label : Ty.Pair Γ₁) (a : Shape Γ₁) (g : Graph Γ₁) : Shape Γ₁ :=
  forallE label a g.size g.names g.ins g.outs

@[match_pattern] abbrev abs (g : Graph Γ₁) : Shape Γ₁ := lam g.size g.names g.ins g.outs

open Opposite

noncomputable abbrev reindexHom (σ : Γ₂ ⟶ Γ₁) : Shape Γ₁ → Shape Γ₂ :=
  map ((Tm E ℓ).map σ.op) ((Ty.pairPresheaf E ℓ).map σ.op)

@[simp] theorem reindexHom_id (a : Shape Γ₁) : a.reindexHom (𝟙 Γ₁) = a := by
  induction a <;> simp_all [reindexHom, map, IndCode.map, QuotCode.map]

theorem reindexHom_comp (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) (a : Shape Γ₁) :
    a.reindexHom (σ₂ ≫ σ₁) = (a.reindexHom σ₁).reindexHom σ₂ := by
  induction a <;> simp_all [reindexHom, map, QuotCode.map]

@[implicit_reducible] noncomputable def presheaf (E : Env ζ) (ℓ : Nat) : (CtxCat E ℓ)ᵒᵖ ⥤ Type where
  obj Γ₁ := Shape Γ₁.unop
  map σ := ↾reindexHom σ.unop
  map_id _ := ConcreteCategory.hom_ext _ _ reindexHom_id
  map_comp σ₁ σ₂ := ConcreteCategory.hom_ext _ _ (reindexHom_comp σ₁.unop σ₂.unop)

end Shape

namespace Graph

open Opposite

noncomputable abbrev reindexHom (σ : Γ₂ ⟶ Γ₁) : Graph Γ₁ → Graph Γ₂ :=
  map ((Tm E ℓ).map σ.op) ((Ty.pairPresheaf E ℓ).map σ.op)

@[simp] theorem reindexHom_id (f : Graph Γ₁) : f.reindexHom (𝟙 Γ₁) = f := by
  have h := Shape.reindexHom_id (Γ₁ := Γ₁)
  simp [Shape.reindexHom] at h
  simp [map, h]

theorem reindexHom_comp (σ₁ : Γ₂ ⟶ Γ₁) (σ₂ : Γ₃ ⟶ Γ₂) (f : Graph Γ₁) :
    f.reindexHom (σ₂ ≫ σ₁) = (f.reindexHom σ₁).reindexHom σ₂ := by
  have h := Shape.reindexHom_comp σ₁ σ₂
  simp [Shape.reindexHom] at h
  simp [map, h]

end Graph

end Metalean
