/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.NaturalModel.Prop
public import Metalean.TypeTheory.NaturalModel.Telescope

@[expose] public noncomputable section

namespace Metalean.TypeTheory.NaturalModel

open CategoryTheory Opposite Limits

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {C : Type u} [SmallCategory C] {Ty Tm : Cᵒᵖ ⥤ Type u} [ℳ : NaturalModel Ty Tm]
  [HasPi Ty Tm] {n : Nat} {Γ : C}

variable (Ty n Γ) in
structure IndSpec where
  index (s : Fin n) : Tele Ty Γ
  nctors (s : Fin n) : Nat
  field {s : Fin n} (c : Fin (nctors s)) : Tele Ty Γ
  target {s : Fin n} (c : Fin (nctors s)) :
    extTele (field c) ⟶ extTele (index s)
  target_disp {s : Fin n} (c : Fin (nctors s)) :
    target c ≫ dispTele (index s) = dispTele (field c)
  nrec {s : Fin n} (c : Fin (nctors s)) : Nat
  arity {s : Fin n} (c : Fin (nctors s)) (k : Fin (nrec c)) : Tele Ty (extTele (field c))
  recSort {s : Fin n} (c : Fin (nctors s)) (k : Fin (nrec c)) : Fin n
  recIndex {s : Fin n} (c : Fin (nctors s)) (k : Fin (nrec c)) :
    extTele (arity c k) ⟶ extTele (index (recSort c k))
  recIndex_disp {s : Fin n} (c : Fin (nctors s)) (k : Fin (nrec c)) :
    recIndex c k ≫ dispTele (index (recSort c k)) = dispTele (arity c k) ≫ dispTele (field c)

variable {I : IndSpec Ty n Γ}

def Carrier (I : IndSpec Ty n Γ) :=
  ∀ s : Fin n, y (extTele (I.index s)) ⟶ Ty

def recType (T : Carrier I) {s : Fin n} (c : Fin (I.nctors s)) (k : Fin (I.nrec c)) :
    y (extTele (I.field c)) ⟶ Ty :=
  piTele (I.arity c k) (y (I.recIndex c k) ≫ T (I.recSort c k))

def recTele (T : Carrier I) {s : Fin n} (c : Fin (I.nctors s)) : Tele Ty (extTele (I.field c)) :=
  Tele.ofFam (𝟙 _) (I.nrec c) (recType T c)

def recArgSect (T : Carrier I) {s : Fin n} (c : Fin (I.nctors s)) (k : Fin (I.nrec c)) :
    Sect (y (dispTele (recTele T c)) ≫ recType T c k) :=
  Sect.convert (by simp; rfl)
    (Sect.ofTerm _ (Tele.var (𝟙 _) (I.nrec c) (recType T c) k)
      (Tele.var_typing (𝟙 _) (I.nrec c) (recType T c) k))

def recArg (T : Carrier I) {s : Fin n} (c : Fin (I.nctors s)) (k : Fin (I.nrec c)) :
    extTele ((I.arity c k).subst (dispTele (recTele T c))) ⟶ ext (T (I.recSort c k)) :=
  (Sect.convert (by simp)
      (appTele _ _ (Sect.convert (subst_piTele _ _ _).symm (recArgSect T c k)))).hom ≫
    extMap (Tele.extMap (dispTele (recTele T c)) (I.arity c k) ≫ I.recIndex c k)
      (T (I.recSort c k))

variable (I) in
structure Algebra where
  carrier : Carrier I
  intro {s : Fin n} (c : Fin (I.nctors s)) :
    extTele (recTele carrier c) ⟶ ext (carrier s)
  intro_disp {s : Fin n} (c : Fin (I.nctors s)) :
    intro c ≫ disp (carrier s) = dispTele (recTele carrier c) ≫ I.target c

def Motive (α : Algebra I) :=
  ∀ t : Fin n, y (ext (α.carrier t)) ⟶ Ty

def ihType (α : Algebra I) (M : Motive α) {s : Fin n} (c : Fin (I.nctors s))
    (k : Fin (I.nrec c)) : y (extTele (recTele α.carrier c)) ⟶ Ty :=
  piTele ((I.arity c k).subst (dispTele (recTele α.carrier c)))
    (y (recArg α.carrier c k) ≫ M (I.recSort c k))

def ihTele (α : Algebra I) (M : Motive α) {s : Fin n} (c : Fin (I.nctors s)) :
    Tele Ty (extTele (recTele α.carrier c)) :=
  Tele.ofFam (𝟙 _) (I.nrec c) (ihType α M c)

abbrev Method (α : Algebra I) (M : Motive α) {s : Fin n} (c : Fin (I.nctors s)) :=
  Sect (y (dispTele (ihTele α M c) ≫ α.intro c) ≫ M s)

def ihSect (α : Algebra I) (M : Motive α) (elim : ∀ t : Fin n, Sect (M t)) {s : Fin n}
    (c : Fin (I.nctors s)) : TeleSect (ihTele α M c) :=
  TeleSect.ofFam (𝟙 _) (I.nrec c) (ihType α M c) fun k =>
    Sect.convert (by simp; rfl)
      (lamTele _ _ (Sect.pullbackAlong (recArg α.carrier c k) (elim (I.recSort c k))))

abbrev Iota (α : Algebra I) (M : Motive α) (elim : ∀ t : Fin n, Sect (M t)) {s : Fin n}
    (c : Fin (I.nctors s)) (method : Method α M c) : Prop :=
  (ihSect α M elim c).hom ≫ method.hom ≫ extMap (dispTele (ihTele α M c) ≫ α.intro c) (M s) =
    α.intro c ≫ (elim s).hom

class HasLargeElim (α : Algebra I) where
  elim (M : Motive α) (method : ∀ {s : Fin n} (c : Fin (I.nctors s)), Method α M c) (t : Fin n) :
    Sect (M t)
  iota (M : Motive α) (method : ∀ {s : Fin n} (c : Fin (I.nctors s)), Method α M c) {s : Fin n}
    (c : Fin (I.nctors s)) :
    Iota α M (elim M method) c (method c)
  unique (M : Motive α) (method : ∀ {s : Fin n} (c : Fin (I.nctors s)), Method α M c)
    (r : ∀ t : Fin n, Sect (M t)) :
    (∀ {s : Fin n} (c : Fin (I.nctors s)), Iota α M r c (method c)) →
    ∀ t : Fin n, r t = elim M method t

class HasSmallElim (α : Algebra I) where
  elim (M : Motive α) (hM : ∀ t : Fin n, IsProp (M t))
    (method : ∀ {s : Fin n} (c : Fin (I.nctors s)), Method α M c) (t : Fin n) :
    Sect (M t)
  iota (M : Motive α) (hM : ∀ t : Fin n, IsProp (M t))
    (method : ∀ {s : Fin n} (c : Fin (I.nctors s)), Method α M c) {s : Fin n}
    (c : Fin (I.nctors s)) :
    Iota α M (elim M hM method) c (method c)

class HasSingletonElim (α : Algebra I) : Prop where
  prop_carrier (s : Fin n) : IsProp (α.carrier s)
  intro_mono {s : Fin n} (c : Fin (I.nctors s)) : Mono (α.intro c)
  intro_jointly_epi {s : Fin n} {Θ : C} (u v : ext (α.carrier s) ⟶ Θ) :
    (∀ c : Fin (I.nctors s), α.intro c ≫ u = α.intro c ≫ v) → u = v

class HasEta (α : Algebra I) {s : Fin n} (c : Fin (I.nctors s)) : Prop where
  intro_isIso : IsIso (α.intro c)

end Metalean.TypeTheory.NaturalModel
