/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.QuotientValue
public import Metalean.TypeTheory.NaturalModel.Quotient
public import Metalean.TypeTheory.SetModel.Code

@[expose] public noncomputable section

namespace Metalean.TypeTheory.SetModel

open CategoryTheory Opposite Limits ZFSet NaturalModel

local notation "y" => yoneda.obj
local notation "y" => yoneda.map

universe u

variable {ℓ : Nat} {Γ : ZFSet.{u}}

open scoped Classical in
def level (A : Fam Γ) : Nat :=
  Nat.find A.bound

open scoped Classical in
theorem obj_mem_sort_level (A : Fam Γ) (γ : Γ) : A.obj γ ∈ S_ (level A) :=
  Nat.find_spec A.bound γ

open scoped Classical in
theorem level_le {A : Fam Γ} {n : Nat} (h : ∀ γ : Γ, A.obj γ ∈ S_ n) : level A ≤ n :=
  Nat.find_le h

theorem mem_sort_mono {n m : Nat} (h : n ≤ m) {x : ZFSet.{u}} (hx : x ∈ S_ n) : x ∈ S_ m := by
  match n, m with
  | 0, 0 => exact hx
  | 0, _ + 1 => exact mem_type_of_mem_sort (by omega) hx
  | _ + 1, 0 => omega
  | _ + 1, _ + 1 => exact type_mono (by omega) hx

theorem quotientCarrier_mem_sort_le {n m : Nat} (hnm : n ≤ m) {α r : ZFSet.{u}}
    (hn : α ∈ S_ n) : quotientCarrier n α r ∈ S_ m :=
  mem_sort_mono hnm (quotientCarrier_mem_sort hn)

def wk (A : y Γ ⟶ Ty.{u}) : y (NaturalModel.ext A) ⟶ Ty.{u} :=
  y (NaturalModel.disp A) ≫ A

def secondFam (A : y Γ ⟶ Ty.{u}) : Fam (NaturalModel.ext A) :=
  yonedaEquiv (wk A)

theorem secondFam_eq (A : y Γ ⟶ Ty.{u}) :
    secondFam A = (yonedaEquiv A).subst (NaturalModel.disp A) :=
  yonedaEquiv_comp _ A

theorem obj_secondFam (A : y Γ ⟶ Ty.{u}) (γ : Γ) (a : (yonedaEquiv A).obj γ) :
    (secondFam A).obj (toExt A (point (yonedaEquiv A) γ a)) = (yonedaEquiv A).obj γ := by
  rw [secondFam_eq]
  exact congrArg (yonedaEquiv A).obj ((congrFun (toExt_disp A) _).trans (disp_point _ γ a))

def pt (A : y Γ ⟶ Ty.{u}) (γ : Γ) (a₁ a₂ : (yonedaEquiv A).obj γ) :
    (NaturalModel.ext (wk A) : ZFSet.{u}) :=
  toExt (wk A)
    (point (secondFam A) (toExt A (point (yonedaEquiv A) γ a₁))
      ⟨a₂, (obj_secondFam A γ a₁).symm ▸ a₂.2⟩)

def relValue (A : y Γ ⟶ Ty.{u})
    (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u})
    (γ : Γ) (a₁ a₂ : (yonedaEquiv A).obj γ) : ZFSet.{u} :=
  (yonedaEquiv R).obj (pt A γ a₁ a₂)

def relFn (A : y Γ ⟶ Ty.{u})
    (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u}) (γ : Γ) : ZFSet.{u} :=
  Aczel.lam ((yonedaEquiv A).obj γ) (ZFSet.app (graph ((yonedaEquiv A).obj γ) fun a₁ =>
    Aczel.lam ((yonedaEquiv A).obj γ) (ZFSet.app (graph ((yonedaEquiv A).obj γ) fun a₂ =>
      relValue A R γ a₁ a₂))))

theorem app_relFn (A : y Γ ⟶ Ty.{u})
    (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u})
    (γ : Γ) (a₁ a₂ : (yonedaEquiv A).obj γ) :
    Aczel.app (Aczel.app (relFn A R γ) a₁) a₂ = relValue A R γ a₁ a₂ := by
  rw [relFn, Aczel.app_lam a₁.2, app_graph a₁.2, Aczel.app_lam a₂.2, app_graph a₂.2]

def quotFam (A : y Γ ⟶ Ty.{u})
    (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u}) : Fam Γ where
  obj γ := quotientCarrier (level (yonedaEquiv A)) ((yonedaEquiv A).obj γ) (relFn A R γ)
  bound := ⟨level (yonedaEquiv A), fun γ => quotientCarrier_mem_sort (obj_mem_sort_level _ γ)⟩

theorem isSort_quotFam (A : y Γ ⟶ Ty.{u})
    (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u}) {v : Level ℓ}
    (hv : HasSorts.IsSort A v) : HasSorts.IsSort (ofFam (quotFam A R)) v := by
  rw [← ofFam_yonedaEquiv A] at hv
  exact isSort_ofFam_iff.mpr fun γ =>
    quotientCarrier_mem_sort_le (level_le (isSort_ofFam_iff.mp hv)) (obj_mem_sort_level _ γ)

def quotCode (A : y Γ ⟶ Ty.{u}) (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u}) : y Γ ⟶ Ty.{u} :=
  ofFam (quotFam A R)

def toQuotFam (A : y Γ ⟶ Ty.{u}) (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u}) :
    ext (yonedaEquiv A) ⟶ ext (quotFam A R) :=
  pairing (quotFam A R) (disp (yonedaEquiv A))
    (fun z => quotientMk (level (yonedaEquiv A)) ((yonedaEquiv A).obj (disp (yonedaEquiv A) z))
      (relFn A R (disp (yonedaEquiv A) z)) (ZFSet.snd z))
    fun z => quotientMk_mem (snd_mem_disp _ z)

theorem toQuotFam_point (A : y Γ ⟶ Ty.{u}) (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u})
    (γ : Γ) (x : (yonedaEquiv A).obj γ) :
    (toQuotFam A R (point (yonedaEquiv A) γ x) : ZFSet.{u}) =
      ZFSet.pair γ
        (quotientMk (level (yonedaEquiv A)) ((yonedaEquiv A).obj γ) (relFn A R γ) x) := by
  change ZFSet.pair (disp (yonedaEquiv A) (point (yonedaEquiv A) γ x))
    (quotientMk (level (yonedaEquiv A))
      ((yonedaEquiv A).obj (disp (yonedaEquiv A) (point (yonedaEquiv A) γ x)))
      (relFn A R (disp (yonedaEquiv A) (point (yonedaEquiv A) γ x)))
      (ZFSet.snd (point (yonedaEquiv A) γ x))) = _
  have hdisp : disp (yonedaEquiv A) (point (yonedaEquiv A) γ x) = γ := disp_point _ _ _
  have hsnd : ZFSet.snd (point (yonedaEquiv A) γ x) = (x : ZFSet.{u}) := snd_point _ _ _
  rw [hdisp, hsnd]

theorem surjective_toQuotFam (A : y Γ ⟶ Ty.{u}) (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u}) :
    Function.Surjective (toQuotFam A R) := by
  intro w
  obtain ⟨a, ha, hc⟩ := quotientCarrier_representation
    (obj_mem_sort_level (yonedaEquiv A) (disp (quotFam A R) w)) (snd_mem_disp (quotFam A R) w)
  refine ⟨point (yonedaEquiv A) (disp (quotFam A R) w) ⟨a, ha⟩, Subtype.ext ?_⟩
  rw [toQuotFam_point, ← hc]
  exact pair_fst_snd_of_mem_ext w.2

theorem epi_of_surjective {Γ Δ : ZFSet.{u}} {f : Γ ⟶ Δ} (h : Function.Surjective f) : Epi f :=
  ⟨fun g₁ g₂ hg => funext fun δ => by
    obtain ⟨γ, rfl⟩ := h δ
    exact congrFun hg γ⟩

instance isIso_fromExt (A : y Γ ⟶ Ty.{u}) : IsIso (fromExt A) :=
  ⟨toExt A, fromExt_toExt A, toExt_fromExt A⟩

def toQuotHom (A : y Γ ⟶ Ty.{u}) (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u}) :
    NaturalModel.ext A ⟶ NaturalModel.ext (quotCode A R) :=
  fromExt A ≫ toQuotFam A R ≫ toExt (quotCode A R)

theorem toQuotHom_disp (A : y Γ ⟶ Ty.{u}) (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u}) :
    toQuotHom A R ≫ NaturalModel.disp (quotCode A R) = NaturalModel.disp A := by
  funext z
  refine ((congrFun (toExt_disp (quotCode A R)) (toQuotFam A R (fromExt A z))).trans ?_)
  exact (disp_pairing _ _ _ _ _).trans (disp_pairing _ _ _ _ z)

instance epi_toQuotHom (A : y Γ ⟶ Ty.{u}) (R : y (NaturalModel.ext (wk A)) ⟶ Ty.{u}) :
    Epi (toQuotHom A R) :=
  have h₁ : Epi (toQuotFam A R) := epi_of_surjective (surjective_toQuotFam A R)
  have h₂ : Epi (toExt (quotCode A R)) := IsIso.epi_of_iso _
  have h₃ : Epi (fromExt A) := IsIso.epi_of_iso _
  @epi_comp _ _ _ _ _ (fromExt A) h₃ _
    (@epi_comp _ _ _ _ _ (toQuotFam A R) h₁ (toExt (quotCode A R)) h₂)

end Metalean.TypeTheory.SetModel
