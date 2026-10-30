/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.SemanticTelescope
public import Metalean.SetTheory.ZFC.Erasure
public import Metalean.SetTheory.ZFC.Coding
import Metalean.Data.Fin

@[expose] public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {n b : Nat} {block block₁ block₂ motive graph graph₁ graph₂ : ZFSet}

noncomputable def recFieldSet
    (Δ : SemTele n b) (index : Dom b) (block : ZFSet) : Dom n :=
  Δ.pi fun γ => fibreOp block (index γ)

noncomputable def typedRecFieldSet (Δ : SemTele n b) (index : Dom b)
    (block : ZFSet) (level : Nat) : Dom n :=
  Δ.pi fun γ => propSet level (fibreOp block (index γ))

noncomputable def typedRecFieldSetDep (Δ : SemTele n b) (index : Dom b)
    (block : Dom n) (level : Nat) : Dom n :=
  Δ.pi fun γ => propSet level
    (fibreOp (block fun field => γ (field.castLE Δ.le)) (index γ))

@[simp] theorem typedRecFieldSetDep_apply (Δ : SemTele n b) (index : Dom b)
    (block : Dom n) (level : Nat) (γ : Slots n) :
    typedRecFieldSetDep Δ index block level γ =
      typedRecFieldSet Δ index (block γ) level γ :=
  Δ.pi_base (fun base final =>
    propSet level (fibreOp (block base) (index final))) γ

noncomputable def recoverRecField (Δ : SemTele n b) (index : Dom b)
    (block : ZFSet) (level : Nat) (γ : Slots n) (value : ZFSet) : ZFSet :=
  Δ.lamAt
    (fun final value => propGet level (fibreOp block (index final)) value)
    γ value

theorem recoverRecField_apps {k : Nat} {Δ : SemTele n (n + k)} {index : Dom (n + k)}
    {block value : ZFSet} {level : Nat} {γ : Slots n} {final : Slots (n + k)}
    (hfinal : final ∈ Reachable {γ} Δ) :
    Aczel.apps (recoverRecField Δ index block level γ value)
        (fun f => final (Fin.natAdd n f)) =
      propGet level (fibreOp block (index final))
        (Aczel.apps value (fun f => final (Fin.natAdd n f))) := by
  simpa [recoverRecField, SemTele.app_eq_apps] using
    (Reachable.app_lamAt (leaf := fun final value => propGet level (fibreOp block (index final)) value)
      (fn := value) hfinal)

noncomputable def eraseRecField (Δ : SemTele n b) (level : Nat)
    (γ : Slots n) (value : ZFSet) : ZFSet :=
  Δ.lamAt (fun _ value => propVal level value) γ value

theorem eraseRecField_mem (Δ : SemTele n b) (index : Dom b)
    {block : ZFSet} {level : Nat} {γ : Slots n} {value : ZFSet}
    (hfield : value ∈ recFieldSet Δ index block γ) :
    eraseRecField Δ level γ value ∈
      typedRecFieldSet Δ index block level γ := by
  have h := Δ.lamAt_mem_piAt
    (domain := fun final => fibreOp block (index final))
    (cod := fun final _ => propSet level (fibreOp block (index final)))
    (fun _ _ hvalue => propVal_mem_propSet hvalue) γ value hfield
  exact h

theorem recoverRecField_mem (Δ : SemTele n b) (index : Dom b)
    {block : ZFSet} {level : Nat} {γ : Slots n} {value : ZFSet}
    (hfield : value ∈ typedRecFieldSet Δ index block level γ) :
    recoverRecField Δ index block level γ value ∈
      recFieldSet Δ index block γ := by
  have h := Δ.lamAt_mem_piAt
    (domain := fun final => propSet level (fibreOp block (index final)))
    (cod := fun final _ => fibreOp block (index final))
    (fun _ _ hvalue => propGet_mem hvalue) γ value hfield
  exact h

theorem eraseRecField_recoverRecField {b level : Nat}
    (tele : SemTele n b) (index : Dom b) (block : ZFSet)
    (γ : Slots n) (value : ZFSet)
    (hfield : value ∈ typedRecFieldSet tele index block level γ) :
    eraseRecField tele level γ
        (recoverRecField tele index block level γ value) = value := by
  calc
    _ = _ := tele.lamAt_comp _ _ γ value
    _ = _ := tele.lamAt_congr (fun _ _ => propVal_propGet) γ value hfield
    _ = value := tele.lamAt_id
      (fun final => propSet level (fibreOp block (index final)))
      γ value hfield

theorem recoverRecField_of_ne_zero {level : Nat} (hlevel : level ≠ 0)
    (Δ : SemTele n b) (index : Dom b) (block : ZFSet)
    (γ : Slots n) (value : ZFSet)
    (hfield : value ∈ recFieldSet Δ index block γ) :
    recoverRecField Δ index block level γ value = value := by
  unfold recoverRecField
  have hcongr := Δ.lamAt_congr
    (fun final value _ => propGet_of_ne_zero hlevel (fibreOp block (index final)) value)
    γ value hfield
  rw [hcongr]
  exact Δ.lamAt_id (fun final => fibreOp block (index final)) γ value hfield

theorem eraseRecField_of_ne_zero {level : Nat} (hlevel : level ≠ 0)
    (Δ : SemTele n b) (index : Dom b) (block : ZFSet)
    (γ : Slots n) (value : ZFSet)
    (hfield : value ∈ recFieldSet Δ index block γ) :
    eraseRecField Δ level γ value = value := by
  unfold eraseRecField
  have hcongr := Δ.lamAt_congr
    (leaf := fun _ => propVal level)
    (leaf' := fun _ => id)
    (by simp [propVal, hlevel]) γ value hfield
  rw [hcongr]
  exact Δ.lamAt_id (fun final => fibreOp block (index final))
    γ value hfield

theorem eraseRecField_zero_eq (Δ : SemTele n b) (leftIndex rightIndex : Dom b)
    (leftBlock rightBlock : ZFSet) (γ : Slots n)
    {left right : ZFSet}
    (hleft : left ∈ recFieldSet Δ leftIndex leftBlock γ)
    (hright : right ∈ recFieldSet Δ rightIndex rightBlock γ) :
    eraseRecField Δ 0 γ left = eraseRecField Δ 0 γ right :=
  Δ.lamAt_eq_of_mem (hleft := hleft) (hright := hright) <| by simp

theorem recFieldSet_mono (Δ : SemTele n b) (index : Dom b) (h : block₁ ⊆ block₂)
    (γ : Slots n) : recFieldSet Δ index block₁ γ ⊆ recFieldSet Δ index block₂ γ :=
  Δ.pi_mono_cod (fun s => fibre_mono h (index s)) γ

noncomputable def ihType (Δ : SemTele n b) (index : Dom b) (motive : ZFSet) : DomAt n :=
  Δ.piAt fun γ value => fibreOp motive [zf|($(index γ), value)]

noncomputable def recMap (Δ : SemTele n b) (index : Dom b) (graph : ZFSet) : DomAt n :=
  Δ.lamAt fun γ value => app graph [zf|($(index γ), value)]

theorem recMap_congr (Δ : SemTele n b) (index : Dom b)
    (h : ∀ value ∈ block, app graph₁ value = app graph₂ value) (γ : Slots n) (value : ZFSet)
    (hfield : value ∈ recFieldSet Δ index block γ) :
    recMap Δ index graph₁ γ value = recMap Δ index graph₂ γ value := by
  refine SemTele.lamAt_congr Δ ?_ γ value hfield
  exact fun _ _ hvalue => h _ (mem_fibre.mp hvalue)

theorem recMap_mem (Δ : SemTele n b) (index : Dom b)
    (hgraph : ∀ value ∈ block, app graph value ∈ fibreOp motive value) (γ : Slots n)
    (value : ZFSet) (hfield : value ∈ recFieldSet Δ index block γ) :
    recMap Δ index graph γ value ∈ ihType Δ index motive γ value := by
  refine Δ.lamAt_mem_piAt ?_ γ value hfield
  exact fun _ _ hvalue => hgraph _ (mem_fibre.mp hvalue)

structure CtorRecCode (n : Nat) : Type (u + 1) where
  arity : Nat
  tele : SemTele n (n + arity)
  index : Dom (n + arity)

structure CtorCode (n : Nat) : Type (u + 1) where
  nfields : Nat
  nrecFields : Nat
  ordinary : SemTele n (n + nfields)
  recursive : Fin nrecFields → CtorRecCode (n + nfields)
  target : Dom (n + nfields)

namespace CtorCode

noncomputable def argSet (block : ZFSet) (code : CtorCode n) : Dom n :=
  code.ordinary.sigma (fun final => tupleSet fun f =>
    recFieldSet (code.recursive f).tele (code.recursive f).index block final)

structure Support (code : CtorCode.{u} n) (γ : Slots.{u} n) : Type (u + 1) where
  ordinary : Reachable {γ} code.ordinary
  field : Fin code.nrecFields
  recursive : Reachable {ordinary.1} (code.recursive field).tele

private def Support.equiv (code : CtorCode.{u} n) (γ : Slots.{u} n) :
    code.Support γ ≃ (final : Reachable {γ} code.ordinary) ×
      (f : Fin code.nrecFields) × Reachable {final.1} (code.recursive f).tele where
  toFun p := ⟨p.ordinary, p.field, p.recursive⟩
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance support_small (code : CtorCode.{u} n) (γ : Slots.{u} n) : Small.{u} (code.Support γ) :=
  small_of_injective (Support.equiv code γ).injective

theorem Support.cardinalMk (code : CtorCode.{u} n) (γ : Slots.{u} n) :
    Cardinal.mk (code.Support γ) = Cardinal.sum (fun final : Reachable {γ} code.ordinary =>
      Cardinal.sum fun f : Fin code.nrecFields =>
        Cardinal.mk (Reachable {final.1} (code.recursive f).tele)) := by
  rw [Cardinal.mk_congr (Support.equiv code γ)]
  simp [Cardinal.mk_sigma]

noncomputable def readSupport (code : CtorCode n) (γ : Slots n) (vargs : ZFSet)
    (point : code.Support γ) : ZFSet :=
  let f := code.recursive point.field
  pair (f.index point.recursive.1) (SemTele.app f.tele point.recursive.1
    (tupleValues code.nrecFields (code.ordinary.tail vargs) point.field))

variable {blockW : ZFSet} {γ : Slots n} {vargs : ZFSet}

theorem argSet_mono (h : block₁ ⊆ block₂) (code : CtorCode n) (γ : Slots n) :
    code.argSet block₁ γ ⊆ code.argSet block₂ γ := by
  apply code.ordinary.sigma_mono_cod
  intro final value hvalue
  obtain ⟨hfields, heq⟩ := mem_tupleSet.mp hvalue
  exact mem_tupleSet.mpr ⟨fun f => recFieldSet_mono _ _ h _ (hfields f), heq⟩

theorem argSet_inter (hw : ∀ value ∈ block₁, value ∈ block₂ → value ∈ blockW)
    (code : CtorCode n) (γ : Slots n) (vargs : ZFSet)
    (h₁ : vargs ∈ code.argSet block₁ γ) (h₂ : vargs ∈ code.argSet block₂ γ) :
    vargs ∈ code.argSet blockW γ := by
  refine code.ordinary.sigma_inter_cod (fun final value h₁ h₂ => ?_) γ h₁ h₂
  obtain ⟨h₁, heq⟩ := mem_tupleSet.mp h₁
  have h₂ := (mem_tupleSet.mp h₂).1
  exact mem_tupleSet.mpr ⟨fun f => (code.recursive f).tele.pi_inter_cod
    (fun _ _ hv₁ hv₂ => mem_fibre.mpr (hw _ (mem_fibre.mp hv₁) (mem_fibre.mp hv₂)))
    final _ (h₁ f) (h₂ f), heq⟩

theorem argSet_mem_of_support
    (code : CtorCode n) (γ : Slots n) (vargs : ZFSet)
    (hargs : vargs ∈ code.argSet block₁ γ)
    (hsupport : ∀ point : code.Support γ,
      code.readSupport γ vargs point ∈ block₁ → code.readSupport γ vargs point ∈ block₂) :
    vargs ∈ code.argSet block₂ γ := by
  obtain ⟨hfinal, htail, hpack⟩ := SemTele.mem_sigma.mp hargs
  obtain ⟨hfields, htuple⟩ := mem_tupleSet.mp htail
  refine SemTele.mem_sigma.mpr ⟨hfinal, mem_tupleSet.mpr ⟨fun f => ?_, htuple⟩, hpack⟩
  refine ((code.recursive f).tele.pi_mem_iff _ _ (hfields f)).mpr fun final hreach => ?_
  exact mem_fibre.mpr (hsupport ⟨⟨_, hfinal⟩, f, ⟨final, hreach⟩⟩
    (mem_fibre.mp (Reachable.app_mem hreach (hfields f))))

noncomputable def applyMinor (level : Nat) (graph : ZFSet) (code : CtorCode n)
    (γ : Slots n) (minor vargs : ZFSet) : ZFSet :=
  let final := code.ordinary.values γ vargs
  let fields := tupleValues code.nrecFields (code.ordinary.tail vargs)
  [zf|$(SemTele.app code.ordinary final minor)
    $(fun f => eraseRecField (code.recursive f).tele level final (fields f))...
    $(fun f => recMap (code.recursive f).tele (code.recursive f).index graph final (fields f))...]

theorem applyMinor_congr {level : Nat} (h : ∀ value ∈ block, app graph₁ value = app graph₂ value)
    (code : CtorCode n) (γ : Slots n) (minor vargs : ZFSet)
    (hargs : vargs ∈ code.argSet block γ) :
    code.applyMinor level graph₁ γ minor vargs = code.applyMinor level graph₂ γ minor vargs := by
  dsimp only [applyMinor]
  congr 1
  funext f
  exact recMap_congr _ _ h _ _ ((mem_tupleSet.mp (SemTele.mem_sigma.mp hargs).2.1).1 f)

noncomputable def targetIndex (code : CtorCode n) (γ : Slots n) (vargs : ZFSet) : ZFSet :=
  code.target (code.ordinary.values γ vargs)

end CtorCode

end Metalean
