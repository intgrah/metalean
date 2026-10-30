/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Telescope
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

theorem ihType_eraseRecField {level : Nat} {motive : ZFSet} (Δ : SemTele n b) (index : Dom b)
    (h : ∀ key value, pair key value ∈ block →
      fibreOp motive (pair key value) = fibreOp motive (pair key (propVal level value)))
    (γ : Slots n) (raw : ZFSet) (hraw : raw ∈ recFieldSet Δ index block γ) :
    ihType Δ index motive γ raw = ihType Δ index motive γ (eraseRecField Δ level γ raw) := by
  apply Δ.piAt_lamAt
    (domain := fun final => fibreOp block (index final))
    (map := fun _ value => propVal level value) _ _ ?_ γ raw hraw
  exact fun final value hvalue => h _ _ (mem_fibre.mp hvalue)

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

noncomputable def minorType (level : Nat) (block motive : ZFSet) (code : CtorCode n)
    (leaf : Slots (n + code.nfields) → Slots code.nrecFields → ZFSet) : Dom n :=
  code.ordinary.pi fun final =>
    Aczel.pis (fun f => typedRecFieldSet (code.recursive f).tele
      (code.recursive f).index block level final) fun fields =>
      Aczel.pis (fun f => ihType (code.recursive f).tele (code.recursive f).index
        motive final (fields f)) fun _ => leaf final fields

theorem applyMinor_mem {code : CtorCode n} {level : Nat} {motive : ZFSet}
    {leaf : Slots (n + code.nfields) → Slots code.nrecFields → ZFSet}
    {γ : Slots n} {minor graph vargs : ZFSet}
    (hminor : minor ∈ code.minorType level block₂ motive leaf γ)
    (hblock : block₁ ⊆ block₂)
    (hgraph : ∀ value ∈ block₁, app graph value ∈ fibreOp motive value)
    (hmotive : ∀ key value, pair key value ∈ block₂ →
      fibreOp motive (pair key value) = fibreOp motive (pair key (propVal level value)))
    (hargs : vargs ∈ code.argSet block₁ γ) :
    code.applyMinor level graph γ minor vargs ∈ leaf (code.ordinary.values γ vargs)
      (fun f => eraseRecField (code.recursive f).tele level (code.ordinary.values γ vargs)
        (tupleValues code.nrecFields (code.ordinary.tail vargs) f)) := by
  obtain ⟨hfinal, htail, _⟩ := SemTele.mem_sigma.mp hargs
  have hfields := (mem_tupleSet.mp htail).1
  have hraw (f) := recFieldSet_mono (code.recursive f).tele (code.recursive f).index
    hblock _ (hfields f)
  have hminor := Reachable.app_mem hfinal hminor
  have hminor := Aczel.apps_mem_pis hminor (fun f => eraseRecField_mem _ _ (hraw f))
  exact Aczel.apps_mem_pis hminor fun f => by
    rw [← ihType_eraseRecField _ _ hmotive _ _ (hraw f)]
    exact recMap_mem _ _ hgraph _ _ (hfields f)

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

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

namespace CtorCode

variable {n : Nat} {code : CtorCode n} {block block₁ block₂ : ZFSet}

noncomputable def pack (block : ZFSet) (level : Nat) (code : CtorCode n)
    (γ : Slots n) (values : Slots code.nfields) (fields : Slots code.nrecFields) : ZFSet :=
  code.ordinary.pack (Fin.append γ values) (tuple fun f => recoverRecField (code.recursive f).tele
    (code.recursive f).index block level (Fin.append γ values) (fields f))

@[simp] theorem values_pack (code : CtorCode n) (block : ZFSet) (level : Nat)
    (γ : Slots n) (values : Slots code.nfields) (fields : Slots code.nrecFields) :
    code.ordinary.values γ (code.pack block level γ values fields) = Fin.append γ values := by
  have h := code.ordinary.values_pack (Fin.append γ values)
    (tuple fun f => recoverRecField (code.recursive f).tele (code.recursive f).index block level
      (Fin.append γ values) (fields f))
  have hbase : (fun base : Fin n => Fin.append γ values (base.castLE code.ordinary.le)) = γ :=
    funext fun base => Fin.append_left γ values base
  rwa [hbase] at h

theorem pack_mem {reach : Set (Slots n)} {γ : Slots n} {values : Slots code.nfields}
    {fields : Slots code.nrecFields} {level : Nat}
    (hfinal : Fin.append γ values ∈ Reachable reach code.ordinary)
    (hfields : ∀ f, fields f ∈ typedRecFieldSet
      (code.recursive f).tele (code.recursive f).index block level (Fin.append γ values)) :
    code.pack block level γ values fields ∈ code.argSet block γ := by
  have h := SemTele.pack_mem
    (leaf := fun final => tupleSet fun f =>
      recFieldSet (code.recursive f).tele (code.recursive f).index block final)
    hfinal (tuple_mem_tupleSet fun f => recoverRecField_mem _ _ (hfields f))
  have hbase : (fun base : Fin n => Fin.append γ values (base.castLE code.ordinary.le)) = γ :=
    funext fun base => Fin.append_left γ values base
  rw [hbase] at h
  exact h

theorem applyMinor_pack (code : CtorCode n) (block graph : ZFSet) (level : Nat)
    (γ : Slots n) (values : Slots code.nfields) (fields : Slots code.nrecFields)
    (hfields : ∀ f, fields f ∈ typedRecFieldSet
      (code.recursive f).tele (code.recursive f).index block level (Fin.append γ values))
    (minor : ZFSet) :
    code.applyMinor level graph γ minor (code.pack block level γ values fields) =
      [zf|minor values... fields...
        $(fun f => recMap (code.recursive f).tele (code.recursive f).index graph (Fin.append γ values)
          (recoverRecField (code.recursive f).tele (code.recursive f).index block level
            (Fin.append γ values) (fields f)))...] := by
  simp only [applyMinor, values_pack]
  simp only [pack, SemTele.tail_pack, tupleValues_tuple, SemTele.app_eq_apps, Fin.append_right]
  congr 2
  funext f
  exact eraseRecField_recoverRecField _ _ _ _ _ (hfields f)

theorem pack_erase (code : CtorCode n) {γ : Slots n} {vargs : ZFSet}
    (hargs : vargs ∈ code.argSet block γ) (level tag : Nat) :
    propVal level (entryValue tag (code.pack block level γ
      (fun f => code.ordinary.values γ vargs (Fin.natAdd n f))
      (fun f => eraseRecField (code.recursive f).tele level (code.ordinary.values γ vargs)
        (tupleValues code.nrecFields (code.ordinary.tail vargs) f)))) =
      propVal level (entryValue tag vargs) := by
  obtain ⟨_, htail, hpack⟩ := SemTele.mem_sigma.mp hargs
  obtain ⟨hfields, htuple⟩ := mem_tupleSet.mp htail
  cases level with
  | zero => simp
  | succ level =>
    have hvalues : (fun f => recoverRecField (code.recursive f).tele (code.recursive f).index
        block (level + 1) (code.ordinary.values γ vargs)
        (eraseRecField (code.recursive f).tele (level + 1) (code.ordinary.values γ vargs)
          (tupleValues code.nrecFields (code.ordinary.tail vargs) f))) =
        tupleValues code.nrecFields (code.ordinary.tail vargs) := by
      funext f
      rw [eraseRecField_of_ne_zero (Nat.succ_ne_zero level) _ _ _ _ _ (hfields f),
        recoverRecField_of_ne_zero (Nat.succ_ne_zero level) _ _ _ _ _ (hfields f)]
    simp [pack, ← code.ordinary.values_eq_append γ vargs, hvalues, htuple, hpack]

theorem applyMinor_zero_congr (code : CtorCode n)
    {γ : Slots n} {left right graph : ZFSet}
    (hgraph : ∀ key value₁ value₂,
      pair key value₁ ∈ block₁ → pair key value₂ ∈ block₂ →
      app graph (pair key value₁) = app graph (pair key value₂))
    (hleft : left ∈ code.argSet block₁ γ) (hright : right ∈ code.argSet block₂ γ)
    (hordinary : code.ordinary.values γ left = code.ordinary.values γ right)
    (minor : ZFSet) :
    code.applyMinor 0 graph γ minor left = code.applyMinor 0 graph γ minor right := by
  have hl := (mem_tupleSet.mp (SemTele.mem_sigma.mp hleft).2.1).1
  have hr := (mem_tupleSet.mp (SemTele.mem_sigma.mp hright).2.1).1
  rw [hordinary] at hl
  dsimp only [applyMinor]
  rw [hordinary]
  have hfields : (fun f => eraseRecField (code.recursive f).tele 0 (code.ordinary.values γ right)
      (tupleValues code.nrecFields (code.ordinary.tail left) f)) =
      fun f => eraseRecField (code.recursive f).tele 0 (code.ordinary.values γ right)
        (tupleValues code.nrecFields (code.ordinary.tail right) f) :=
    funext fun f => eraseRecField_zero_eq _ _ _ _ _ _ (hl f) (hr f)
  rw [hfields]
  congr 1
  funext f
  apply (code.recursive f).tele.lamAt_ext
  exact fun final hfinal => hgraph _ _ _
    (mem_fibre.mp (Reachable.app_mem hfinal (hl f)))
    (mem_fibre.mp (Reachable.app_mem hfinal (hr f)))

end CtorCode

end Metalean
