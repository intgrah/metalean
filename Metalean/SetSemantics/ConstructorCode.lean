/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.SemanticTelescope
public import Metalean.SetTheory.ZFC.Erasure
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

inductive CtorCode : Nat → Type (u + 1)
  | target {n : Nat} (index : Dom n) : CtorCode n
  | arg {n : Nat} (domain : Dom n)
    (rest : CtorCode (n + 1)) :
    CtorCode n
  | recArg {n b : Nat} (tele : SemTele n b)
    (index : Dom b) (rest : CtorCode n) :
    CtorCode n

structure CtorRecCode (n arity : Nat) : Type (u + 1) where
  tele : SemTele n (n + arity)
  index : Dom (n + arity)

abbrev CtorRecCode.Packed (n : Nat) := Σ arity, CtorRecCode n arity

namespace SemTele

noncomputable def tail {b : Nat} (vargs : ZFSet) : SemTele n b → ZFSet
  | .nil => vargs
  | .snoc Δ _ => snd (tail vargs Δ)

noncomputable def values {b : Nat} (γ : Slots n) (vargs : ZFSet) : SemTele n b → Slots b
  | .nil => γ
  | .snoc Δ _ => Fin.snoc (values γ vargs Δ) (fst (tail vargs Δ))

theorem values_base (Δ : SemTele n b) (γ : Slots n) (vargs : ZFSet) (base : Fin n) :
    Δ.values γ vargs (base.castLE Δ.le) = γ base := by
  induction Δ with
  | nil => rfl
  | snoc Δ domain ih =>
    exact (Fin.snoc_castSucc (α := fun _ => ZFSet) (p := values γ vargs Δ)
      (i := base.castLE Δ.le) ..).trans ih

theorem values_eq_append {count : Nat} (Δ : SemTele n (n + count)) (γ : Slots n)
    (vargs : ZFSet) :
    Δ.values γ vargs = Fin.append γ fun f => Δ.values γ vargs (Fin.natAdd n f) :=
  Fin.append_castAdd_natAdd.symm.trans
    (congrArg (Fin.append · _) (funext (Δ.values_base γ vargs)))

end SemTele

namespace CtorCode

def prependOrdinary (Δ : SemTele n b) (rest : CtorCode b) : CtorCode n :=
  Tele.foldr CtorCode.arg rest Δ

def prependRecursive {n : Nat} :
    (count : Nat) → (Fin count → CtorRecCode.Packed n) →
      CtorCode n → CtorCode n
  | 0, _, rest => rest
  | count + 1, descriptors, rest =>
    let head := descriptors 0
    .recArg head.2.tele head.2.index
      (prependRecursive count (fun field => descriptors field.succ) rest)

noncomputable def Support {n : Nat} : CtorCode.{u} n → Slots.{u} n → Type (u + 1)
  | .target _ => fun _ => PEmpty
  | .arg domain rest => fun γ => (value : domain γ) × rest.Support (γ.snoc value.1)
  | .recArg tele _ rest => fun γ => Reachable {γ} tele ⊕ rest.Support γ

instance support_small (code : CtorCode.{u} n) (γ : Slots.{u} n) : Small.{u} (code.Support γ) := by
  induction code with
  | target => change Small.{u} PEmpty; infer_instance
  | arg domain rest ih =>
    have := ih
    exact small_sigma _
  | recArg tele index rest ih =>
    have := ih
    exact small_sum

noncomputable def readSupport {n : Nat} (code : CtorCode n) :
    (γ : Slots n) → ZFSet → code.Support γ → ZFSet :=
  code.rec
    (fun _ _ _ point => point.elim)
    (fun _ _ read γ vargs point =>
      read (γ.snoc point.1.1) (snd vargs) point.2)
    fun tele index _ read γ vargs point =>
      point.elim
        (fun final => pair (index final.1) (SemTele.app tele final.1 (fst vargs)))
        (read γ (snd vargs))

noncomputable def argSet (block : ZFSet) {n : Nat} :
    CtorCode n → Dom n
  | .target _ => fun _ => verum
  | .arg domain rest => fun γ =>
    σ (domain γ) (map (fun value => rest.argSet block (γ.snoc value)) (domain γ))
  | .recArg tele index rest => fun γ =>
    let domain := recFieldSet tele index block γ
    σ domain (map (fun _ => rest.argSet block γ) domain)

variable {blockW : ZFSet} {γ : Slots n} {vargs : ZFSet}

theorem argSet_mono (h : block₁ ⊆ block₂) (code : CtorCode n) (γ : Slots n) :
    argSet block₁ code γ ⊆ argSet block₂ code γ := by
  induction code with
  | target => exact subset_refl _
  | arg domain rest ih =>
    refine sigma_mono (subset_refl _) fun value hvalue => ?_
    rw [app_map hvalue, app_map hvalue]
    exact ih _
  | recArg tele index rest ih =>
    have hdomain := recFieldSet_mono tele index h γ
    refine sigma_mono hdomain fun value hvalue => ?_
    rw [app_map hvalue, app_map (hdomain hvalue)]
    exact ih _

theorem argSet_inter (hw : ∀ value ∈ block₁, value ∈ block₂ → value ∈ blockW)
    (code : CtorCode n) (γ : Slots n) (vargs : ZFSet)
    (h : vargs ∈ argSet block₁ code γ) (h' : vargs ∈ argSet block₂ code γ) :
    vargs ∈ argSet blockW code γ := by
  induction code generalizing vargs with
  | target => exact h
  | arg domain rest ih =>
    obtain ⟨value, hvalue, tail, htail, rfl⟩ := mem_sigma_map.mp h
    have ⟨_, hvalue', tail', htail', heq⟩ := mem_sigma_map.mp h'
    have ⟨rfl, rfl⟩ := pair_inj.mp heq
    exact pair_mem_sigma_map.mpr ⟨hvalue, ih _ tail htail htail'⟩
  | recArg tele index rest ih =>
    obtain ⟨value, hvalue, tail, htail, rfl⟩ := mem_sigma_map.mp h
    have ⟨_, hvalue', tail', htail', heq⟩ := mem_sigma_map.mp h'
    have ⟨rfl, rfl⟩ := pair_inj.mp heq
    have hvalueW : value ∈ recFieldSet tele index blockW γ := tele.pi_inter_cod
      (fun _ _ hv hv' => mem_fibre.mpr (hw _ (mem_fibre.mp hv) (mem_fibre.mp hv')))
      γ value hvalue hvalue'
    exact pair_mem_sigma_map.mpr ⟨hvalueW, ih _ tail htail htail'⟩

theorem argSet_mem_of_support
    (code : CtorCode n) (γ : Slots n) (vargs : ZFSet)
    (hargs : vargs ∈ code.argSet block₁ γ)
    (hsupport : ∀ point : code.Support γ,
      code.readSupport γ vargs point ∈ block₁ →
        code.readSupport γ vargs point ∈ block₂) :
    vargs ∈ code.argSet block₂ γ := by
  induction code generalizing vargs with
  | target => exact hargs
  | arg domain rest ih =>
    obtain ⟨value, hvalue, tail, htail, rfl⟩ := mem_sigma_map.mp hargs
    refine pair_mem_sigma_map.mpr ⟨hvalue, ih (γ.snoc value) tail htail ?_⟩
    exact fun point => by simpa [readSupport] using hsupport ⟨⟨value, hvalue⟩, point⟩
  | recArg tele index rest ih =>
    obtain ⟨field, hfield, tail, htail, rfl⟩ := mem_sigma_map.mp hargs
    refine pair_mem_sigma_map.mpr ⟨(tele.pi_mem_iff γ field hfield).mpr ?_, ih γ tail htail ?_⟩
    · exact fun final hfinal => mem_fibre.mpr (by
        simpa [readSupport] using hsupport (.inl ⟨final, hfinal⟩)
          (by simpa [readSupport] using mem_fibre.mp (Reachable.app_mem hfinal hfield)))
    · exact fun point => by simpa [readSupport] using hsupport (.inr point)

theorem eq_proof_of_mem_argSet_prependRecursive {count : Nat}
    {fields : Fin count → CtorRecCode.Packed n} {index : Dom n}
    (hcount : IsEmpty (Fin count))
    (h : vargs ∈ argSet block (prependRecursive count fields (.target index)) γ) :
    vargs = proof := by
  obtain rfl : count = 0 := Fin.eq_zero_of_isEmpty hcount
  exact mem_verum.mp h

noncomputable def applyFields (level : Nat) {n : Nat} :
    (code : CtorCode n) → Slots n → ZFSet → ZFSet → ZFSet
  | .target _ => fun _ minor _ => minor
  | .arg _ rest => fun γ minor vargs =>
    applyFields level rest (γ.snoc [zf|vargs.1]) [zf|minor vargs.1] [zf|vargs.2]
  | .recArg tele _ rest => fun γ minor vargs =>
    applyFields level rest γ [zf|minor $(eraseRecField tele level γ [zf|vargs.1])]
      [zf|vargs.2]

noncomputable def applyIhs (graph : ZFSet) {n : Nat} :
    CtorCode n → Slots n → ZFSet → ZFSet → ZFSet
  | .target _ => fun _ minor _ => minor
  | .arg _ rest => fun γ minor vargs =>
    applyIhs graph rest (γ.snoc [zf|vargs.1]) minor [zf|vargs.2]
  | .recArg tele index rest => fun γ minor vargs =>
    applyIhs graph rest γ [zf|minor $(recMap tele index graph γ [zf|vargs.1])] [zf|vargs.2]

noncomputable def applyMinor (level : Nat) (graph : ZFSet) {n : Nat}
    (code : CtorCode n) (γ : Slots n) (minor vargs : ZFSet) : ZFSet :=
  applyIhs graph code γ (applyFields level code γ minor vargs) vargs

theorem applyIhs_congr (h : ∀ value ∈ block, app graph₁ value = app graph₂ value)
    (code : CtorCode n) (γ : Slots n) (minor vargs : ZFSet)
    (hargs : vargs ∈ argSet block code γ) :
    applyIhs graph₁ code γ minor vargs = applyIhs graph₂ code γ minor vargs := by
  induction code generalizing minor vargs with
  | target => rfl
  | arg domain rest ih =>
    obtain ⟨value, _, tail, htail, rfl⟩ := mem_sigma_map.mp hargs
    simpa! using ih (γ.snoc value) minor tail htail
  | recArg tele index rest ih =>
    obtain ⟨value, hvalue, tail, htail, rfl⟩ := mem_sigma_map.mp hargs
    simp only [applyIhs, fst_pair, snd_pair]
    rw [recMap_congr tele index h γ value hvalue]
    exact ih γ _ tail htail

theorem applyMinor_congr {level : Nat} (h : ∀ value ∈ block, app graph₁ value = app graph₂ value)
    (code : CtorCode n) (γ : Slots n) (minor vargs : ZFSet)
    (hargs : vargs ∈ argSet block code γ) :
    applyMinor level graph₁ code γ minor vargs = applyMinor level graph₂ code γ minor vargs :=
  applyIhs_congr h code γ _ vargs hargs

noncomputable def targetIndex {n : Nat} :
    CtorCode n → Slots n → ZFSet → ZFSet
  | .target index => fun γ _ => index γ
  | .arg _ rest => fun γ vargs =>
    targetIndex rest (γ.snoc [zf|vargs.1]) [zf|vargs.2]
  | .recArg _ _ rest => fun γ vargs => targetIndex rest γ [zf|vargs.2]

theorem tail_mem_argSet {Δ : SemTele n b} {rest : CtorCode b}
    (hargs : vargs ∈ (prependOrdinary Δ rest).argSet block γ) :
    Δ.tail vargs ∈ rest.argSet block (Δ.values γ vargs) := by
  induction Δ with
  | nil => exact hargs
  | snoc Δ domain ih =>
    have ⟨_, _, _, htail, heq⟩ := mem_sigma_map.mp (ih hargs)
    change snd (SemTele.tail vargs Δ) ∈ rest.argSet block
      (Fin.snoc (SemTele.values γ vargs Δ) (fst (SemTele.tail vargs Δ)))
    rwa [heq, fst_pair, snd_pair]

end CtorCode

end Metalean
