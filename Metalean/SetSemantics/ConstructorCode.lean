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
  rw [recoverRecField]
  simp only [SemTele.lamAt]
  rw [← SemTele.fold_applyAt _ Aczel.lam]
  simpa [SemTele.app_eq_apps, SemTele.lam] using Reachable.apps_lam_of_base hfinal

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
  rwa [Δ.piAt_const
    (fun final => propSet level (fibreOp block (index final))) γ value] at h

theorem recoverRecField_mem (Δ : SemTele n b) (index : Dom b)
    {block : ZFSet} {level : Nat} {γ : Slots n} {value : ZFSet}
    (hfield : value ∈ typedRecFieldSet Δ index block level γ) :
    recoverRecField Δ index block level γ value ∈
      recFieldSet Δ index block γ := by
  have h := Δ.lamAt_mem_piAt
    (domain := fun final => propSet level (fibreOp block (index final)))
    (cod := fun final _ => fibreOp block (index final))
    (fun _ _ hvalue => propGet_mem hvalue) γ value hfield
  rwa [Δ.piAt_const (fun final => fibreOp block (index final)) γ value] at h

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

variable {blockW : ZFSet} {γ : Slots n} {vargs : ZFSet}

noncomputable def support {n : Nat} :
    CtorCode n → Dom n
  | .target _ => fun _ => ∅
  | .arg domain rest => fun γ =>
    σ (domain γ) (map (fun value => rest.support (γ.snoc value)) (domain γ))
  | .recArg tele _ rest => fun γ =>
    image (fun point => [zf|(falsum, point)]) (tele.support (fun _ => verum) γ) ∪
      image (fun point => [zf|(verum, point)]) (rest.support γ)

noncomputable def readSupport {n : Nat}
    (code : CtorCode n) : Slots n → ZFSet → ZFSet → ZFSet :=
  code.rec
    (fun _ _ _ _ => ∅)
    (fun _ _ read γ vargs point =>
      read (γ.snoc [zf|vargs.1]) [zf|vargs.2] [zf|point.2])
    fun tele index _ read γ vargs point =>
      branch [zf|point.1]
        (tele.readSupport (fun final value _ => [zf|($(index final), value)])
          γ [zf|vargs.1] [zf|point.2])
        (read γ [zf|vargs.2] [zf|point.2])

noncomputable def argSet (block : ZFSet) {n : Nat} :
    CtorCode n → Dom n
  | .target _ => fun _ => verum
  | .arg domain rest => fun γ =>
    σ (domain γ) (map (fun value => rest.argSet block (γ.snoc value)) (domain γ))
  | .recArg tele index rest => fun γ =>
    let domain := recFieldSet tele index block γ
    σ domain (map (fun _ => rest.argSet block γ) domain)

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
    obtain ⟨value, hvalue, tail, htail, rfl⟩ := mem_sigma.mp h
    have ⟨_, hvalue', tail', htail', heq⟩ := mem_sigma.mp h'
    have ⟨rfl, rfl⟩ := pair_inj.mp heq
    rw [app_map hvalue] at htail
    rw [app_map hvalue'] at htail'
    exact mem_sigma.mpr ⟨value, hvalue, tail,
      by rw [app_map hvalue]; exact ih _ tail htail htail', rfl⟩
  | recArg tele index rest ih =>
    obtain ⟨value, hvalue, tail, htail, rfl⟩ := mem_sigma.mp h
    have ⟨_, hvalue', tail', htail', heq⟩ := mem_sigma.mp h'
    have ⟨rfl, rfl⟩ := pair_inj.mp heq
    rw [app_map hvalue] at htail
    rw [app_map hvalue'] at htail'
    have hvalueW : value ∈ recFieldSet tele index blockW γ := tele.pi_inter_cod
      (fun _ _ hv hv' => mem_fibre.mpr (hw _ (mem_fibre.mp hv) (mem_fibre.mp hv')))
      γ value hvalue hvalue'
    exact mem_sigma.mpr ⟨value, hvalueW, tail,
      by rw [app_map hvalueW]; exact ih _ tail htail htail', rfl⟩

theorem mem_argSet_arg {domain : Dom n} {rest : CtorCode (n + 1)}
    {value : ZFSet} (hvalue : value ∈ domain γ)
    (hrest : vargs ∈ rest.argSet block (Fin.snoc γ value)) :
    [zf|(value, vargs)] ∈ (CtorCode.arg domain rest).argSet block γ :=
  mem_sigma.mpr ⟨value, hvalue, vargs, by rw [app_map hvalue]; simpa! using hrest, rfl⟩

theorem mem_argSet_recArg {b : Nat} {tele : SemTele n b} {index : Dom b}
    {rest : CtorCode n} {value : ZFSet}
    (hvalue : value ∈ recFieldSet tele index block γ)
    (hrest : vargs ∈ rest.argSet block γ) :
    [zf|(value, vargs)] ∈ (CtorCode.recArg tele index rest).argSet block γ :=
  mem_sigma.mpr ⟨value, hvalue, vargs, by rw [app_map hvalue]; simpa! using hrest, rfl⟩

theorem argSet_arg_inv {domain : Dom n} {rest : CtorCode (n + 1)}
    (h : vargs ∈ (CtorCode.arg domain rest).argSet block γ) :
    ∃ value t : ZFSet, value ∈ domain γ ∧
      t ∈ rest.argSet block (Fin.snoc γ value) ∧ vargs = [zf|(value, t)] := by
  obtain ⟨value, hvalue, t, ht, rfl⟩ := mem_sigma.mp h
  rw [app_map hvalue] at ht
  exact ⟨value, t, hvalue, by simpa using ht, rfl⟩

theorem argSet_recArg_inv {b : Nat} {tele : SemTele n b} {index : Dom b}
    {rest : CtorCode n}
    (h : vargs ∈ (CtorCode.recArg tele index rest).argSet block γ) :
    ∃ value t : ZFSet, value ∈ recFieldSet tele index block γ ∧
      t ∈ rest.argSet block γ ∧ vargs = [zf|(value, t)] := by
  obtain ⟨value, hvalue, t, ht, rfl⟩ := mem_sigma.mp h
  rw [app_map hvalue] at ht
  exact ⟨value, t, hvalue, by simpa using ht, rfl⟩

theorem argSet_mem_of_support
    (code : CtorCode n) (γ : Slots n) (vargs : ZFSet)
    (hargs : vargs ∈ code.argSet block₁ γ)
    (hsupport : ∀ point ∈ code.support γ,
      code.readSupport γ vargs point ∈ block₁ →
        code.readSupport γ vargs point ∈ block₂) :
    vargs ∈ code.argSet block₂ γ := by
  induction code generalizing vargs with
  | target => exact hargs
  | arg domain rest ih =>
    obtain ⟨value, tail, hvalue, htail, rfl⟩ := argSet_arg_inv hargs
    refine mem_argSet_arg hvalue (ih (γ.snoc value) tail htail ?_)
    intro point hpoint hmem
    have hp := hsupport [zf|(value, point)] (mem_sigma.mpr
      ⟨value, hvalue, point, by rw [app_map hvalue]; exact hpoint, rfl⟩)
    have hmem' : (CtorCode.arg domain rest).readSupport γ
        [zf|(value, tail)] [zf|(value, point)] ∈ block₁ := by
      simpa [readSupport] using hmem
    simpa [readSupport] using hp hmem'
  | recArg tele index rest ih =>
    obtain ⟨field, tail, hfield, htail, rfl⟩ := argSet_recArg_inv hargs
    have hfield' : field ∈ recFieldSet tele index block₂ γ := by
      refine tele.pi_replace
        (source := fun final => fibreOp block₁ (index final))
        (target := fun final => fibreOp block₂ (index final))
        (address := fun _ => verum)
        (read := fun final value _ => [zf|($(index final), value)])
        (fun entry => entry ∈ block₁ → entry ∈ block₂)
        (fun final value hvalue hread =>
          mem_fibre.mpr (hread proof proof_mem_verum (mem_fibre.mp hvalue)))
        γ field hfield fun point hpoint hmem => ?_
      have hp := hsupport [zf|(falsum, point)] (mem_union.mpr (.inl
        (mem_image.mpr ⟨point, hpoint, rfl⟩)))
      have hmem' : (CtorCode.recArg tele index rest).readSupport γ
          [zf|(field, tail)] [zf|(falsum, point)] ∈ block₁ := by
        simpa [readSupport] using hmem
      simpa [readSupport] using hp hmem'
    refine mem_argSet_recArg hfield' (ih γ tail htail ?_)
    intro point hpoint hmem
    have hp := hsupport [zf|(verum, point)] (mem_union.mpr (.inr
      (mem_image.mpr ⟨point, hpoint, rfl⟩)))
    have hmem' : (CtorCode.recArg tele index rest).readSupport γ
        [zf|(field, tail)] [zf|(verum, point)] ∈ block₁ := by
      rw [readSupport]
      simp
      exact hmem
    simpa [readSupport] using hp hmem'

theorem eq_proof_of_mem_argSet_target {index : Dom n}
    (h : vargs ∈ argSet block (.target index) γ) : vargs = proof := by
  simpa! using h

theorem proof_mem_argSet_target {index : Dom n} (γ : Slots n) :
    proof ∈ argSet block (CtorCode.target index) γ := by
  simp!

theorem eq_proof_of_mem_argSet_prependRecursive {count : Nat}
    {fields : Fin count → CtorRecCode.Packed n} {index : Dom n}
    (hcount : IsEmpty (Fin count))
    (h : vargs ∈ argSet block (prependRecursive count fields (.target index)) γ) :
    vargs = proof := by
  obtain rfl : count = 0 := Fin.eq_zero_of_isEmpty hcount
  exact eq_proof_of_mem_argSet_target h

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
    obtain ⟨value, tail, _, htail, rfl⟩ := argSet_arg_inv hargs
    simpa! using ih (γ.snoc value) minor tail htail
  | recArg tele index rest ih =>
    obtain ⟨value, tail, hvalue, htail, rfl⟩ := argSet_recArg_inv hargs
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
    have ⟨_, _, _, htail, heq⟩ := argSet_arg_inv (ih hargs)
    change snd (SemTele.tail vargs Δ) ∈ rest.argSet block
      (Fin.snoc (SemTele.values γ vargs Δ) (fst (SemTele.tail vargs Δ)))
    rwa [heq, fst_pair, snd_pair]

end CtorCode

end Metalean
