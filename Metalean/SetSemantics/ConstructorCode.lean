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

noncomputable def ihSet (Δ : SemTele n b) (index : Dom b) (block motive : ZFSet) : Dom n :=
  fun γ =>
    σ (recFieldSet Δ index block γ)
      (map (ihType Δ index motive γ) (recFieldSet Δ index block γ))

theorem ihSet_mono (Δ : SemTele n b) (index : Dom b) (h : block₁ ⊆ block₂) (motive : ZFSet)
    (γ : Slots n) : ihSet Δ index block₁ motive γ ⊆ ihSet Δ index block₂ motive γ := by
  have hdom := recFieldSet_mono Δ index h γ
  refine sigma_mono hdom fun field hfield => ?_
  rw [app_map hfield, app_map (hdom hfield)]

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

noncomputable def recEntries (Δ : SemTele n b) (index : Dom b)
    (γ : Slots n) (value : ZFSet) : ZFSet :=
  Δ.collect (fun final value => {[zf|($(index final), value)]}) γ value

theorem mem_recEntries_of_mem (Δ : SemTele n b) (index : Dom b)
    {block : ZFSet} (γ : Slots n) (value : ZFSet)
    (hfield : value ∈ Δ.pi (fun final => fibreOp block (index final)) γ) :
    ∀ entry ∈ recEntries Δ index γ value, entry ∈ block := by
  refine Δ.collect_property (fun entry => entry ∈ block)
    (fun final value hvalue entry hentry => ?_) γ value hfield
  rw [mem_singleton.mp hentry]
  exact mem_fibre.mp hvalue

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

noncomputable def predecessors {n : Nat} :
    CtorCode n → Slots n → ZFSet → ZFSet
  | .target _, _, _ => ∅
  | .arg _ rest, γ, vargs =>
    predecessors rest (γ.snoc [zf|vargs.1]) [zf|vargs.2]
  | .recArg tele index rest, γ, vargs =>
    recEntries tele index γ [zf|vargs.1] ∪ predecessors rest γ [zf|vargs.2]

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

noncomputable def ihArgSet
    (block motive : ZFSet) {n : Nat} :
    CtorCode n → Dom n
  | .target _ => fun _ => verum
  | .arg domain rest => fun γ =>
    σ (domain γ) (map (fun value => rest.ihArgSet block motive (γ.snoc value))
      (domain γ))
  | .recArg tele index rest => fun γ =>
    let domain := ihSet tele index block motive γ
    σ domain (map (fun _ => rest.ihArgSet block motive γ) domain)

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

theorem ihArgSet_mono (h : block₁ ⊆ block₂) (motive : ZFSet) (code : CtorCode n)
    (γ : Slots n) : ihArgSet block₁ motive code γ ⊆ ihArgSet block₂ motive code γ := by
  induction code with
  | target => exact subset_refl _
  | arg domain rest ih =>
    refine sigma_mono (subset_refl _) fun value hvalue => ?_
    rw [app_map hvalue, app_map hvalue]
    exact ih _
  | recArg tele index rest ih =>
    have hdomain := ihSet_mono tele index h motive γ
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
  mem_sigma.mpr ⟨value, hvalue, vargs, by rw [app_map hvalue]; simpa [argSet] using hrest, rfl⟩

theorem mem_argSet_recArg {b : Nat} {tele : SemTele n b} {index : Dom b}
    {rest : CtorCode n} {value : ZFSet}
    (hvalue : value ∈ recFieldSet tele index block γ)
    (hrest : vargs ∈ rest.argSet block γ) :
    [zf|(value, vargs)] ∈ (CtorCode.recArg tele index rest).argSet block γ :=
  mem_sigma.mpr ⟨value, hvalue, vargs, by rw [app_map hvalue]; simpa [argSet] using hrest, rfl⟩

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
      simpa [readSupport, branch_falsum] using hp hmem'
    refine mem_argSet_recArg hfield' (ih γ tail htail ?_)
    intro point hpoint hmem
    have hp := hsupport [zf|(verum, point)] (mem_union.mpr (.inr
      (mem_image.mpr ⟨point, hpoint, rfl⟩)))
    have hmem' : (CtorCode.recArg tele index rest).readSupport γ
        [zf|(field, tail)] [zf|(verum, point)] ∈ block₁ := by
      rw [readSupport]
      simp [branch_verum]
      exact hmem
    simpa [readSupport, branch_verum] using hp hmem'

theorem eq_proof_of_mem_argSet_target {index : Dom n}
    (h : vargs ∈ argSet block (.target index) γ) : vargs = proof := by
  simpa [argSet] using h

theorem proof_mem_argSet_target {index : Dom n} (γ : Slots n) :
    proof ∈ argSet block (CtorCode.target index) γ := by
  simp [argSet]

theorem eq_proof_of_mem_argSet_prependRecursive {count : Nat}
    {fields : Fin count → CtorRecCode.Packed n} {index : Dom n}
    (hcount : IsEmpty (Fin count))
    (h : vargs ∈ argSet block (prependRecursive count fields (.target index)) γ) :
    vargs = proof := by
  obtain rfl : count = 0 := Fin.eq_zero_of_isEmpty hcount
  exact eq_proof_of_mem_argSet_target h

noncomputable def argMap (graph : ZFSet) {n : Nat} :
    CtorCode n → Slots n → ZFSet → ZFSet
  | .target _ => fun _ vargs => vargs
  | .arg _ rest => fun γ vargs => [zf|(vargs.1,
    $(argMap graph rest (γ.snoc [zf|vargs.1]) [zf|vargs.2]))]
  | .recArg tele index rest => fun γ vargs =>
    [zf|((vargs.1, $(recMap tele index graph γ [zf|vargs.1])),
      $(argMap graph rest γ [zf|vargs.2]))]

private theorem lamAt_congr_of_collect {a b : Nat} (P : ZFSet → Prop)
    {domain : Dom b} {leaf leaf' keys : DomAt b} (tele : SemTele a b)
    (hleaf : ∀ (final : Slots b) (value : ZFSet), value ∈ domain final →
      (∀ key ∈ keys final value, P key) → leaf final value = leaf' final value)
    (γ : Slots a) (value : ZFSet) (hfield : value ∈ tele.pi domain γ)
    (hkeys : ∀ key ∈ tele.collect keys γ value, P key) :
    tele.lamAt leaf γ value = tele.lamAt leaf' γ value := by
  induction tele generalizing value with
  | nil => exact hleaf γ value hfield (by simpa [SemTele.collect, SemTele.foldAt] using hkeys)
  | snoc tele next ih =>
    refine ih
      (domain := fun current => [zf|(argument : $(next current)) →
        $(domain (current.snoc argument))])
      (leaf := fun current function => [zf|fun argument : $(next current) =>
        $(leaf (current.snoc argument) [zf|function argument])])
      (leaf' := fun current function => [zf|fun argument : $(next current) =>
        $(leaf' (current.snoc argument) [zf|function argument])])
      (keys := fun current function =>
        ⋃₀ image (fun argument => keys (current.snoc argument) [zf|function argument])
          (next current))
      (fun current function hfunction hlocal => ?_) value hfield
      (by simpa [SemTele.collect, SemTele.foldAt] using hkeys)
    refine Aczel.lam_congr fun argument hargument => ?_
    have happ := Aczel.app_mem hfunction hargument
    rw [app_map hargument] at happ
    exact hleaf (current.snoc argument) [zf|function argument] happ fun key hkey =>
      hlocal key (mem_sUnion.mpr ⟨_, mem_image.mpr ⟨argument, hargument, rfl⟩, hkey⟩)

theorem argMap_congr_of_predecessors (code : CtorCode n)
    (γ : Slots n) (vargs : ZFSet) (hargs : vargs ∈ code.argSet block γ)
    (hgraph : ∀ predecessor ∈ code.predecessors γ vargs,
      app graph₁ predecessor = app graph₂ predecessor) :
    code.argMap graph₁ γ vargs = code.argMap graph₂ γ vargs := by
  induction code generalizing vargs with
  | target => rfl
  | arg domain rest ih =>
    obtain ⟨value, tail, _, htail, rfl⟩ := argSet_arg_inv hargs
    simp [argMap]
    rw [ih (γ.snoc value) tail htail]
    intro predecessor hpredecessor
    apply hgraph predecessor
    simpa [predecessors] using hpredecessor
  | recArg tele index rest ih =>
    obtain ⟨field, tail, hfield, htail, rfl⟩ := argSet_recArg_inv hargs
    have hfieldMap : recMap tele index graph₁ γ field = recMap tele index graph₂ γ field := by
      apply lamAt_congr_of_collect
        (fun predecessor => app graph₁ predecessor = app graph₂ predecessor)
        (keys := fun final value => {[zf|($(index final), value)]})
      · intro final value _ hlocal
        simpa using hlocal [zf|($(index final), value)] (by simp)
      · exact hfield
      · intro predecessor hpredecessor
        apply hgraph predecessor
        simpa [predecessors] using .inl hpredecessor
    simp only [argMap, fst_pair, snd_pair]
    rw [hfieldMap, ih γ tail htail]
    intro predecessor hpredecessor
    apply hgraph predecessor
    simpa [predecessors] using .inr hpredecessor

noncomputable def forgetIhs {n : Nat} :
    CtorCode n → ZFSet → ZFSet
  | .target _ => fun vargs => vargs
  | .arg _ rest => fun vargs => [zf|(vargs.1, $(forgetIhs rest [zf|vargs.2]))]
  | .recArg _ _ rest => fun vargs =>
    [zf|((vargs.1).1, $(forgetIhs rest [zf|vargs.2]))]

theorem forgetIhs_mem_argSet (code : CtorCode n)
    (γ : Slots n) (vargs : ZFSet)
    (hargs : vargs ∈ code.ihArgSet block motive γ) :
    code.forgetIhs vargs ∈ code.argSet block γ := by
  induction code generalizing vargs with
  | target => exact hargs
  | arg domain rest ih =>
    obtain ⟨value, hvalue, tail, htail, rfl⟩ := mem_sigma.mp hargs
    rw [app_map hvalue] at htail
    simpa [forgetIhs] using mem_argSet_arg hvalue (ih (γ.snoc value) tail htail)
  | recArg tele index rest ih =>
    obtain ⟨fieldAndIh, hfieldAndIh, tail, htail, rfl⟩ := mem_sigma.mp hargs
    rw [app_map hfieldAndIh] at htail
    obtain ⟨field, hfield, fieldIh, _, rfl⟩ := mem_sigma.mp hfieldAndIh
    simpa [forgetIhs] using mem_argSet_recArg hfield (ih γ tail htail)

noncomputable def applyFields (level : Nat) {n : Nat} :
    (code : CtorCode n) → Slots n → ZFSet → ZFSet → ZFSet
  | .target _ => fun _ minor _ => minor
  | .arg _ rest => fun γ minor vargs =>
    applyFields level rest (γ.snoc [zf|vargs.1]) [zf|minor vargs.1] [zf|vargs.2]
  | .recArg tele _ rest => fun γ minor vargs =>
    applyFields level rest γ [zf|minor $(eraseRecField tele level γ [zf|vargs.1])]
      [zf|vargs.2]

noncomputable def applyIhs {n : Nat} :
    CtorCode n → ZFSet → ZFSet → ZFSet
  | .target _ => fun minor _ => minor
  | .arg _ rest => fun minor vargs => applyIhs rest minor [zf|vargs.2]
  | .recArg _ _ rest => fun minor vargs =>
    applyIhs rest [zf|minor (vargs.1).2] [zf|vargs.2]

noncomputable def applyMinor (level : Nat) {n : Nat}
    (code : CtorCode n)
    (γ : Slots n) (minor vargs : ZFSet) : ZFSet :=
  applyIhs code (applyFields level code γ minor (forgetIhs code vargs)) vargs

theorem argMap_congr (h : ∀ value ∈ block, app graph₁ value = app graph₂ value)
    (code : CtorCode n) (γ : Slots n) (vargs : ZFSet)
    (hargs : vargs ∈ argSet block code γ) :
    argMap graph₁ code γ vargs = argMap graph₂ code γ vargs := by
  induction code generalizing vargs with
  | target => rfl
  | arg domain rest ih =>
    obtain ⟨value, tail, _, htail, rfl⟩ := argSet_arg_inv hargs
    simp [argMap]
    rw [ih (γ.snoc value) tail htail]
  | recArg tele index rest ih =>
    obtain ⟨value, tail, hvalue, htail, rfl⟩ := argSet_recArg_inv hargs
    simp only [argMap, fst_pair, snd_pair]
    rw [recMap_congr tele index h γ value hvalue, ih γ tail htail]

theorem forgetIhs_argMap (code : CtorCode n) (γ : Slots n) (vargs : ZFSet)
    (hargs : vargs ∈ argSet block code γ) :
    forgetIhs code (argMap graph code γ vargs) = vargs := by
  induction code generalizing vargs with
  | target => rfl
  | arg domain rest ih =>
    obtain ⟨value, tail, _, htail, rfl⟩ := argSet_arg_inv hargs
    simp [argMap, forgetIhs]
    rw [ih (γ.snoc value) tail htail]
  | recArg tele index rest ih =>
    obtain ⟨value, tail, _, htail, rfl⟩ := argSet_recArg_inv hargs
    simp [argMap, forgetIhs]
    rw [ih γ tail htail]

theorem argMap_mem (hgraph : ∀ value ∈ block, app graph value ∈ fibreOp motive value)
    (code : CtorCode n) (γ : Slots n) (vargs : ZFSet)
    (hargs : vargs ∈ argSet block code γ) :
    argMap graph code γ vargs ∈ ihArgSet block motive code γ := by
  induction code generalizing vargs with
  | target => exact hargs
  | arg domain rest ih =>
    obtain ⟨value, tail, hvalue, htail, rfl⟩ := argSet_arg_inv hargs
    refine mem_sigma.mpr ⟨value, hvalue, argMap graph rest (γ.snoc value) tail,
      by rw [app_map hvalue]; exact ih (γ.snoc value) tail htail, ?_⟩
    simp [argMap]
  | recArg tele index rest ih =>
    obtain ⟨value, tail, hvalue, htail, rfl⟩ := argSet_recArg_inv hargs
    have hih : [zf|(value, $(recMap tele index graph γ value))]
        ∈ ihSet tele index block motive γ := by
      refine mem_sigma.mpr ⟨value, hvalue, recMap tele index graph γ value, ?_, rfl⟩
      rw [app_map hvalue]
      exact recMap_mem tele index hgraph γ value hvalue
    refine mem_sigma.mpr
      ⟨_, hih, argMap graph rest γ tail, by rw [app_map hih]; exact ih γ tail htail,
        ?_⟩
    simp [argMap]

noncomputable def targetIndex {n : Nat} :
    CtorCode n → Slots n → ZFSet → ZFSet
  | .target index => fun γ _ => index γ
  | .arg _ rest => fun γ vargs =>
    targetIndex rest (γ.snoc [zf|vargs.1]) [zf|vargs.2]
  | .recArg _ _ rest => fun γ vargs => targetIndex rest γ [zf|vargs.2]

inductive ArgAgree :
    {n : Nat} → CtorCode n → ZFSet → ZFSet → Prop
  | target {n : Nat} {index : Dom n} {vargs : ZFSet} :
    ArgAgree (.target index) vargs vargs
  | arg {n : Nat} {domain : Dom n}
    {rest : CtorCode (n + 1)} {left right : ZFSet} :
    fst left = fst right →
    ArgAgree rest (snd left) (snd right) →
    ArgAgree (.arg domain rest) left right
  | recArg {n b : Nat} {tele : SemTele n b} {index : Dom b}
    {rest : CtorCode n} {left right : ZFSet} :
    ArgAgree rest (snd left) (snd right) →
    ArgAgree (.recArg tele index rest) left right

private theorem SemTele.collect_key_recover
    {leftDomain rightDomain : Dom b} {leaf : DomAt b} (tele : SemTele n b)
    (hleaf : ∀ (final : Slots b) (left right : ZFSet),
      left ∈ leftDomain final → right ∈ rightDomain final →
      ∀ result ∈ leaf final right,
        ∃ recovered ∈ leaf final left, [zf|recovered.1] = [zf|result.1])
    (γ : Slots n) {left right : ZFSet}
    (hleft : left ∈ tele.pi leftDomain γ)
    (hright : right ∈ tele.pi rightDomain γ) :
    ∀ result ∈ tele.collect leaf γ right,
      ∃ recovered ∈ tele.collect leaf γ left,
        [zf|recovered.1] = [zf|result.1] := by
  induction tele generalizing left right with
  | nil => exact hleaf γ left right hleft hright
  | snoc tele next ih =>
    have hleftPi : left ∈ SemTele.pi
        (fun current => [zf|(argument : $(next current)) →
          $(leftDomain (current.snoc argument))]) tele γ := by
      simpa [SemTele.pi, SemTele.fold] using hleft
    have hrightPi : right ∈ SemTele.pi
        (fun current => [zf|(argument : $(next current)) →
          $(rightDomain (current.snoc argument))]) tele γ := by
      simpa [SemTele.pi, SemTele.fold] using hright
    apply ih
      (leftDomain := fun current => [zf|(argument : $(next current)) →
        $(leftDomain (current.snoc argument))])
      (rightDomain := fun current => [zf|(argument : $(next current)) →
        $(rightDomain (current.snoc argument))])
      (leaf := fun current function =>
        ⋃₀ image (fun argument =>
          leaf (current.snoc argument) [zf|function argument])
          (next current)) ?_ hleftPi hrightPi
    intro current leftFunction rightFunction hleftFunction hrightFunction
      result hresult
    have ⟨results, hresults, hresult⟩ := mem_sUnion.mp hresult
    obtain ⟨argument, hargument, rfl⟩ := mem_image.mp hresults
    have hleftValue := Aczel.app_mem hleftFunction hargument
    have hrightValue := Aczel.app_mem hrightFunction hargument
    rw [app_map hargument] at hleftValue hrightValue
    have ⟨recovered, hrecovered, hkey⟩ := hleaf
      (current.snoc argument) [zf|leftFunction argument]
      [zf|rightFunction argument] hleftValue hrightValue result hresult
    exact ⟨recovered, mem_sUnion.mpr
      ⟨_, mem_image.mpr ⟨argument, hargument, rfl⟩, hrecovered⟩, hkey⟩

private theorem recEntries_key_recover
    (tele : SemTele n b) (index : Dom b) (leftBlock rightBlock : ZFSet)
    (γ : Slots n) {left right entry : ZFSet}
    (hleft : left ∈ recFieldSet tele index leftBlock γ)
    (hright : right ∈ recFieldSet tele index rightBlock γ)
    (hentry : entry ∈ recEntries tele index γ right) :
    ∃ recovered ∈ recEntries tele index γ left,
      [zf|recovered.1] = [zf|entry.1] := by
  rw [recFieldSet] at hleft hright
  refine SemTele.collect_key_recover tele (γ := γ) ?_ hleft hright entry hentry
  · intro final leftValue rightValue _ _ result hresult
    rw [mem_singleton] at hresult
    refine ⟨[zf|($(index final), leftValue)], by simp, ?_⟩
    rw [hresult]
    simp

theorem predecessor_key_recover
    (code : CtorCode n) (leftBlock rightBlock : ZFSet)
    (γ : Slots n) {left right predecessor : ZFSet}
    (hleft : left ∈ code.argSet leftBlock γ)
    (hright : right ∈ code.argSet rightBlock γ)
    (hagree : code.ArgAgree left right)
    (hpredecessor : predecessor ∈ code.predecessors γ right) :
    ∃ recovered ∈ code.predecessors γ left,
      [zf|recovered.1] = [zf|predecessor.1] := by
  induction hagree generalizing predecessor with
  | target => simp [predecessors] at hpredecessor
  | arg hfst _ ih =>
    obtain ⟨leftValue, leftTail, _, hleftTail, rfl⟩ := argSet_arg_inv hleft
    obtain ⟨rightValue, rightTail, _, hrightTail, rfl⟩ := argSet_arg_inv hright
    simp only [fst_pair, snd_pair] at hfst ih
    subst hfst
    simp only [predecessors, fst_pair, snd_pair] at hpredecessor ⊢
    exact ih _ hleftTail hrightTail hpredecessor
  | @recArg _ _ tele index _ _ _ _ ih =>
    obtain ⟨leftField, leftTail, hleftField, hleftTail, rfl⟩ := argSet_recArg_inv hleft
    obtain ⟨rightField, rightTail, hrightField, hrightTail, rfl⟩ := argSet_recArg_inv hright
    simp only [snd_pair] at ih
    simp only [predecessors, fst_pair, snd_pair, mem_union] at hpredecessor ⊢
    cases hpredecessor with
    | inl hfield =>
      have ⟨recovered, hrecovered, hkey⟩ := recEntries_key_recover
        tele index leftBlock rightBlock γ hleftField hrightField hfield
      exact ⟨recovered, .inl hrecovered, hkey⟩
    | inr htail =>
      have ⟨recovered, hrecovered, hkey⟩ := ih γ hleftTail hrightTail htail
      exact ⟨recovered, .inr hrecovered, hkey⟩

theorem argAgree_prependRecursive {count : Nat}
    (fields : Fin count → CtorRecCode.Packed n) (index : Dom n)
    (block : ZFSet) (γ : Slots n) {left right : ZFSet}
    (hleft : left ∈ (prependRecursive count fields (.target index)).argSet
      block γ)
    (hright : right ∈ (prependRecursive count fields (.target index)).argSet
      block γ) :
    (prependRecursive count fields (.target index)).ArgAgree left right := by
  induction count generalizing left right with
  | zero =>
    rw [eq_proof_of_mem_argSet_target hleft, eq_proof_of_mem_argSet_target hright]
    exact .target
  | succ count ih =>
    obtain ⟨leftField, leftTail, _, hleftTail, rfl⟩ := argSet_recArg_inv hleft
    obtain ⟨rightField, rightTail, _, hrightTail, rfl⟩ := argSet_recArg_inv hright
    refine .recArg ?_
    rw [snd_pair, snd_pair]
    exact ih (fields := fun f => fields f.succ) hleftTail hrightTail

theorem argAgree_prependOrdinary (Δ : SemTele n b) (rest : CtorCode b) (γ : Slots n)
    {left right : ZFSet}
    (htail : rest.ArgAgree (Δ.tail left) (Δ.tail right))
    (hvalues : Δ.values γ left = Δ.values γ right) :
    (prependOrdinary Δ rest).ArgAgree left right := by
  induction Δ with
  | nil => exact htail
  | snoc Δ domain ih =>
    have hlast := (Fin.snoc_last ..).symm.trans
      ((congrFun hvalues (Fin.last _)).trans (Fin.snoc_last ..))
    have hinit := (Fin.init_snoc ..).symm.trans
      ((congrArg Fin.init hvalues).trans (Fin.init_snoc ..))
    exact ih (.arg domain rest) (.arg hlast htail) hinit

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

theorem tail_mem_ihArgSet {Δ : SemTele n b} {rest : CtorCode b}
    (hargs : vargs ∈ (prependOrdinary Δ rest).ihArgSet block motive γ) :
    Δ.tail vargs ∈ rest.ihArgSet block motive (Δ.values γ vargs) := by
  induction Δ with
  | nil => exact hargs
  | snoc Δ domain ih =>
    have ⟨_, hvalue, _, htail, heq⟩ := mem_sigma.mp (ih hargs)
    rw [app_map hvalue] at htail
    change snd (SemTele.tail vargs Δ) ∈ rest.ihArgSet block motive
      (Fin.snoc (SemTele.values γ vargs Δ) (fst (SemTele.tail vargs Δ)))
    rwa [heq, fst_pair, snd_pair]

end CtorCode

end Metalean
