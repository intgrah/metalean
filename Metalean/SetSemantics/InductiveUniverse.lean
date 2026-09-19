/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.InductiveBlock
public import Metalean.SetTheory.ZFC.SmallSupport
import Metalean.Grind
import Metalean.SetTheory.ZFC.AczelUniverse

public section

universe u

namespace Metalean

open ZFSet

attribute [local instance 2000] Classical.allZFSetDefinable

variable {a b n m level : Nat} {nctors : Fin m → Nat}

theorem fibreOp_subset_type {block : ZFSet} (h : block ⊆ U_ level) (key : ZFSet) :
    fibreOp block key ⊆ U_ level := fun _ he => by
  have h' := snd_mem_type (h (mem_fibre.mp he))
  rwa [snd_pair] at h'

abbrev SemTele.DomsIn (level : Nat) {a b : Nat} (Δ : SemTele a b) : Prop :=
  Tele.Forall (fun _ domain => ∀ γ, domain γ ∈ U_ level) Δ

inductive CtorCode.DomsIn (level : Nat) :
    {n : Nat} → CtorCode n → Prop
  | target {n : Nat} {index : Dom n} :
    DomsIn level (.target index)
  | arg {n : Nat} {domain : Dom n} {rest : CtorCode (n + 1)} :
    (∀ γ : Slots n, domain γ ∈ U_ level) →
    DomsIn level rest →
    DomsIn level (.arg domain rest)
  | recArg {n b : Nat} {tele : SemTele n b} {index : Dom b}
      {rest : CtorCode n} :
    tele.DomsIn level →
    DomsIn level rest →
    DomsIn level (.recArg tele index rest)

theorem SemTele.DomsIn.mono {level level' : Nat} (hle : level ≤ level')
    {tele : SemTele a b} (h : tele.DomsIn level) : tele.DomsIn level' := by
  induction h <;> constructor <;> solve_by_elim [type_mono]

theorem SemTele.DomsIn.append {d : Nat} {base : SemTele a b}
    {extension : SemTele b d} (hbase : base.DomsIn level) :
    extension.DomsIn level →
    SemTele.DomsIn level (base ++ extension)
  | .nil => hbase
  | .snoc htele hdomain => .snoc (append hbase htele) hdomain

theorem CtorCode.DomsIn.mono {level level' : Nat} (hle : level ≤ level')
    {n : Nat} {code : CtorCode n} :
    code.DomsIn level →
    code.DomsIn level'
  | .target => .target
  | .arg hdomain hrest => .arg (fun γ => type_mono hle (hdomain γ)) (mono hle hrest)
  | .recArg htele hrest => .recArg (htele.mono hle) (mono hle hrest)

theorem CtorCode.DomsIn.prependOrdinary {Δ : SemTele n b} (hΔ : Δ.DomsIn level)
    {rest : CtorCode b} (hrest : rest.DomsIn level) :
    (CtorCode.prependOrdinary Δ rest).DomsIn level := by
  induction hΔ with
  | nil => exact hrest
  | snoc _ hdomain ih => exact ih (.arg hdomain hrest)

theorem CtorCode.DomsIn.prependRecursive {n count : Nat}
    {fields : Fin count → CtorRecCode.Packed n}
    (hfields : ∀ f, (fields f).2.tele.DomsIn level)
    {rest : CtorCode n} (hrest : rest.DomsIn level) :
    (CtorCode.prependRecursive count fields rest).DomsIn level := by
  induction count with
  | zero => exact hrest
  | succ count ih =>
    exact .recArg (hfields 0) (ih fun f => hfields f.succ)

theorem SemTele.pi_mem_type {Δ : SemTele a b} (hdoms : Δ.DomsIn level)
    {cod : Dom b} (hcod : ∀ γ : Slots b, cod γ ∈ U_ level) (γ : Slots a) :
    Δ.pi cod γ ∈ U_ level := by
  induction hdoms with
  | nil => exact hcod γ
  | snoc _ hdomain ih =>
    refine ih fun s => ?_
    refine piMap_mem_type (hdomain s) fun d hd => ?_
    rw [app_map hd]
    exact hcod _

theorem SemTele.support_mem_type {Δ : SemTele a b} (hdoms : Δ.DomsIn level)
    {leaf : Dom b} (hleaf : ∀ γ : Slots b, leaf γ ∈ U_ level)
    (γ : Slots a) : Δ.support leaf γ ∈ U_ level := by
  induction hdoms with
  | nil => exact hleaf γ
  | snoc _ hdomain ih => exact ih fun current => by grind only [zfBounds]

theorem SemTele.pi_subset_type {Δ : SemTele a b} (hdoms : Δ.DomsIn level)
    {cod : Dom b} (hcod : ∀ γ : Slots b, cod γ ⊆ U_ level) (γ : Slots a) :
    Δ.pi cod γ ⊆ U_ level := by
  induction hdoms with
  | nil => exact hcod γ
  | snoc _ hdomain ih =>
    refine ih fun s f hf => ?_
    refine type_mem_of_mem_piMap (hdomain s) hf fun d hd => ?_
    have hv := Aczel.app_mem hf hd
    rw [app_map hd] at hv
    exact hcod _ hv

theorem recFieldSet_subset_type {Δ : SemTele n b} (hdoms : Δ.DomsIn level)
    {index : Dom b} {block : ZFSet} (hblock : ∀ key, fibreOp block key ⊆ U_ level)
    (γ : Slots n) : recFieldSet Δ index block γ ⊆ U_ level :=
  Δ.pi_subset_type hdoms (fun s => hblock (index s)) γ

theorem recFieldSet_mem_type {Δ : SemTele n b} (hdoms : Δ.DomsIn level)
    {index : Dom b} {block : ZFSet} (hblock : ∀ key, fibreOp block key ∈ U_ level)
    (γ : Slots n) : recFieldSet Δ index block γ ∈ U_ level :=
  Δ.pi_mem_type hdoms (fun current => hblock (index current)) γ

theorem CtorCode.support_mem_type {code : CtorCode n}
    (hdoms : code.DomsIn level) (γ : Slots n) : code.support γ ∈ U_ level := by
  induction hdoms with
  | target => exact empty_mem_type
  | arg hdomain _ ih =>
    simp only [CtorCode.support]
    grind only [zfBounds]
  | recArg htele _ ih =>
    have htele' := SemTele.support_mem_type htele (fun _ => singleton_mem_type empty_mem_type) γ
    simp only [CtorCode.support]
    grind only [zfBounds]

theorem CtorCode.argSet_mem_type {code : CtorCode n}
    (hdoms : code.DomsIn level) {block : ZFSet}
    (hblock : ∀ key, fibreOp block key ∈ U_ level) (γ : Slots n) :
    code.argSet block γ ∈ U_ level := by
  induction hdoms with
  | target => exact singleton_mem_type empty_mem_type
  | arg hdomain _ ih =>
    simp only [CtorCode.argSet]
    grind only [zfBounds]
  | recArg htele _ ih =>
    simp only [CtorCode.argSet]
    grind only [zfBounds, recFieldSet_mem_type htele hblock γ]

abbrev CodesDomsIn (level : Nat) (codes : (s : Fin m) → Fin (nctors s) → CtorCode n) : Prop :=
  ∀ s c, (codes s c).DomsIn level

noncomputable def blockSupport (codes : (s : Fin m) → Fin (nctors s) → CtorCode.{u} n)
    (γ : Slots n) : ZFSet.{u} :=
  ⋃₀ range fun s => range fun c => (codes s c).support γ

theorem support_mem_blockSupport (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (γ : Slots n) (s : Fin m) (c : Fin (nctors s)) :
    (codes s c).support γ ∈ blockSupport codes γ :=
  mem_sUnion.mpr ⟨_, mem_range_self (f := fun s => range fun c => (codes s c).support γ) s,
    mem_range_self (f := fun c => (codes s c).support γ) c⟩

theorem blockSupport_mem_type (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (hdoms : CodesDomsIn level codes) (γ : Slots n) : blockSupport codes γ ∈ U_ level :=
  sUnion_mem_type (range_mem_type fun s => range_mem_type fun c =>
    CtorCode.support_mem_type (hdoms s c) γ)

theorem image_snd_indOp_mem_type (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (hdoms : CodesDomsIn level codes)
    {block : ZFSet} (hblock : ∀ key, fibreOp block key ∈ U_ level)
    (γ : Slots n) : image snd (indOp codes γ block) ∈ U_ level := by
  have hvalues (s : Fin m) (c : Fin (nctors s)) :
      image (entryValue (tagOf s c)) ((codes s c).argSet block γ) ∈ U_ level :=
    have hargs := CtorCode.argSet_mem_type (hdoms s c) hblock γ
    image_mem_type hargs fun vargs hvargs =>
      pair_mem_type (numeral_mem_type level _) (mem_type_of_mem hargs hvargs)
  refine mem_type_of_subset
    (y := tagGraph (fun code => code.argSet block γ) (fun _ tag => entryValue tag) codes)
    (sUnion_mem_type (range_mem_type fun s => sUnion_mem_type (range_mem_type (hvalues s))))
    fun value hvalue => ?_
  have ⟨entry', hentry, heq⟩ := mem_image.mp hvalue
  have ⟨s, c, vargs, hargs, hentry'⟩ := mem_indOp.mp hentry
  refine mem_tagGraph.mpr ⟨s, c, vargs, hargs, ?_⟩
  rw [← heq, ← hentry', entry_eq, snd_pair]

noncomputable def bodyOp (codes : (s : Fin m) → Fin (nctors s) → CtorCode n) (bound : ZFSet)
    (γ : Slots n) (body : ZFSet) : ZFSet :=
  image snd (indOp codes γ (prod bound body))

theorem bodyOp_mono {codes : (s : Fin m) → Fin (nctors s) → CtorCode n} {bound : ZFSet}
    {γ : Slots n} {body body' : ZFSet} (h : body ⊆ body') :
    bodyOp codes bound γ body ⊆ bodyOp codes bound γ body' := by
  intro value hvalue
  have ⟨entry', hentry, heq⟩ := mem_image.mp hvalue
  refine mem_image.mpr ⟨entry', indOp_mono ?_ hentry, heq⟩
  intro member hmember
  have ⟨key, hkey, value', hvalue', hpair⟩ := mem_prod.mp hmember
  exact mem_prod.mpr ⟨key, hkey, value', h hvalue', hpair⟩

theorem bodyOp_mem_type {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    (hdoms : CodesDomsIn level codes)
    (bound : ZFSet) (γ : Slots n) {body : ZFSet} (hbody : body ∈ U_ level) :
    bodyOp codes bound γ body ∈ U_ level :=
  image_snd_indOp_mem_type codes hdoms (fun _ =>
    mem_type_of_subset hbody fun _ hvalue =>
      (pair_mem_prod.mp (mem_fibre.mp hvalue)).2) γ

theorem image_snd_indOp_support (codes : (s : Fin m) → Fin (nctors s) → CtorCode n)
    (bound : ZFSet) (γ : Slots n) {body value : ZFSet}
    (hvalue : value ∈ image snd (indOp codes γ (prod bound body))) :
    ∃ small, small ⊆ body ∧ SmallOver (blockSupport codes γ) small ∧
      value ∈ image snd (indOp codes γ (prod bound small)) := by
  have ⟨entry', hentry, heq⟩ := mem_image.mp hvalue
  have ⟨s, c, vargs, hargs, hentry'⟩ := mem_indOp.mp hentry
  let code := codes s c
  let small :=
    (image (fun point => snd (code.readSupport γ vargs point))
      (code.support γ)).sep fun member => member ∈ body
  refine ⟨small, fun member hmember => (mem_sep.mp hmember).2, ⟨code.support γ,
      support_mem_blockSupport codes γ s c,
      fun point => snd (code.readSupport γ vargs point),
      fun _ hmember => (mem_sep.mp hmember).1⟩, ?_⟩
  have hargs' : vargs ∈ code.argSet (prod bound small) γ := by
    apply code.argSet_mem_of_support γ vargs hargs
    intro point hpoint hmember
    have ⟨key, hkey, member, hbody, hpair⟩ := mem_prod.mp hmember
    have hsnd : snd (code.readSupport γ vargs point) = member := by
      rw [hpair, snd_pair]
    have hbody' : snd (code.readSupport γ vargs point) ∈ small :=
      mem_sep.mpr ⟨mem_image.mpr ⟨point, hpoint, rfl⟩, hsnd ▸ hbody⟩
    exact mem_prod.mpr ⟨key, hkey, member, hsnd ▸ hbody', hpair⟩
  exact mem_image.mpr ⟨entry', mem_indOp.mpr ⟨s, c, vargs, hargs', hentry'⟩, heq⟩

theorem exists_bodyOp_closed {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    (hdoms : CodesDomsIn level codes)
    (bound : ZFSet) (γ : Slots n) :
    ∃ body, body ∈ U_ level ∧ bodyOp codes bound γ body ⊆ body :=
  exists_closed_of_smallSupport (fun _ _ h => bodyOp_mono h)
    (fun _ hbody => bodyOp_mem_type hdoms bound γ hbody)
    (blockSupport_mem_type codes hdoms γ)
    fun _ _ hvalue => image_snd_indOp_support codes bound γ hvalue

theorem fibreOp_indSet_mem_type_of_trap {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    {body : ZFSet} (hbody : body ∈ U_ level) (hbodyBound : body ⊆ U_ b)
    (γ : Slots n)
    (hclosed : indOp codes γ (prod (U_ b) body) ⊆ prod (U_ b) body)
    (key : ZFSet) : fibreOp (indSet codes (U_ b) γ) key ∈ U_ level := by
  have hproduct : prod (U_ b) body ⊆ U_ b := by
    intro entry' hentry
    have ⟨key', hkey, value, hvalue, hpair⟩ := mem_prod.mp hentry
    rw [hpair]
    exact pair_mem_type hkey (hbodyBound hvalue)
  have hind : indSet codes (U_ b) γ ⊆ prod (U_ b) body := lfp_least hproduct hclosed
  exact mem_type_of_subset hbody fun value hvalue =>
    (pair_mem_prod.mp (hind (mem_fibre.mp hvalue))).2

theorem fibreOp_indSet_mem_type {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    (hdoms : CodesDomsIn level codes)
    {slots : Slots n}
    (hmaps : Set.MapsTo (indOp codes slots) (Set.Iic (U_ b)) (Set.Iic (U_ b)))
    (key : ZFSet) : fibreOp (indSet codes (U_ b) slots) key ∈ U_ level := by
  have ⟨body, hbody, hclosed⟩ := exists_bodyOp_closed hdoms (U_ b) slots
  let boundedBody := body.sep fun value => value ∈ U_ b
  have hboundedBody : boundedBody ∈ U_ level := sep_mem_type hbody
  have hboundedBodyBound : boundedBody ⊆ U_ b := fun _ hvalue => (mem_sep.mp hvalue).2
  refine fibreOp_indSet_mem_type_of_trap hboundedBody hboundedBodyBound slots
    (fun entry' hentry => ?_) key
  have hcandidate : prod (U_ b) boundedBody ⊆ U_ b := by
    intro member hmember
    have ⟨key', hkey, value, hvalue, hpair⟩ := mem_prod.mp hmember
    rw [hpair]
    exact pair_mem_type hkey (hboundedBodyBound hvalue)
  have hentryBound : entry' ∈ U_ b := hmaps hcandidate hentry
  have hentryTrap : entry' ∈ indOp codes slots (prod (U_ b) body) := by
    apply indOp_mono _ hentry
    intro member hmember
    have ⟨key', hkey, value, hvalue, hpair⟩ := mem_prod.mp hmember
    exact mem_prod.mpr ⟨key', hkey, value, (mem_sep.mp hvalue).1, hpair⟩
  have hpair : entry' = pair (fst entry') (snd entry') := by
    have ⟨_, _, _, _, heq⟩ := mem_indOp.mp hentry
    simp [← heq, entry_eq]
  rw [hpair]
  exact pair_mem_prod.mpr ⟨fst_mem_type hentryBound,
    mem_sep.mpr ⟨hclosed (mem_image.mpr ⟨entry', hentryTrap, rfl⟩), snd_mem_type hentryBound⟩⟩

theorem CtorCode.argSet_subset_type {code : CtorCode n}
    (hdoms : code.DomsIn level)
    {block : ZFSet} (hblock : ∀ key, fibreOp block key ⊆ U_ level) (γ : Slots n) :
    argSet block code γ ⊆ U_ level := by
  intro t ht
  induction hdoms generalizing t with
  | target =>
    simp [argSet] at ht
    exact ht ▸ empty_mem_type
  | arg hdomain _ ih =>
    obtain ⟨value, hvalue, w, hw, rfl⟩ := mem_sigma.mp ht
    rw [app_map hvalue] at hw
    exact pair_mem_type (mem_type_of_mem (hdomain γ) hvalue) (ih _ hw)
  | recArg htele _ ih =>
    obtain ⟨value, hvalue, w, hw, rfl⟩ := mem_sigma.mp ht
    rw [app_map hvalue] at hw
    exact pair_mem_type (recFieldSet_subset_type htele hblock γ hvalue) (ih _ hw)

theorem indOp_subset_type {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    (hdoms : CodesDomsIn level codes)
    {block : ZFSet} (hblock : ∀ key, fibreOp block key ⊆ U_ level)
    (hindex : ∀ s c (γ : Slots n) vargs, (codes s c).targetIndex γ vargs ∈ U_ level)
    (γ : Slots n) : indOp codes γ block ⊆ U_ level := fun _ hz => by
  obtain ⟨s, c, vargs, hargs, rfl⟩ := mem_indOp.mp hz
  exact entry_mem_type (hindex s c γ vargs)
    (CtorCode.argSet_subset_type (hdoms s c) hblock γ hargs)

theorem indOp_mapsTo {codes : (s : Fin m) → Fin (nctors s) → CtorCode n}
    (hdoms : CodesDomsIn level codes)
    (hindex : ∀ s c (γ : Slots n) vargs, (codes s c).targetIndex γ vargs ∈ U_ level)
    (γ : Slots n) :
    Set.MapsTo (indOp codes γ) (Set.Iic (U_ level)) (Set.Iic (U_ level)) := fun _ hblock =>
  indOp_subset_type hdoms (fun key => fibreOp_subset_type hblock key) hindex γ

end Metalean
