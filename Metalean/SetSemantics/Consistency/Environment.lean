/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Soundness
public import Metalean.SetSemantics.Environment.Quot
public import Metalean.Typing.InstLevel

@[expose] public section

universe u

namespace Metalean

open CategoryTheory ZFSet

variable {ζ : Sigs}

def atomBelow {sig : Sig} (previous : Atom ζ 0 → ZFSet.{u}) :
    (Atom (.snoc ζ sig) 0 → ZFSet.{u}) →
    Atom (.snoc ζ sig) 0 → ZFSet.{u} :=
  fun fresh a => match a.unstep sig with
    | some old => previous old
    | none => fresh a

inductive Entry.Sound (pre : Env ζ) : {sig : Sig} → Entry ζ sig →
    (Atom (.snoc ζ sig) 0 → ZFSet.{u}) → Prop
  | axiom {nlevels : Nat} {type : Expr ζ nlevels 0} {ε}
    (mem : ∀ ls, ε (.const .here ls) ∈ ε[![]]⟦(type.map (.step .refl)).instL ls⟧) :
    Sound pre (.axiom type) ε
  | opaque {nlevels : Nat} {type : Expr ζ nlevels 0} {ε}
    (mem : ∀ ls, ε (.const .here ls) ∈ ε[![]]⟦(type.map (.step .refl)).instL ls⟧) :
    Sound pre (.opaque type) ε
  | def {nlevels : Nat} {type value : Expr ζ nlevels 0} {ε}
    (mem : ∀ ls, ε (.const .here ls) ∈ ε[![]]⟦(type.map (.step .refl)).instL ls⟧)
    (unfolds : ∀ ls, ε (.const .here ls) = ε[![]]⟦(value.map (.step .refl)).instL ls⟧) :
    Sound pre (.def type value) ε
  | inductive {ι : IndSig} {block : Inductive ζ ι} {ε}
    (sound : ∀ ls, ∃ w : InductiveModel.{u} ι,
      w.Sound (pre.snoc (.inductive block)) ε
        (block.map (.step .refl)) .here ls) :
    Sound pre (.inductive block) ε
  | quot {eqHead : Head ζ (.inductive Eq.sig)} {ε}
    (sound : Quot.RulesSound (pre.snoc (.quot eqHead)) ε .here) :
    Sound pre (.quot eqHead) ε

theorem atomBelow.map {sig : Sig} (ε : Atom ζ 0 → ZFSet.{u})
    (fresh : Atom (.snoc ζ sig) 0 → ZFSet.{u}) :
    AtomsMap (.step .refl : ζ ⟶ ζ.snoc sig) ε (atomBelow ε fresh) := by
  funext a
  change atomBelow ε fresh (a.map (.step .refl)) = _
  rw [atomBelow, Atom.unstep_map_step]

inductive Env.Sound : {ζ : Sigs} → Env ζ → (Atom ζ 0 → ZFSet.{u}) → Prop
  | nil {ε} : Sound .nil ε
  | snoc {ζ : Sigs} {sig : Sig} {pre : Env ζ} {entry : Entry ζ sig}
    {ε : Atom ζ 0 → ZFSet.{u}} {fresh : Atom (.snoc ζ sig) 0 → ZFSet.{u}}
    (previous : Sound pre ε)
    (latest : Entry.Sound pre entry (atomBelow ε fresh)) :
    Sound (pre.snoc entry) (atomBelow ε fresh)

structure Env.Model (E : Env ζ) where
  atoms : Atom ζ 0 → ZFSet.{u}
  sound : E.Sound atoms

def Env.Model.nil : Model.{u} .nil := ⟨fun _ => ∅, .nil⟩

def Env.Model.snoc {pre : Env ζ} {sig : Sig} {entry : Entry ζ sig}
    (m : Model.{u} pre) (fresh : Atom (.snoc ζ sig) 0 → ZFSet.{u})
    (h : Entry.Sound pre entry (atomBelow m.atoms fresh)) : Model.{u} (pre.snoc entry) :=
  ⟨atomBelow m.atoms fresh, .snoc m.sound h⟩

theorem Env.Sound.constMem {E : Env ζ} {ε : Atom ζ 0 → ZFSet.{u}} (h : Env.Sound E ε)
    {kind : ConstKind} {nlevels : Nat} (η : Head ζ (.const kind nlevels))
    (ls : Fin nlevels → Level 0) :
    ε (.const η ls) ∈ ε[![]]⟦(E.get η).constType.instL ls⟧ := by
  induction h with
  | nil => nomatch η
  | @snoc ζ sig pre entry ε fresh previous latest ih =>
    cases η with
    | here =>
      cases latest with
      | «axiom» hmem => exact hmem ls
      | «opaque» hmem => exact hmem ls
      | «def» hmem _ => exact hmem ls
    | there η =>
      let step : pre.as ⟶ (pre.snoc entry).as := .step .refl
      have hatoms : AtomsMap step.sigs ε (atomBelow ε fresh) := atomBelow.map ε fresh
      change ε (.const η ls) ∈
        (atomBelow ε fresh)[![]]⟦((pre.get η).map step.sigs).constType.instL ls⟧
      rw [show ((pre.get η).map step.sigs).constType = (pre.get η).constType.map step.sigs from
        (Entry.constTypeNatTrans _ _).naturality_apply step.sigs (pre.get η),
        ← Expr.map_instL, Expr.denote_map _ hatoms]
      exact ih η

theorem Env.Sound.defEq {E : Env ζ} {ε : Atom ζ 0 → ZFSet.{u}} (h : Env.Sound E ε)
    {nlevels : Nat} (η : Head ζ (.const .def nlevels)) (ls : Fin nlevels → Level 0) :
    ε (.const η ls) = ε[![]]⟦(E.get η).defValue.instL ls⟧ := by
  induction h with
  | nil => nomatch η
  | @snoc ζ sig pre entry ε fresh previous latest ih =>
    cases η with
    | here =>
      have .def _ hunfolds := latest
      exact hunfolds ls
    | there η =>
      let step : pre.as ⟶ (pre.snoc entry).as := .step .refl
      have hatoms : AtomsMap step.sigs ε (atomBelow ε fresh) := atomBelow.map ε fresh
      change ε (.const η ls) =
        (atomBelow ε fresh)[![]]⟦((pre.get η).map step.sigs).defValue.instL ls⟧
      rw [show ((pre.get η).map step.sigs).defValue = (pre.get η).defValue.map step.sigs from
        (Entry.defValueNatTrans _).naturality_apply step.sigs (pre.get η),
        ← Expr.map_instL, Expr.denote_map _ hatoms]
      exact ih η

theorem Env.Sound.quotientRules {E : Env ζ} {ε : Atom ζ 0 → ZFSet.{u}}
    (h : Env.Sound E ε) (η : Head ζ .quot) :
    Quot.RulesSound E ε η := by
  induction h with
  | nil => nomatch η
  | @snoc ζ sig pre entry ε fresh previous latest ih =>
    cases η with
    | here =>
      have .quot hsound := latest
      exact hsound
    | there η => exact (ih η).map (.step .refl) (atomBelow.map ε fresh)

theorem Env.Sound.inductiveModel {E : Env ζ} {ι : IndSig} {ε : Atom ζ 0 → ZFSet.{u}}
    (h : Env.Sound E ε) (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Level 0) :
    ∃ w : InductiveModel.{u} ι,
      InductiveModel.Sound E ε (E.get η).block η ls w := by
  induction h with
  | nil => nomatch η
  | @snoc ζ sig pre entry ε fresh previous latest ih =>
    cases η with
    | here =>
      have .inductive hsound := latest
      exact hsound ls
    | there η =>
      have ⟨w, hmodel⟩ := ih η
      rw [Env.get, Entry.block_map]
      exact ⟨w, hmodel.map (.step .refl) (atomBelow.map ε fresh)⟩

theorem Env.Sound.inductiveRules {E : Env ζ} {ι : IndSig} {ε : Atom ζ 0 → ZFSet.{u}}
    (h : Env.Sound E ε) (η : Head ζ (.inductive ι))
    (ls : Fin ι.nlevels → Level 0) :
    Inductive.RulesSound E ε η ls :=
  have ⟨_, hmodel⟩ := h.inductiveModel η ls
  hmodel.rules

theorem InductiveModel.Sound.uniqueCtor_of_mem_sort {ι : IndSig} {E : Env ζ}
    {ε : Atom ζ 0 → ZFSet.{u}} {I : Inductive ζ ι} {η : Head ζ (.inductive ι)}
    {ls : Fin ι.nlevels → Level 0} {w : InductiveModel.{u} ι}
    (h : InductiveModel.Sound E ε I η ls w) (hlevel : w.level = 0)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (hs : ∀ s₁ : Fin ι.nsorts, s₁ = s) (hc : ∀ c₁ : Fin (ι.nctors s), c₁ = c)
    {vps : Slots ι.nparams} {vis : Slots (ι.nindices s)} {raw : ZFSet.{u}}
    (hraw : raw ∈ ε (.ind η s ls vps vis)) :
    ∃ vargs, vargs ∈ (w.codes s c).argSet (w.block vps) vps ∧
      (w.codes s c).targetIndex vps vargs = sortKey s.val (encode vis) := by
  rw [h.sortAtom, InductiveModel.sortValue, hlevel] at hraw
  have ⟨value, hvalue, _⟩ := mem_squash.mp hraw
  exact h.uniqueCtor_of_mem_fibre s c hs hc vps hvalue

theorem Env.Model.semDecls {E : Env ζ} (m : Env.Model.{u} E) :
    SemDecls E m.atoms ![] :=
  fun η ls => m.sound.constMem η ls

theorem Env.Model.semDeclRules {E : Env ζ} (m : Env.Model.{u} E) :
    SemDeclRules E m.atoms ![] :=
  have hatoms : AtomsMap (𝟙 ζ) m.atoms m.atoms :=
    funext fun a => congrArg m.atoms ((Atom.functor _).map_id_apply _ a)
  { ind _ := (m.sound.inductiveRules _ _).ind .refl hatoms
    ctor _ := (m.sound.inductiveRules _ _).ctor .refl hatoms
    recr _ := (m.sound.inductiveRules _ _).recr .refl hatoms
    quot _ := (m.sound.quotientRules _).quot .refl hatoms
    quotMk _ := (m.sound.quotientRules _).quotMk .refl hatoms
    quotLift _ := (m.sound.quotientRules _).quotLift .refl hatoms
    quotInd _ := (m.sound.quotientRules _).quotInd .refl hatoms
    quotIota _ := (m.sound.quotientRules _).quotIota .refl hatoms
    iota _ := (m.sound.inductiveRules _ _).iota .refl hatoms
    delta := fun {_ _ _ η ls} _ =>
      ⟨by simpa! using m.sound.defEq η ls, by simpa! using m.sound.constMem η ls⟩
    etaStruct hstruct _ := (m.sound.inductiveRules _ _).etaStruct .refl hatoms hstruct }

def Env.Model.addConst {pre : Env ζ} {kind : ConstKind} {nlevels : Nat}
    {entry : Entry ζ (.const kind nlevels)} (m : Model.{u} pre)
    (v : (Fin nlevels → Level 0) → ZFSet.{u})
    (hsound : ∀ ε : Atom (.snoc ζ (.const kind nlevels)) 0 → ZFSet.{u},
      AtomsMap (.step .refl) m.atoms ε →
      (∀ ls, ε (.const .here ls) = v ls) →
      Entry.Sound pre entry ε) : Model.{u} (pre.snoc entry) :=
  let fresh : Atom (.snoc ζ (.const kind nlevels)) 0 → ZFSet.{u}
    | .const .here ls => v ls
    | _ => ∅
  m.snoc fresh (hsound _ (atomBelow.map m.atoms fresh) fun _ => rfl)

noncomputable def Env.Model.addAxiom {pre : Env ζ} {nlevels : Nat}
    {type : Expr ζ nlevels 0} (m : Model.{u} pre)
    (hvalid : ∀ ls, ∃ v, v ∈ m.atoms[![]]⟦type.instL ls⟧) :
    Model.{u} (pre.snoc (.axiom type)) := by
  apply m.addConst fun ls => (hvalid ls).choose
  intro ε hatoms hvalue
  refine .axiom fun ls => ?_
  rw [hvalue, ← Expr.map_instL, Expr.denote_map _ hatoms]
  exact (hvalid ls).choose_spec

noncomputable def Env.Model.addOpaque {pre : Env ζ} {ℓ : Nat}
    {t : Expr ζ ℓ 0} (m : Model.{u} pre) (hE : EnvWF pre)
    (hwf : EntryWF pre (.opaque t)) : Model.{u} (pre.snoc (.opaque t)) := by
  have hex : ∃ e, pre[.nil] ⊢ e : t :=
    have @EntryWF.opaque _ _ _ e _ heq _ := hwf
    ⟨e, heq⟩
  apply m.addConst (m.atoms[![]]⟦hex.choose.instL ·⟧)
  intro ε hatoms heq
  refine .opaque fun ls => ?_
  rw [heq, ← Expr.map_instL, Expr.denote_map _ hatoms]
  exact (soundness m.semDecls m.semDeclRules hE (hex.choose_spec.instLevel ls) ![] .nil).mem

noncomputable def Env.Model.addDef {pre : Env ζ} {ℓ : Nat}
    {t e : Expr ζ ℓ 0} (m : Model.{u} pre) (hE : EnvWF pre)
    (hwf : EntryWF pre (.def t e)) : Model.{u} (pre.snoc (.def t e)) := by
  apply m.addConst (m.atoms[![]]⟦e.instL ·⟧)
  intro ε hatoms heq
  refine .def (fun ls => ?_) fun ls => ?_
  · have .def _ htyped := hwf
    rw [heq, ← Expr.map_instL, Expr.denote_map _ hatoms]
    exact (soundness m.semDecls m.semDeclRules hE (htyped.instLevel ls) ![] .nil).mem
  · rw [heq, ← Expr.map_instL, Expr.denote_map _ hatoms]

end Metalean
