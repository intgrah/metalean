/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Environment.Inductive.Model

@[expose] public section

universe u

namespace Metalean

open CategoryTheory ZFSet

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{u}} {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
  {ι : IndSig} {I : Inductive ζ₁ ι} {η : Head ζ₁ (.inductive ι)}
  {ls : Fin ι.nlevels → Level 0} {witness : InductiveModel.{u} ι}

structure Inductive.RulesSound (E₁ : Env ζ₁) (ε₁ : Atom ζ₁ 0 → ZFSet.{u})
    (η : Head ζ₁ (.inductive ι)) (ls : Fin ι.nlevels → Level 0) : Prop where
  ind {ζ₂ : Sigs} {E₂ : Env ζ₂}
      {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
      (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
      {n : Nat} {γ : Slots n}
      {s : Fin ι.nsorts}
      {ps₁ ps₂ : Fin ι.nparams → Expr ζ₂ 0 n}
      {is₁ is₂ : Fin (ι.nindices s) → Expr ζ₂ 0 n}
      (hps : ∀ param, ε₂[γ] ⊨ ps₁ param ≡ ps₂ param :
        (E₂.get (η.map pre.sigs)).block.paramType ls ps₁ param)
      (his : ∀ index, ε₂[γ] ⊨ is₁ index ≡ is₂ index :
        (E₂.get (η.map pre.sigs)).block.indexType ls s ps₁ is₁ index) :
      ε₂[γ] ⊨ .ind (η.map pre.sigs) s ls ps₁ is₁ ≡
        .ind (η.map pre.sigs) s ls ps₂ is₂ :
        .sort ((E₂.get (η.map pre.sigs)).block.level.inst ls)
  ctor {ζ₂ : Sigs} {E₂ : Env ζ₂}
      {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
      (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
      {n : Nat} {γ : Slots n}
      {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
      {ps₁ ps₂ : Fin ι.nparams → Expr ζ₂ 0 n}
      {fds₁ fds₂ : Fin (ι.ctors s c).nfields → Expr ζ₂ 0 n}
      {recFds₁ recFds₂ : Fin (ι.ctors s c).nrecFields → Expr ζ₂ 0 n}
      (hps : ∀ param, ε₂[γ] ⊨ ps₁ param ≡ ps₂ param :
        (E₂.get (η.map pre.sigs)).block.paramType ls ps₁ param)
      (hfields : ∀ f, ε₂[γ] ⊨ fds₁ f ≡ fds₂ f :
        ((((E₂.get (η.map pre.sigs)).block.ctors s c).ordinaryType f).instL ls).subst
          (Fin.append ps₁ fun previous : Fin f.val => fds₁ (previous.castLE f.isLt.le)))
      (hrecFields : ∀ f, ε₂[γ] ⊨ recFds₁ f ≡ recFds₂ f :
        (((E₂.get (η.map pre.sigs)).block.ctors s c).recursive f).instantiatedType
          (η.map pre.sigs) ls ps₁ (Fin.append ps₁ fds₁)) :
      ε₂[γ] ⊨ .ctor (η.map pre.sigs) s c ls ps₁ fds₁ recFds₁ ≡
        .ctor (η.map pre.sigs) s c ls ps₂ fds₂ recFds₂ :
        .ind (η.map pre.sigs) s ls ps₁ fun index =>
          ((E₂.get (η.map pre.sigs)).block.ctors s c).targetIndex
            ls ps₁ fds₁ index
  recr {ζ₂ : Sigs} {E₂ : Env ζ₂}
      {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
      (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
      {n : Nat} {γ : Slots n}
      {s : Fin ι.nsorts}
      {l : Level 0} {ps₁ ps₂ : Fin ι.nparams → Expr ζ₂ 0 n}
      {ms₁ ms₂ : Fin ι.nsorts → Expr ζ₂ 0 n}
      {mins₁ mins₂ : (s : Fin ι.nsorts) →
        Fin (ι.nctors s) → Expr ζ₂ 0 n}
      {is₁ is₂ : Fin (ι.nindices s) → Expr ζ₂ 0 n}
      {maj₁ maj₂ : Expr ζ₂ 0 n}
      (hallowed : (E₂.get (η.map pre.sigs)).block.RecAllowed l)
      (hps : ∀ param, ε₂[γ] ⊨ ps₁ param ≡ ps₂ param :
        (E₂.get (η.map pre.sigs)).block.paramType ls ps₁ param)
      (hms : ∀ s, ε₂[γ] ⊨ ms₁ s ≡ ms₂ s :
        (E₂.get (η.map pre.sigs)).block.motiveType
          (η.map pre.sigs) ls ps₁ l s)
      (hmins : ∀ s c, ε₂[γ] ⊨ mins₁ s c ≡ mins₂ s c :
        (E₂.get (η.map pre.sigs)).block.caseFnType
          (η.map pre.sigs) ls ps₁ ms₁ s c)
      (his : ∀ index, ε₂[γ] ⊨ is₁ index ≡ is₂ index :
        (E₂.get (η.map pre.sigs)).block.indexType
          ls s ps₁ is₁ index)
      (hmaj : ε₂[γ] ⊨ maj₁ ≡ maj₂ :
        .ind (η.map pre.sigs) s ls ps₁ is₁) :
      ε₂[γ] ⊨ .recr (η.map pre.sigs) s ls l ps₁ ms₁ mins₁ is₁ maj₁ ≡
        .recr (η.map pre.sigs) s ls l ps₂ ms₂ mins₂ is₂ maj₂ :
        Inductive.motiveResult (ms₁ s) is₁ maj₁
  iota {ζ₂ : Sigs} {E₂ : Env ζ₂}
      {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
      (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
      {n : Nat} {γ : Slots n}
      {l : Level 0} {ps : Fin ι.nparams → Expr ζ₂ 0 n}
      {ms : Fin ι.nsorts → Expr ζ₂ 0 n}
      {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ₂ 0 n}
      {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
      {fds : Fin (ι.ctors s c).nfields → Expr ζ₂ 0 n}
      {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ₂ 0 n}
      (hallowed : (E₂.get (η.map pre.sigs)).block.RecAllowed l)
      (hps : ∀ param, ε₂[γ] ⊨ ps param ≡ ps param :
        (E₂.get (η.map pre.sigs)).block.paramType ls ps param)
      (hms : ∀ s, ε₂[γ] ⊨ ms s ≡ ms s :
        (E₂.get (η.map pre.sigs)).block.motiveType (η.map pre.sigs) ls ps l s)
      (hmins : ∀ s c, ε₂[γ] ⊨ mins s c ≡ mins s c :
        (E₂.get (η.map pre.sigs)).block.caseFnType (η.map pre.sigs) ls ps ms s c)
      (hfields : ∀ f, ε₂[γ] ⊨ fds f ≡ fds f :
        ((((E₂.get (η.map pre.sigs)).block.ctors s c).ordinaryType f).instL ls).subst
          (Fin.append ps fun previous : Fin f.val =>
            fds (previous.castLE f.isLt.le)))
      (hrecFields : ∀ f, ε₂[γ] ⊨ recFds f ≡ recFds f :
        (((E₂.get (η.map pre.sigs)).block.ctors s c).recursive f).instantiatedType
          (η.map pre.sigs) ls ps (Fin.append ps fds)) :
      ε₂[γ] ⊨ (E₂.get (η.map pre.sigs)).block.iotaLhs (η.map pre.sigs) ls l
          ps ms mins s c fds recFds ≡
        (E₂.get (η.map pre.sigs)).block.iotaRhs (η.map pre.sigs) ls l
          ps ms mins s c fds recFds :
        (E₂.get (η.map pre.sigs)).block.iotaType (η.map pre.sigs) ls
          ps ms s c fds recFds
  etaStruct {ζ₂ : Sigs} {E₂ : Env ζ₂}
      {ε₂ : Atom ζ₂ 0 → ZFSet.{u}}
      (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂)
      {n : Nat} {γ : Slots n}
      {s : Fin ι.nsorts} {c : Fin (ι.nctors s)}
      {ps : Fin ι.nparams → Expr ζ₂ 0 n}
      {is : Fin (ι.nindices s) → Expr ζ₂ 0 n} {maj : Expr ζ₂ 0 n}
      (hstruct : (E₂.get (η.map pre.sigs)).block.IsStructure s c) :
      (∀ param, ε₂[γ] ⊨ ps param ≡ ps param :
        (E₂.get (η.map pre.sigs)).block.paramType ls ps param) →
      ε₂[γ] ⊨ maj ≡ maj : .ind (η.map pre.sigs) s ls ps is →
      ε₂[γ] ⊨ hstruct.rebuildTerm (η.map pre.sigs) ls ps maj ≡ maj :
        .ind (η.map pre.sigs) s ls ps is

theorem Inductive.RulesSound.map (h : Inductive.RulesSound E₁ ε₁ η ls)
    (pre : E₁.as ⟶ E₂.as) (hatoms₁ : AtomsMap pre.sigs ε₁ ε₂) :
    Inductive.RulesSound E₂ ε₂ (η.map pre.sigs) ls :=
  have hmap {ζ₃ : Sigs} {E₃ : Env ζ₃} (suffix : E₂.as ⟶ E₃.as) :
      (η.map pre.sigs).map suffix.sigs = η.map (pre ≫ suffix).sigs :=
    ((Env.forget ⋙ Head.functor _).map_comp_apply pre suffix η).symm
  have hcomp {ζ₃ : Sigs} {E₃ : Env ζ₃} {ε₃ : Atom ζ₃ 0 → ZFSet.{u}}
      (suffix : E₂.as ⟶ E₃.as) (hatoms₂ : AtomsMap suffix.sigs ε₂ ε₃) :
      AtomsMap (pre ≫ suffix).sigs ε₁ ε₃ := by
    simpa [dsimp% Env.forget.map_comp pre suffix] using hatoms₁.trans hatoms₂
  { ind := fun {ζ₃ E₃ ε₃} suffix hatoms₂ {n γ s ps₁ ps₂ is₁ is₂} hps his => by
        simp [hmap suffix] at hps his
        simpa [hmap suffix] using h.ind (pre ≫ suffix) (hcomp suffix hatoms₂) hps his
    ctor := fun {ζ₃ E₃ ε₃} suffix hatoms₂ {n γ s c ps₁ ps₂ fds₁ fds₂ recFds₁ recFds₂}
      hps hfields hrecFields => by
        simp [hmap suffix] at hps hfields hrecFields
        simpa [hmap suffix] using h.ctor (pre ≫ suffix) (hcomp suffix hatoms₂)
          hps hfields hrecFields
    recr := fun {ζ₃ E₃ ε₃} suffix hatoms₂ {n γ s l ps₁ ps₂ ms₁ ms₂ mins₁ mins₂ is₁ is₂ maj₁ maj₂}
      hallowed hps hms hmins his hmaj => by
        simp [hmap suffix] at hallowed hps hms hmins his hmaj
        simpa [hmap suffix] using h.recr (pre ≫ suffix) (hcomp suffix hatoms₂)
          hallowed hps hms hmins his hmaj
    iota := fun {ζ₃ E₃ ε₃} suffix hatoms₂ {n γ l ps ms mins s c fds recFds}
      hallowed hps hms hmins hfields hrecFields => by
        simp [hmap suffix] at hallowed hps hms hmins hfields hrecFields
        simpa [hmap suffix] using h.iota (pre ≫ suffix) (hcomp suffix hatoms₂)
          hallowed hps hms hmins hfields hrecFields
    etaStruct := fun {ζ₃ E₃ ε₃} suffix hatoms₂ {n γ s c ps is maj} hstruct hps hmaj => by
        generalize hη : (η.map pre.sigs).map suffix.sigs = η₃ at hstruct hps hmaj ⊢
        rw [hmap suffix] at hη
        subst hη
        exact h.etaStruct (pre ≫ suffix) (hcomp suffix hatoms₂) hstruct hps hmaj }

structure InductiveModel.Sound (E₁ : Env ζ₁) (ε : Atom ζ₁ 0 → ZFSet.{u})
    (I : Inductive ζ₁ ι) (η : Head ζ₁ (.inductive ι))
    (ls : Fin ι.nlevels → Level 0) (witness : InductiveModel.{u} ι) : Prop where
  block_eq : (E₁.get η).block = I
  realizes : witness.Interprets ε zeroNs I η ls
  sortAtom (s : Fin ι.nsorts) (vps : Slots ι.nparams) (vis : Slots (ι.nindices s)) :
    ε (.ind η s ls vps vis) = witness.sortValue s vps vis
  rules : Inductive.RulesSound E₁ ε η ls

namespace InductiveModel.Sound

theorem uniqueCtor_of_mem_fibre (h : InductiveModel.Sound E₁ ε₁ I η ls witness)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    (hs : ∀ s₁ : Fin ι.nsorts, s₁ = s)
    (hc : ∀ c₁ : Fin (ι.nctors s), c₁ = c)
    (vps : Slots ι.nparams) {key raw : ZFSet.{u}}
    (hraw : raw ∈ fibreOp (witness.block vps) key) :
    ∃ vargs, vargs ∈ (witness.codes s c).argSet (witness.block vps) vps ∧
      (witness.codes s c).targetIndex vps vargs = key := by
  have hentry := mem_fibre.mp hraw
  unfold InductiveModel.block at hentry
  rw [← indSet_unfold (h.realizes.bounded vps)] at hentry
  have ⟨s₁, c₁, vargs, hargs, hentryEq⟩ := mem_indOp.mp hentry
  obtain rfl := hs s₁
  obtain rfl := hc c₁
  exact ⟨vargs, hargs, by simpa [entry_eq] using congrArg fst hentryEq⟩

theorem map
    (h : InductiveModel.Sound E₁ ε₁ I η ls witness)
    (pre : E₁.as ⟶ E₂.as) (hatoms : AtomsMap pre.sigs ε₁ ε₂) :
    InductiveModel.Sound E₂ ε₂ (I.map pre.sigs) (η.map pre.sigs) ls witness where
  block_eq := by
    simpa [dsimp% (Env.lookup _).naturality_apply pre η] using
      congrArg (Inductive.map pre.sigs) h.block_eq
  realizes := h.realizes.map pre hatoms
  sortAtom s vps vis := (congrFun hatoms _).trans (h.sortAtom s vps vis)
  rules := h.rules.map pre hatoms

end InductiveModel.Sound

end Metalean
