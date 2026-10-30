/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.QuotientValue
public import Metalean.SetSemantics.Soundness

public section

universe v

namespace Metalean

open CategoryTheory ZFSet

variable {ζ₁ ζ₂ ζ₃ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {E₃ : Env ζ₃}
  {ε₁ : Atom ζ₁ 0 → ZFSet.{v}} {ε₂ : Atom ζ₂ 0 → ZFSet.{v}}

structure Quot.RulesSound (E₁ : Env ζ₁)
    (ε₁ : Atom ζ₁ 0 → ZFSet.{v}) (η : Head ζ₁ .quot) : Prop where
  quotAtom : ∀ (l : Level 0) (a r : ZFSet),
    ε₁ (.quot η l a r) = quotientCarrier (l.eval ![]) a r
  quotMkAtom : ∀ (l : Level 0) (a r x : ZFSet),
    ε₁ (.quotMk η l a r x) = quotientMk (l.eval ![]) a r x
  rules : ∀ {ζ₂ : Sigs} {E₂ : Env ζ₂} {ε₂ : Atom ζ₂ 0 → ZFSet.{v}}
    (pre : E₁.as ⟶ E₂.as), AtomsMap pre.sigs ε₁ ε₂ →
    Quot.SemRules ε₂ ![] (η.map pre.sigs) (E₂.get (η.map pre.sigs)).eqHead

private theorem denote_compatType {ε : Atom ζ₁ 0 → ZFSet.{v}}
    {n : Nat} (γ : Slots n) {η : Head ζ₁ (.inductive Eq.sig)} {l : Level 0}
    (α r β f : Expr ζ₁ 0 n) {equality : ZFSet → ZFSet → ZFSet → ZFSet}
    (hequality : ∀ b x y,
      ε (.ind η ⟨0, by decide⟩ (fun _ => l) ![b, x] ![y]) = equality b x y) :
    ε[γ]⟦Quot.compatType η l α r β f⟧ =
      quotientCompat equality ε[γ]⟦α⟧ ε[γ]⟦r⟧ ε[γ]⟦β⟧ ε[γ]⟦f⟧ := by
  have heq (b x y : ZFSet) : ε (.ind η 0 ![l] ![b, x] ![y]) = equality b x y := by
    simpa [Fin.const_fin_one] using hequality b x y
  simp! [quotientCompat, heq, Fin.fun_vecCons, Fin.fun_vecEmpty, Fin.const_fin_one]

private theorem denote_compatType_map {η : Head ζ₁ .quot}
    {pre : E₁.as ⟶ E₂.as} (hatoms : AtomsMap pre.sigs ε₁ ε₂)
    {equality : Level 0 → ZFSet → ZFSet → ZFSet → ZFSet}
    (hequality : ∀ l b xv yv, ε₁ (.ind (E₁.get η).eqHead ⟨0, by decide⟩ (fun _ => l)
      ![b, xv] ![yv]) = equality l b xv yv)
    {n : Nat} (γ : Slots n) (l : Level 0) (α r β f : Expr ζ₂ 0 n) :
    ε₂[γ]⟦Quot.compatType (E₂.get (η.map pre.sigs)).eqHead l α r β f⟧ =
      quotientCompat (equality l) ε₂[γ]⟦α⟧ ε₂[γ]⟦r⟧ ε₂[γ]⟦β⟧ ε₂[γ]⟦f⟧ :=
  denote_compatType γ α r β f fun b x y => by
    simpa! [dsimp% (Env.lookup .quot).naturality_apply pre η,
      dsimp% Entry.eqHeadNatTrans.naturality_apply] using
      (congrFun hatoms _).trans (hequality l b x y)

namespace Quot.RulesSound

theorem ofValues (η : Head ζ₁ .quot)
    (equality : Level 0 → ZFSet → ZFSet → ZFSet → ZFSet)
    (hseparates : ∀ l, EqualitySeparates (l.eval ![]) (equality l))
    (hequality : ∀ l b xv yv, ε₁ (.ind (E₁.get η).eqHead ⟨0, by decide⟩ (fun _ => l)
        ![b, xv] ![yv]) = equality l b xv yv)
    (hquot : ∀ l a r, ε₁ (.quot η l a r) = quotientCarrier (l.eval ![]) a r)
    (hquotMk : ∀ l a r x, ε₁ (.quotMk η l a r x) = quotientMk (l.eval ![]) a r x)
    (hquotLift : ∀ l₁ l₂ a r b fn h c, ε₁ (.quotLift η l₁ l₂ a r b fn h c) =
      quotientLiftResult (l₁.eval ![]) (l₂.eval ![]) fn c)
    (hquotInd : ∀ l a r motive minor c, ε₁ (.quotInd η l a r motive minor c) = proof) :
    Quot.RulesSound E₁ ε₁ η where
  quotAtom := hquot
  quotMkAtom := hquotMk
  rules {ζ₂ E₂ ε₂} pre hatoms :=
    { quot {_n γ l α α' r r'} hα hr := by
        refine ⟨?_, ?_⟩
        · simp! [hα.eq, hr.eq]
        · change (ε₂ ∘ Atom.map pre.sigs) (.quot η l _ _) ∈ _
          rw [hatoms, hquot]
          exact quotientCarrier_mem_sort hα.mem
      quotMk {_n γ l α α' r r' a₁ a₂} hα hr ha := by
        refine ⟨?_, ?_⟩
        · simp! [hα.eq, hr.eq, ha.eq]
        · change (ε₂ ∘ Atom.map pre.sigs) (.quotMk η l _ _ _) ∈
            (ε₂ ∘ Atom.map pre.sigs) (.quot η l _ _)
          rw [hatoms, hquotMk, hquot]
          exact quotientMk_mem ha.mem
      quotLift {_n γ l₁ l₂ α α' r r' β β' f f' h h' a₁ a₂} hα hr hβ hf hh ha := by
        refine ⟨?_, ?_⟩
        · simp! [hα.eq, hr.eq, hβ.eq, hf.eq, hh.eq, ha.eq]
        · have hhmem := hh.mem
          rw [denote_compatType_map hatoms hequality γ l₂ α r β f] at hhmem
          have hcmem := ha.mem
          change _ ∈ (ε₂ ∘ Atom.map pre.sigs) (.quot η l₁ _ _) at hcmem
          rw [hatoms, hquot] at hcmem
          change (ε₂ ∘ Atom.map pre.sigs) (.quotLift η l₁ l₂ _ _ _ _ _ _) ∈ _
          rw [hatoms, hquotLift]
          exact quotientLiftResult_mem (hseparates _) hα.mem hβ.mem
            (by simpa! [quotientArrow] using hf.mem) hhmem hcmem
      quotInd {_n γ l α α' r r' β β' f f' a₁ a₂} hα hr hβ hf ha := by
        refine ⟨?_, ?_⟩
        · simp! [hα.eq, hr.eq, hβ.eq, hf.eq, ha.eq]
        · have hq a r : ε₂ (.quot (η.map pre.sigs) l a r) =
              quotientCarrier (l.eval ![]) a r := (congrFun hatoms _).trans (hquot l a r)
          have hmk a r x : ε₂ (.quotMk (η.map pre.sigs) l a r x) =
              quotientMk (l.eval ![]) a r x := (congrFun hatoms _).trans (hquotMk l a r x)
          change (ε₂ ∘ Atom.map pre.sigs) (.quotInd η l _ _ _ _ _) ∈ _
          rw [hatoms, hquotInd]
          apply quotientIndResult_mem hα.mem
          · have hm := hβ.mem
            simp! [Quot.motiveType, hq] at hm
            exact hm
          · simpa! [Quot.minorType, Quot.minorQuotMk, hmk] using hf.mem
          · simpa! [hq] using ha.mem
      quotIota {_n γ l₁ l₂ α r β f h a} hα hr hβ hf hh ha hlift happ := by
        have hhmem := hh.mem
        rw [denote_compatType_map hatoms hequality γ l₂ α r β f] at hhmem
        have heq : ε₂[γ]⟦(.quotLift (η.map pre.sigs) l₁ l₂ α r β f h
            (.quotMk (η.map pre.sigs) l₁ α r a) : Expr ζ₂ 0 _)⟧ =
              ε₂[γ]⟦f.app a⟧ := by
          change (ε₂ ∘ Atom.map pre.sigs)
            (.quotLift η l₁ l₂ _ _ _ _ _
              ((ε₂ ∘ Atom.map pre.sigs) (.quotMk η l₁ _ _ _))) = _
          rw [hatoms, hquotMk, hquotLift]
          exact quotientLiftResult_mk (hseparates _) hα.mem hβ.mem
            (by simpa! [quotientArrow] using hf.mem) hhmem ha.mem
        exact ⟨heq, heq.symm ▸ happ.mem⟩ }

theorem map {η : Head ζ₁ .quot} (pre : E₁.as ⟶ E₂.as) :
    AtomsMap pre.sigs ε₁ ε₂ →
    Quot.RulesSound E₁ ε₁ η →
    Quot.RulesSound E₂ ε₂ (η.map pre.sigs) := fun hatoms₁ rules =>
  { quotAtom l a r := (congrFun hatoms₁ _).trans (rules.quotAtom l a r)
    quotMkAtom l a r x := (congrFun hatoms₁ _).trans (rules.quotMkAtom l a r x)
    rules {ζ₃ E₃ ε₃} suffix hatoms₂ := by
      have hcomp : AtomsMap (pre ≫ suffix).sigs ε₁ ε₃ := by
        simpa [dsimp% Env.forget.map_comp pre suffix] using hatoms₁.trans hatoms₂
      have hhead : (η.map pre.sigs).map suffix.sigs = η.map (pre ≫ suffix).sigs :=
        ((Env.forget ⋙ Head.functor _).map_comp_apply pre suffix η).symm
      simpa [hhead] using rules.rules (pre ≫ suffix) hcomp }

end Quot.RulesSound

end Metalean
