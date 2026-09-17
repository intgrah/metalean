/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Consistency.Builtin.Eq
public import Metalean.SetSemantics.Consistency.Inductive

public section

universe u

namespace Metalean

open ZFSet

variable {ζ ζ₁ ζ₂ : Sigs}

noncomputable def Env.Model.addQuotient {pre : Env ζ}
    {ηeq : Head ζ (.inductive Eq.sig)} (m : Env.Model.{u} pre)
    (hwf : Entry.WF pre (.quot ηeq)) :
    Env.Model.{u} (pre.snoc (.quot ηeq)) := by
  have heq : Eq.Sem m.atoms ηeq :=
    have .quot hblock := hwf
    Eq.Sem.of_model m hblock
  let equality : Level 0 → ZFSet → ZFSet → ZFSet → ZFSet :=
    fun l α x y => m.atoms (.ind ηeq ⟨0, by decide⟩ (fun _ => l) ![α, x] ![y])
  let fresh : Atom (.snoc ζ .quot) 0 → ZFSet.{u}
    | .quot .here l a r => quotientCarrier (l.eval zeroNs) a r
    | .quotMk .here l a r x => quotientMk (l.eval zeroNs) a r x
    | .quotLift .here l₁ l₂ _ _ _ fn _ c =>
      quotientLiftResult (l₁.eval zeroNs) (l₂.eval zeroNs) fn c
    | .quotInd .here _ _ _ _ _ _ => proof
    | _ => ∅
  have hatoms := atomBelow.map m.atoms fresh
  have hseparates (l) : EqualitySeparates (l.eval zeroNs) (equality l) := by
    simpa [equality] using heq.separates l
  have hequality (u b x y) : atomBelow m.atoms fresh
        (.ind (pre.snoc (.quot ηeq) |>.get .here).eqHead
          ⟨0, by decide⟩ (fun _ => u) ![b, x] ![y])
      = equality u b x y :=
    congrFun hatoms (.ind ηeq ⟨0, by decide⟩ (fun _ => u) ![b, x] ![y])
  refine m.snoc fresh (.quot (Quot.RulesSound.ofValues .here equality
    hseparates hequality ?_ ?_ ?_ ?_))
  all_goals intros
  all_goals simp [atomBelow, fresh, Atom.unstep, Head.unstep]

inductive IsAxiom : {ζ : Sigs} → {sig : Sig} → Entry ζ sig → Prop
  | intro {ζ : Sigs} {ℓ : Nat} (t : Expr ζ ℓ 0) : IsAxiom (.axiom t)

noncomputable def Env.Model.extend {E₁ : Env ζ₁} {E₂ : Env ζ₂}
    (m : Model.{u} E₁) (pre : E₁.as ⟶ E₂.as)
    (h : pre.Forall fun entry => ¬ IsAxiom entry) (ho : E₂.Ordered) : Model.{u} E₂ := by
  induction pre with
  | refl => exact m
  | @step ζ₂ sig E₁ E₂ entry pre ih =>
    have hwf : Entry.WF E₂ entry :=
      have .snoc _ hwf := ho
      hwf
    have hprefix : pre.Forall fun entry => ¬ IsAxiom entry :=
      have .step hprefix _ := h
      hprefix
    have hpre : E₂.Ordered := ho.ofPrefix (.step .refl)
    let m := ih m hprefix hpre
    cases entry with
    | «axiom» type => exact (have .step _ hfree := h; hfree (.intro type)).elim
    | «opaque» => exact m.addOpaque hpre hwf
    | «def» => exact m.addDef hpre hwf
    | «inductive» => exact m.addInductive hpre hwf
    | quot => exact m.addQuotient hwf

end Metalean
