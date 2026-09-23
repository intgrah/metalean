/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Eq
public import Metalean.Typing.Env.Defs
public import Metalean.Typing.Quot
import Metalean.Level.Quot.Order
import Metalean.Typing.Substitution
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Built in environment
Here we define and check the builtins, then assemble a base environment.
-/

namespace Metalean

universe u

variable {ζ ζ₁ ζ₂ : Sigs} {E : Env ζ}

/-
We already had to define Eq much earlier because of quotient types,
so here we only need to prove well formedness
-/

variable (E) in
theorem Eq.wf : InductiveWF E Eq.block where
  params := .snoc
    (.snoc .nil ⟨_, trivial, .sortDF⟩)
    ⟨_, trivial, .var .sortDF⟩
  indices | ⟨0, _⟩ => .snoc .nil ⟨_, trivial, .var .sortDF⟩
  ctors | ⟨0, _⟩, ⟨0, _⟩ => {
    ordinary f := Fin.elim0 f
    recursive f := Fin.elim0 f
    targetIndices | ⟨0, _⟩ => .var (.var .sortDF)
  }

namespace Iff

@[reducible] def ctorSig : CtorSig 1 where
  nfields := 2
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] def sig : IndSig where
  nlevels := 0
  nparams := 2
  nsorts := 1
  nindices _ := 0
  nctors _ := 1
  ctors _ _ := ctorSig

/-- `Iff (a b : Prop) : Prop` -/
@[reducible] def block : Inductive ζ sig where
  params := #t[.prop, .prop]
  indices _ := .nil
  level := .zero
  ctors _ _ := {
    ordinary
      | ⟨0, _⟩ => ⟨.forallE (.var ⟨0, by simp⟩) (.var ⟨1, by simp⟩), .zero⟩
      | ⟨1, _⟩ => ⟨.forallE (.var ⟨1, by simp⟩) (.var ⟨0, by simp⟩), .zero⟩
    recursive f := Fin.elim0 f
    targetIndices := ![]
  }

@[simp] theorem block_map (pre : ζ₁ ⟶ ζ₂) :
    (@block ζ₁).map pre = @block ζ₂ := by
  dsimp [Inductive.map]
  congr
  funext s c
  refine Fin.cases ?_ (fun i => Fin.elim0 i) s
  refine Fin.cases ?_ (fun i => Fin.elim0 i) c
  dsimp [Ctor.map, Field.map]
  congr
  · funext f
    refine Fin.cases ?_ (fun f => ?_) f
    · simp [Expr.map]
    · refine Fin.cases ?_ (fun i => Fin.elim0 i) f
      simp [Expr.map]
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

variable (E) in
theorem wf : InductiveWF E block :=
  ⟨.snoc (.snoc .nil ⟨_, trivial, .sortDF⟩) ⟨_, trivial, .sortDF⟩,
    fun _ => .nil,
    fun _ _ => {
      ordinary
        | ⟨0, _⟩ =>
          ⟨by
              refine .defeqDF (l := .succ .zero) ?_ (.forallEDF (.var .sortDF) (.var .sortDF) (.var .sortDF))
              rw [Level.imax_zero]
              exact .sortDF,
            Inductive.levelOK_of_zero _ rfl⟩
        | ⟨1, _⟩ =>
          ⟨by
              refine .defeqDF (l := .succ .zero) ?_ (.forallEDF (.var .sortDF) (.var .sortDF) (.var .sortDF))
              rw [Level.imax_zero]
              exact .sortDF,
            Inductive.levelOK_of_zero _ rfl⟩
      recursive f := Fin.elim0 f
      targetIndices i := Fin.elim0 i
    }⟩

end Iff

namespace Nonempty

@[reducible] def ctorSig : CtorSig 1 where
  nfields := 1
  nrecFields := 0
  recursiveArity := ![]
  recursiveTarget := ![]

@[reducible] def sig : IndSig where
  nlevels := 1
  nparams := 1
  nsorts := 1
  nindices _ := 0
  nctors _ := 1
  ctors _ _ := ctorSig

/-- `Nonempty.{u} (α : Sort u) : Prop` -/
@[reducible] def block : Inductive ζ sig where
  params := #t[.sort (.param ⟨0, by decide⟩)]
  indices _ := .nil
  level := .zero
  ctors | ⟨0, _⟩, ⟨0, _⟩ => {
    ordinary _ := ⟨.var ⟨0, by simp⟩,
      .param ⟨0, by decide⟩⟩
    recursive f := Fin.elim0 f
    targetIndices := ![]
  }

@[simp] theorem block_map (pre : ζ₁ ⟶ ζ₂) :
    (@block ζ₁).map pre = @block ζ₂ := by
  dsimp [Inductive.map]
  congr
  funext s c
  refine Fin.cases ?_ (fun i => Fin.elim0 i) s
  refine Fin.cases ?_ (fun i => Fin.elim0 i) c
  dsimp [Ctor.map]
  congr <;> exact Subsingleton.elim _ _

variable (E) in
theorem wf : InductiveWF E block :=
  ⟨.snoc .nil ⟨_, trivial, .sortDF⟩,
    fun _ => .nil,
    fun ⟨0, _⟩ ⟨0, _⟩ => {
      ordinary
        | ⟨0, _⟩ =>
          ⟨.var .sortDF, Inductive.levelOK_of_zero block rfl⟩
      recursive f := Fin.elim0 f
      targetIndices i := Fin.elim0 i
    }⟩

end Nonempty

namespace ClassicalEnv

variable {ηeq : Head ζ (.inductive Eq.sig)} {ηquot : Head ζ .quot}
  {ηiff : Head ζ (.inductive Iff.sig)} {η : Head ζ (.inductive Nonempty.sig)}

recall Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α},
  r a b → @Quot.mk.{u} α r a = @Quot.mk.{u} α r b

variable (ηeq ηquot) in
def quotSoundType : Expr ζ 1 0 :=
  let r := (#1 : Expr ζ 1 5)
  .forallE (.sort (.param ⟨0, by decide⟩)) <|
    .forallE (.forallE #0 (.forallE #0 .prop)) <|
      .forallE #0 <|
        .forallE #0 <|
          .forallE (.app (.app #1 #2) #3) <|
            Quot.eqApp ηeq (.param ⟨0, by decide⟩)
              (.quot ηquot (.param ⟨0, by decide⟩) #0 r)
              (.quotMk ηquot (.param ⟨0, by decide⟩) #0 r #2)
              (.quotMk ηquot (.param ⟨0, by decide⟩) #0 r #3)

theorem quotSoundType_isType (heq : (E.get ηeq).block = Eq.block) :
    E[.nil] ⊢ quotSoundType ηeq ηquot typ := by
  let l : Level 1 := .param ⟨0, by decide⟩
  let Γ₁ : Ctx ζ 1 0 4 := #t[.sort l, Quot.relType #0, #0, #0]
  have hα₁ : E[Γ₁] ⊢ #0 : .sort l := .var .sortDF
  have hr₁ : E[Γ₁] ⊢ #1 : Quot.relType #0 :=
    .var (Quot.relType_congr hα₁)
  have ha₁ : E[Γ₁] ⊢ #2 : #0 := .var hα₁
  have hb₁ : E[Γ₁] ⊢ #3 : #0 := .var hα₁
  have hcod : E[Γ₁.snoc #0] ⊢ .forallE #0 .prop : .sort (.imax l .one) :=
    .forallEDF (.var .sortDF) .sortDF .sortDF
  have hrel : E[Γ₁] ⊢ .app (.app #1 #2) #3 : .prop :=
    .appDF (t' := .prop) hα₁ .sortDF
      (by
        simpa [Expr.inst, Expr.subst, Subst.extend, Subst.id] using
          Defeq.appDF hα₁ hcod hr₁ ha₁ (hcod.inst_congr ha₁))
      hb₁ .sortDF
  let Γ₂ := Γ₁.snoc (.app (.app #1 #2) #3)
  have hα₂ : E[Γ₂] ⊢ #0 : .sort l := .var .sortDF
  have hr₂ : E[Γ₂] ⊢ #1 : Quot.relType #0 :=
    .var (Quot.relType_congr hα₂)
  have ha₂ : E[Γ₂] ⊢ #2 : #0 := .var hα₂
  have hb₂ : E[Γ₂] ⊢ #3 : #0 := .var hα₂
  have htype := Quot.eqApp_typed heq
    (Defeq.quotDF (η := ηquot) hα₂ hr₂)
    (.quotMkDF hα₂ hr₂ ha₂) (.quotMkDF hα₂ hr₂ hb₂)
  have h₄ := Defeq.forallEDF hrel htype htype
  have h₃ := Defeq.forallEDF (.var .sortDF) h₄ h₄
  have h₂ := Defeq.forallEDF (.var .sortDF) h₃ h₃
  have h₁ := Defeq.forallEDF (Quot.relType_congr (.var .sortDF)) h₂ h₂
  exact ⟨_, .forallEDF .sortDF h₁ h₁⟩

recall propext : ∀ {a b : Prop}, Iff a b → @Eq.{1} Prop a b

variable (ηeq ηiff) in
def propextType : Expr ζ 0 0 :=
  .forallE .prop <| .forallE .prop <| .forallE
      (.ind ηiff ⟨0, by decide⟩ ![] ![#0, #1] ![]) <|
        .ind ηeq ⟨0, by decide⟩ (fun _ => .succ .zero) ![.prop, #0] ![#1]

theorem propextType_isType (heq : (E.get ηeq).block = Eq.block)
    (hiff : (E.get ηiff).block = Iff.block) :
    E[.nil] ⊢ propextType ηeq ηiff typ := by
  let Γ₁ : Ctx ζ 0 0 2 := #t[.prop, .prop]
  have hi : E[Γ₁] ⊢ .ind ηiff 0 ![] ![#0, #1] ![] : .prop := by
    suffices h : E[Γ₁] ⊢ .ind ηiff 0 ![] ![#0, #1] ![] :
        .sort ((E.get ηiff).block.level.inst ![]) by
      simpa [hiff, Iff.block] using h
    apply Defeq.indDF
    · intro p
      fin_cases p
      · rw [hiff]
        exact .var .sortDF
      · rw [hiff]
        exact .var .sortDF
    · exact fun i => Fin.elim0 i
  let Γ₂ := Γ₁.snoc (.ind ηiff 0 ![] ![#0, #1] ![])
  have he : E[Γ₂] ⊢ .ind ηeq 0 (fun _ => .succ .zero) ![.prop, #0] ![#1] : .prop := by
    suffices h : E[Γ₂] ⊢ .ind ηeq 0 (fun _ => .succ .zero) ![.prop, #0] ![#1] :
        .sort ((E.get ηeq).block.level.inst (fun _ => .succ .zero)) by
      simpa [heq, Eq.block] using h
    apply Defeq.indDF
    · intro p
      fin_cases p
      · rw [heq]
        exact .sortDF
      · rw [heq]
        exact .var .sortDF
    · intro i
      fin_cases i
      rw [heq]
      exact .var .sortDF
  exact ⟨_, .forallEDF .sortDF
    (.forallEDF .sortDF (.forallEDF hi he he) (.forallEDF hi he he))
    (.forallEDF .sortDF (.forallEDF hi he he) (.forallEDF hi he he))⟩

recall Classical.choice : ∀ {α : Sort u}, Nonempty.{u} α → α

variable (η) in
def classicalChoiceType : Expr ζ 1 0 :=
  .forallE (.sort (.param 0)) <|
    .forallE (.ind η ⟨0, by decide⟩ (fun _ => .param ⟨0, by decide⟩) ![#0] ![]) #0

theorem classicalChoiceType_isType (hblock : (E.get η).block = Nonempty.block) :
    E[.nil] ⊢ classicalChoiceType η typ := by
  let l : Level 1 := .param ⟨0, by decide⟩
  have hn : E[#t[.sort l]] ⊢ .ind η 0 (fun _ => l) ![#0] ![] : .prop := by
    suffices h : E[#t[.sort l]] ⊢ .ind η 0 (fun _ => l) ![#0] ![] :
        .sort ((E.get η).block.level.inst (fun _ => l)) by
      simpa [hblock, Nonempty.block] using h
    apply Defeq.indDF
    · intro p
      fin_cases p
      rw [hblock]
      exact .var .sortDF
    · exact fun i => Fin.elim0 i
  exact ⟨_, .forallEDF .sortDF
    (.forallEDF hn (.var .sortDF) (.var .sortDF))
    (.forallEDF hn (.var .sortDF) (.var .sortDF))⟩

/-! ## Environment construction -/

abbrev sigs₁ : Sigs := Sigs.nil.snoc (.inductive Eq.sig)
abbrev env₁ : Env sigs₁ := Env.nil.snoc (.inductive Eq.block)
theorem wf₁ : EnvWF env₁ := .snoc .nil (.inductive (Eq.wf _))

abbrev sigs₂ : Sigs := sigs₁.snoc .quot
abbrev env₂ : Env sigs₂ := env₁.snoc (.quot .here)
theorem wf₂ : EnvWF env₂ := .snoc wf₁ (.quot (Eq.block_map _))

abbrev sigs₃ : Sigs := sigs₂.snoc (.inductive Iff.sig)
abbrev env₃ : Env sigs₃ := env₂.snoc (.inductive Iff.block)
theorem wf₃ : EnvWF env₃ := .snoc wf₂ (.inductive (Iff.wf _))

abbrev sigs₄ : Sigs := sigs₃.snoc (.inductive Nonempty.sig)
abbrev env₄ : Env sigs₄ := env₃.snoc (.inductive Nonempty.block)
theorem wf₄ : EnvWF env₄ := .snoc wf₃ (.inductive (Nonempty.wf _))

abbrev sigs₅ : Sigs := sigs₄.snoc (.const .axiom 1)
abbrev env₅ : Env sigs₅ := env₄.snoc (.axiom (quotSoundType Head.here.there.there.there Head.here.there.there))
theorem wf₅ : EnvWF env₅ := .snoc wf₄ (.axiom (quotSoundType_isType <| by simp! [Env.get, Entry.block]))

abbrev sigs₆ : Sigs := .snoc sigs₅ (.const .axiom 0)
abbrev env₆ : Env sigs₆ := .snoc env₅
  (.axiom (propextType Head.here.there.there.there.there Head.here.there.there))
theorem wf₆ : EnvWF env₆ :=
  .snoc wf₅ (.axiom (propextType_isType
    (by simp [Env.get, Entry.map, Entry.block])
    (by simp [Env.get, Entry.map, Entry.block])))

abbrev sigs₇ : Sigs := sigs₆.snoc (.const .axiom 1)
abbrev env₇ : Env sigs₇ := env₆.snoc (.axiom (classicalChoiceType Head.here.there.there))
theorem wf₇ : EnvWF env₇ := .snoc wf₆ (.axiom (classicalChoiceType_isType <| by simp! [Env.get, Entry.block]))

protected abbrev ζ : Sigs := sigs₇
protected abbrev E : Env ClassicalEnv.ζ := env₇

end Metalean.ClassicalEnv
