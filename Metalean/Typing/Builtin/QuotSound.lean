/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.QuotSound
public import Metalean.Typing.Quot
import Metalean.Typing.Substitution
import Metalean.Typing.Builtin.Eq

@[expose] public section

namespace Metalean.Quot.Sound

theorem isType : Nonempty.env[.nil] ⊢ type typ := by
  let l : Level 1 := .param ⟨0, by decide⟩
  let Γ₁ : Ctx Nonempty.sigs 1 0 4 := #t[.sort l, Quot.relType #0, #0, #0]
  have hα₁ : Nonempty.env[Γ₁] ⊢ #0 : .sort l := .var .sortDF
  have hr₁ : Nonempty.env[Γ₁] ⊢ #1 : Quot.relType #0 :=
    .var (Quot.relType_congr hα₁)
  have ha₁ : Nonempty.env[Γ₁] ⊢ #2 : #0 := .var hα₁
  have hb₁ : Nonempty.env[Γ₁] ⊢ #3 : #0 := .var hα₁
  have hcod : Nonempty.env[Γ₁.snoc #0] ⊢ .forallE #0 .prop : .sort (.imax l .one) :=
    .forallEDF (.var .sortDF) .sortDF .sortDF
  have hrel : Nonempty.env[Γ₁] ⊢ .app (.app #1 #2) #3 : .prop :=
    .appDF (t' := .prop) hα₁ .sortDF
      (by
        simpa [Expr.inst, Expr.subst, Subst.extend, Subst.id] using
          Defeq.appDF hα₁ hcod hr₁ ha₁ (hcod.inst_congr ha₁))
      hb₁ .sortDF
  let Γ₂ := Γ₁.snoc (.app (.app #1 #2) #3)
  have hα₂ : Nonempty.env[Γ₂] ⊢ #0 : .sort l := .var .sortDF
  have hr₂ : Nonempty.env[Γ₂] ⊢ #1 : Quot.relType #0 :=
    .var (Quot.relType_congr hα₂)
  have ha₂ : Nonempty.env[Γ₂] ⊢ #2 : #0 := .var hα₂
  have hb₂ : Nonempty.env[Γ₂] ⊢ #3 : #0 := .var hα₂
  have heq := Quot.eqApp_typed (ηeq := eqHead) (by
    simp [eqHead, Nonempty.env, Iff.env, Quot.env, Eq.env, Env.get,
      Entry.weakenEnv, Entry.map, Entry.block])
    (Defeq.quotDF (η := quotHead) hα₂ hr₂)
    (.quotMkDF hα₂ hr₂ ha₂) (.quotMkDF hα₂ hr₂ hb₂)
  have h₄ := Defeq.forallEDF hrel heq heq
  have h₃ := Defeq.forallEDF (.var .sortDF) h₄ h₄
  have h₂ := Defeq.forallEDF (.var .sortDF) h₃ h₃
  have h₁ := Defeq.forallEDF (Quot.relType_congr (.var .sortDF)) h₂ h₂
  exact ⟨_, .forallEDF .sortDF h₁ h₁⟩

end Metalean.Quot.Sound
