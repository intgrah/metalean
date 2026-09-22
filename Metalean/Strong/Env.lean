/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Inductive
public import Metalean.Typing.Env
import Metalean.Strong.InstLevel
import Metalean.Strong.Substitution
import Metalean.Strong.Telescope
import Metalean.Strong.WeakenEnv
import Metalean.Typing.Builtin.Eq
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ : Sigs} {E : Env ζ} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

namespace Entry

variable {sig sig₁ : Sig} {entry : Entry ζ sig}

theorem WFStrong.weakenEnv
    {entry' : Entry ζ sig₁} :
    entry.WFStrong E →
    (entry.weakenEnv).WFStrong (E.snoc entry') := by
  intro h
  induction h with
  | «axiom» ht =>
    obtain ⟨l, ht⟩ := ht
    exact .axiom ⟨l, by
      simpa [Ctx.weakenEnv, Expr.weakenEnv, Expr.map] using ht.weakenEnv entry'⟩
  | «opaque» he ht =>
    obtain ⟨l, ht⟩ := ht
    exact .opaque
      (by simpa [Ctx.weakenEnv, Expr.weakenEnv] using he.weakenEnv entry')
      ⟨l, by simpa [Ctx.weakenEnv, Expr.weakenEnv, Expr.map] using ht.weakenEnv entry'⟩
  | «def» ht he =>
    obtain ⟨l, ht⟩ := ht
    exact .def
      ⟨l, by simpa [Ctx.weakenEnv, Expr.weakenEnv, Expr.map] using ht.weakenEnv entry'⟩
      (by simpa [Ctx.weakenEnv, Expr.weakenEnv] using he.weakenEnv entry')
  | quot heq =>
    exact .quot <| by
      simpa using congrArg (Inductive.map (.step .refl : ζ ⟶ ζ.snoc sig₁)) heq
  | «inductive» hi => exact .inductive hi.weakenEnv

theorem WFStrong.block {ι : IndSig}
    {entry : Entry ζ (.inductive ι)} :
    entry.WFStrong E →
    entry.block.WFStrong E := by
  intro h
  cases h with
  | «inductive» hi => exact hi

theorem WFStrong.value
    {entry : Entry ζ (.const .def ℓ)} :
    entry.WFStrong E →
    E[.nil] ⊢ₛ entry.defValue : entry.constType := by
  intro h
  cases h with
  | «def» _ he => exact he

theorem WFStrong.type {kind : ConstKind}
    {entry : Entry ζ (.const kind ℓ)} :
    entry.WFStrong E →
    E[.nil] ⊢ₛ entry.constType typ := by
  intro h
  cases h with
  | «axiom» ht | «opaque» _ ht | «def» ht _ => exact ht

theorem WFStrong.constType
    {kind : ConstKind} {ℓ' : Nat}
    {η : Head ζ (.const kind ℓ')}
    (h : (E.get η).WFStrong E)
    (ls : Fin ℓ' → Level ℓ) :
    E[Γ] ⊢ₛ ((E.get η).constType.instL ls).wkClosed typ :=
  have ⟨l, ht⟩ := h.type
  ⟨l.inst ls, by simpa! using (ht.instLevel ls).wkClosed⟩

theorem WFStrong.defValue
    {ℓ' : Nat} {η : Head ζ (.const .def ℓ')}
    (h : (E.get η).WFStrong E)
    (ls : Fin ℓ' → Level ℓ) :
    E[Γ] ⊢ₛ ((E.get η).defValue.instL ls).wkClosed :
      ((E.get η).constType.instL ls).wkClosed :=
  (h.value.instLevel ls).wkClosed

theorem WFStrong.ctorType
    {ι : IndSig} {η : Head ζ (.inductive ι)}
    (h : (E.get η).WFStrong E)
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    {ls : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    {fds₁ fds₂ : Fin (ι.ctors s c).nfields → Expr ζ ℓ n} :
    (∀ p, E[Γ] ⊢ₛ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ₛ fds₁ f ≡ fds₂ f :
      (((((E.get η).block.ctors s c).ordinary f).type).instL ls).subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ₛ .ind η s ls ps₁ (((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁) ≡
      .ind η s ls ps₂ (((E.get η).block.ctors s c).targetIndex ls ps₂ fds₂) :
      .sort ((E.get η).block.level.inst ls) := by
  intro hps hfields
  have hctor := h.block.ctors s c
  exact .indDF hps (hctor.targetIndex_congr h.block.params · hps hfields)

end Entry

theorem Env.Ordered.entryWFStrong (ho : E.Ordered) {sig : Sig} (η : Head ζ sig) :
    (E.get η).WFStrong E := by
  induction ho generalizing sig with
  | nil => exact nomatch η
  | snoc _ hentry ih =>
    cases η with
    | here =>
      simpa [Env.get] using hentry.weakenEnv
    | there η =>
      simpa [Env.get] using (ih η).weakenEnv

theorem Env.Ordered.block_spec {ι : IndSig} {ζ₀ : Sigs} {E₀ : Env ζ₀} (ho : E₀.Ordered)
    (pre : E₀.as ⟶ E.as) (η : Head ζ₀ (.inductive ι)) :
    ∃ (ζ₂ : Sigs) (E₂ : Env ζ₂) (pre₂ : E₂.as ⟶ E₀.as) (I : Inductive ζ₂ ι),
      ζ₂.length < ζ₀.length ∧ I.WFStrong E₂ ∧
        (E.get (η.map pre.sigs)).block = I.map (pre₂ ≫ pre).sigs := by
  induction ho with
  | nil => cases η
  | @snoc ζ₁ sig E₀ entry ho hentry ih =>
    cases η with
    | here =>
      cases entry with
      | «inductive» I =>
        have .«inductive» hi := hentry
        refine ⟨_, E₀, .step .refl, I, Nat.lt_succ_self _, hi, ?_⟩
        rw [dsimp% (Env.lookup _).naturality_apply pre Head.here]
        exact (Functor.map_comp_apply (Env.forget ⋙ Inductive.functor ι) (X := E₀.as)
          (Y := (E₀.snoc (.inductive I)).as) (Z := E.as) (.step .refl) pre I).symm
    | there η =>
      have ⟨ζ₂, E₂, pre₂, I, hlen, hi, hget⟩ := ih (.step .refl ≫ pre) η
      refine ⟨ζ₂, E₂, pre₂ ≫ .step .refl, I, Nat.lt_succ_of_lt hlen, hi, ?_⟩
      have hsigs := Env.forget.map_comp (X := E₀.as) (Y := (E₀.snoc entry).as) (Z := E.as)
        (.step .refl) pre
      have hη := ConcreteCategory.congr_hom ((Head.functor _).map_comp
        (Sigs.Prefix.step .refl : ζ₁ ⟶ ζ₁.snoc sig) pre.sigs) η
      dsimp at hsigs hη
      rw [Category.assoc, ← hget, hsigs]
      exact congrArg (fun η => (E.get η).block) hη.symm

open CategoryTheory in
theorem Env.Ordered.def_spec {ℓ' : Nat} {ζ₀ : Sigs} {E₀ : Env ζ₀} (ho : E₀.Ordered)
    (pre : E₀.as ⟶ E.as) (η : Head ζ₀ (.const .def ℓ')) :
    ∃ (ζ₂ : Sigs) (E₂ : Env ζ₂) (pre₂ : E₂.as ⟶ E₀.as) (t e : Expr ζ₂ ℓ' 0),
      ζ₂.length < ζ₀.length ∧ E₂[.nil] ⊢ₛ e : t ∧
        E.get (η.map pre.sigs) = (Entry.def t e).map (pre₂ ≫ pre).sigs := by
  induction ho with
  | nil => cases η
  | @snoc ζ₁ sig E₀ entry ho hentry ih =>
    cases η with
    | here =>
      cases entry with
      | «def» t e =>
        have .«def» _ he := hentry
        refine ⟨_, E₀, .step .refl, t, e, Nat.lt_succ_self _, he, ?_⟩
        rw [dsimp% (Env.lookup _).naturality_apply pre Head.here]
        exact (Functor.map_comp_apply (Env.forget ⋙ Entry.functor _) (X := E₀.as)
          (Y := (E₀.snoc (.def t e)).as) (Z := E.as) (.step .refl) pre (.def t e)).symm
    | there η =>
      have ⟨ζ₂, E₂, pre₂, t, e, hlen, he, hget⟩ := ih (.step .refl ≫ pre) η
      refine ⟨ζ₂, E₂, pre₂ ≫ .step .refl, t, e, Nat.lt_succ_of_lt hlen, he, ?_⟩
      have hsigs := Env.forget.map_comp (X := E₀.as) (Y := (E₀.snoc entry).as) (Z := E.as)
        (.step .refl) pre
      have hη := ConcreteCategory.congr_hom ((Head.functor _).map_comp
        (Sigs.Prefix.step .refl : ζ₁ ⟶ ζ₁.snoc sig) pre.sigs) η
      dsimp at hsigs hη
      rw [Category.assoc, ← hget, hsigs]
      exact congrArg E.get hη.symm

end Metalean
