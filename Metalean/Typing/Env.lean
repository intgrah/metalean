/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Typing.Inductive
public import Metalean.Typing.Env.Defs
import Metalean.Typing.InstLevel
import Metalean.Typing.Map
import Metalean.Typing.Substitution
import Metalean.Typing.Telescope
import Metalean.Syntax.Eq
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean

open CategoryTheory

variable {ζ ζ₁ ζ₂ : Sigs} {E : Env ζ} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n}

namespace EntryWF

theorem map {sig : Sig} {entry : Entry ζ₁ sig} (pre : E₁.as ⟶ E₂.as) :
    EntryWF E₁ entry →
    EntryWF E₂ (entry.map pre.sigs) := by
  intro h
  induction h with
  | «axiom» ht =>
    obtain ⟨l, ht⟩ := ht
    exact .axiom ⟨l, by simpa using ht.map pre⟩
  | «opaque» he ht =>
    obtain ⟨l, ht⟩ := ht
    exact .opaque
      (by simpa using he.map pre)
      ⟨l, by simpa using ht.map pre⟩
  | «def» ht he =>
    obtain ⟨l, ht⟩ := ht
    exact .def
      ⟨l, by simpa using ht.map pre⟩
      (by simpa using he.map pre)
  | quot heq =>
    exact .quot <| by
      simpa [Env.get_map] using congrArg (Inductive.map pre.sigs) heq
  | «inductive» hi => exact .inductive (hi.map pre)

theorem block {ι : IndSig} {entry : Entry ζ (.inductive ι)} :
    EntryWF E entry →
    InductiveWF E entry.block
  | «inductive» hi => hi

theorem value {entry : Entry ζ (.const .def ℓ)} :
    EntryWF E entry →
    E[.nil] ⊢ entry.defValue : entry.constType
  | «def» _ he => he

theorem type {kind : ConstKind} {entry : Entry ζ (.const kind ℓ)} :
    EntryWF E entry →
    E[.nil] ⊢ entry.constType typ
  | «axiom» ht | «opaque» _ ht | «def» ht _ => ht

theorem constType {kind : ConstKind} {ℓ' : Nat}
    {η : Head ζ (.const kind ℓ')} (h : EntryWF E (E.get η)) (ls : Fin ℓ' → Level ℓ) :
    E[Γ] ⊢ (E.get η).constType{ls}.wkClosed typ :=
  have ⟨l, ht⟩ := h.type
  ⟨l{ls}, by simpa! using (ht.instLevel ls).wkClosed⟩

theorem defValue {ℓ' : Nat} {η : Head ζ (.const .def ℓ')}
    (h : EntryWF E (E.get η)) (ls : Fin ℓ' → Level ℓ) :
    E[Γ] ⊢ (E.get η).defValue{ls}.wkClosed :
      (E.get η).constType{ls}.wkClosed :=
  (h.value.instLevel ls).wkClosed

theorem ctorType {ι : IndSig} {η : Head ζ (.inductive ι)} (h : EntryWF E (E.get η))
    (s : Fin ι.nsorts) (c : Fin (ι.nctors s))
    {ls : Fin ι.nlevels → Level ℓ}
    {ps₁ ps₂ : Fin ι.nparams → Expr ζ ℓ n}
    {fds₁ fds₂ : Fin (ι.ctors s c).nfields → Expr ζ ℓ n} :
    (∀ p, E[Γ] ⊢ ps₁ p ≡ ps₂ p :
      (E.get η).block.paramType ls ps₁ p) →
    (∀ f, E[Γ] ⊢ fds₁ f ≡ fds₂ f :
      (((E.get η).block.ctors s c).ordinary f).type{ls}.subst
        (Fin.append ps₁ fun previous : Fin f.val =>
          fds₁ (previous.castLE f.isLt.le))) →
    E[Γ] ⊢ .ind η s ls ps₁ (((E.get η).block.ctors s c).targetIndex ls ps₁ fds₁) ≡
      .ind η s ls ps₂ (((E.get η).block.ctors s c).targetIndex ls ps₂ fds₂) :
      .sort (E.get η).block.level{ls} := by
  intro hps hfields
  have hctor := h.block.ctors s c
  exact .indDF hps (hctor.targetIndex_congr h.block.params · hps hfields)

end EntryWF

theorem EnvWF.entryWF {sig : Sig} (η : Head ζ sig) :
    EnvWF E →
    EntryWF E (E.get η) := by
  intro hE
  induction hE generalizing sig with
  | nil => exact nomatch η
  | snoc _ hentry ih =>
    cases η with
    | here => exact hentry.map (.step .refl)
    | there η => exact (ih η).map (.step .refl)

theorem EnvWF.eqBlock (η : Head ζ .quot) :
    EnvWF E →
    (E.get (E.get η).eqHead).block = Eq.block := by
  intro hE
  have hη := hE.entryWF η
  generalize E.get η = entry at hη
  have .quot heq := hη
  exact heq

theorem EnvWF.block_spec {ι : IndSig} {ζ₀ : Sigs} {E₀ : Env ζ₀} (hE : EnvWF E₀)
    (pre : E₀.as ⟶ E.as) (η : Head ζ₀ (.inductive ι)) :
    ∃ (ζ₂ : Sigs) (E₂ : Env ζ₂) (pre₂ : E₂.as ⟶ E₀.as) (I : Inductive ζ₂ ι),
      ζ₂.length < ζ₀.length ∧ InductiveWF E₂ I ∧
        (E.get (η.map pre.sigs)).block = I.map (pre₂ ≫ pre).sigs := by
  induction hE with
  | nil => cases η
  | @snoc ζ₁ sig E₀ entry hE hentry ih =>
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
theorem EnvWF.def_spec {ℓ' : Nat} {ζ₀ : Sigs} {E₀ : Env ζ₀} (hE : EnvWF E₀)
    (pre : E₀.as ⟶ E.as) (η : Head ζ₀ (.const .def ℓ')) :
    ∃ (ζ₂ : Sigs) (E₂ : Env ζ₂) (pre₂ : E₂.as ⟶ E₀.as) (t e : Expr ζ₂ ℓ' 0),
      ζ₂.length < ζ₀.length ∧ E₂[.nil] ⊢ e : t ∧
        E.get (η.map pre.sigs) = (Entry.def t e).map (pre₂ ≫ pre).sigs := by
  induction hE with
  | nil => cases η
  | @snoc ζ₁ sig E₀ entry hE hentry ih =>
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

namespace Defeq

variable {t : Expr ζ ℓ n}
variable {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
  {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ n} {ms : Fin ι.nsorts → Expr ζ ℓ n}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ n}
  {is : Fin (ι.nindices s) → Expr ζ ℓ n} {maj : Expr ζ ℓ n}
  {fds : Fin (ι.ctors s c).nfields → Expr ζ ℓ n}
  {recFds : Fin (ι.ctors s c).nrecFields → Expr ζ ℓ n}

theorem ind_typed :
    EnvWF E →
    E[Γ] ⊢ .ind η s ls ps is : t →
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) ∧
    ∀ i, E[Γ] ⊢ is i : (E.get η).block.indexType ls s ps is i := by
  intro hE h
  have ⟨_, _, hps, his, _⟩ := h.ind_inv
  have hB := (hE.entryWF η).block
  exact ⟨fun p => Inductive.paramType_conv hB p hps,
    fun i => Inductive.indexType_conv hB i hps his⟩

theorem ctor_typed :
    EnvWF E →
    E[Γ] ⊢ .ctor η s c ls ps fds recFds : t →
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) ∧
    (∀ f, E[Γ] ⊢ fds f : ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps fds f) ∧
    ∀ f, E[Γ] ⊢ recFds f : ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps fds f := by
  intro hE h
  have ⟨_, _, _, hps, hfds, hrecFds, _, _⟩ := h.ctor_inv
  have hB := (hE.entryWF η).block
  refine ⟨fun p => Inductive.paramType_conv hB p hps, fun f => ?_, fun f => ?_⟩
  · exact (TypeEq.ofDefEq ((hB.ctors s c).ordinaryFieldExpr_congr hB.params f hps
      fun g _ => hfds g)).conv (hfds f).right
  · have ⟨_, hrec⟩ := (hB.ctors s c).recursiveFieldExpr_congr hB.params rfl f hps hfds
    exact (TypeEq.ofDefEq hrec).conv (hrecFds f).right

theorem recr_typed :
    EnvWF E →
    E[Γ] ⊢ ok →
    E[Γ] ⊢ .recr η s ls l ps ms mins is maj : t →
    (E.get η).block.RecAllowed ls l ∧
    (∀ p, E[Γ] ⊢ ps p : (E.get η).block.paramType ls ps p) ∧
    (∀ s₁, E[Γ] ⊢ ms s₁ : (E.get η).block.motiveType η ls ps l s₁) ∧
    (∀ s₁ c₁, E[Γ] ⊢ mins s₁ c₁ : (E.get η).block.caseFnType η ls ps ms s₁ c₁) ∧
    (∀ i, E[Γ] ⊢ is i : (E.get η).block.indexType ls s ps is i) ∧
    E[Γ] ⊢ maj : .ind η s ls ps is := by
  intro hE hΓ h
  have ⟨_, _, _, _, _, hrec, hps, hms, hmins, his, hmaj, _, _⟩ := h.recr_inv
  have hB := (hE.entryWF η).block
  exact ⟨hrec, fun p => Inductive.paramType_conv hB p hps,
    fun s₁ => (Inductive.motiveType_congr hB hΓ hps).conv (hms s₁).right,
    fun s₁ c₁ => Inductive.caseFnType_conv hB hΓ hps hms (hmins s₁ c₁),
    fun i => Inductive.indexType_conv hB i hps his,
    (TypeEq.ofDefEq (.indDF hps his)).conv hmaj.right⟩

end Defeq

end Metalean
