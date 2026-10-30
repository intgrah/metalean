/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.SetSemantics.Realization
public import Metalean.SetSemantics.Soundness

@[expose] public section

universe u

namespace Metalean

open ZFSet

variable {ℓ ℓ₁ n m count level bound bound₁ : Nat}
  {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ε₁ : Atom ζ₁ ℓ → ZFSet.{u}} {ε₂ : Atom ζ₂ ℓ → ZFSet.{u}} {ν : Param ℓ → Nat}
  {Γ : Ctx ζ₁ ℓ 0 n} {Δ : Ctx ζ₁ ℓ n m}

structure StrongTeleModel (E₁ : Env ζ₁) (ε₁ : Atom ζ₁ ℓ → ZFSet.{u}) (ν : Param ℓ → Nat)
    (Γ : Ctx ζ₁ ℓ 0 n) : Type (u + 1) where
  sem : SemTele.{u} 0 n
  bounded : ∃ level, sem.DomsIn level
  realizes : Realizes ε₁ ν Set.univ Γ sem

structure StrongTeleExtension (E₁ : Env ζ₁) (ε₁ : Atom ζ₁ ℓ → ZFSet.{u}) (ν : Param ℓ → Nat)
    (base : StrongTeleModel E₁ ε₁ ν Γ) (Δ : Ctx ζ₁ ℓ n m) (bound : Nat) : Type (u + 1) where
  sem : SemTele.{u} n m
  bounded : sem.DomsIn bound
  realizes : Realizes ε₁ ν (Reachable Set.univ base.sem) Δ sem

variable {base : StrongTeleModel E₁ ε₁ ν Γ}

theorem StrongTeleModel.semCtx (model : StrongTeleModel E₁ ε₁ ν Γ)
    (γ : Slots n) (hγ : γ ∈ Reachable Set.univ model.sem) :
    ε₁[ν] ⊨ γ : Γ :=
  model.realizes.semCtx γ hγ

theorem StrongTeleExtension.semCtx (extension : StrongTeleExtension E₁ ε₁ ν base Δ bound)
    (γ : Slots m) (hγ : γ ∈ Reachable (Reachable Set.univ base.sem) extension.sem) :
    ε₁[ν] ⊨ γ : (Γ ++ Δ) :=
  (base.realizes.append extension.realizes).semCtx γ (.append hγ)

def StrongTeleExtension.mono (extension : StrongTeleExtension E₁ ε₁ ν base Δ bound)
    (hle : bound ≤ bound₁) :
    StrongTeleExtension E₁ ε₁ ν base Δ bound₁ where
  sem := extension.sem
  bounded := extension.bounded.mono hle
  realizes := extension.realizes

open scoped Classical in
private theorem SemDefeq.exists_domain {t : Expr ζ₁ ℓ m}
    {reach : Set (Slots.{u} m)} {l : Level ℓ}
    (interp : ∀ γ ∈ reach, ε₁[ν; γ] ⊨ t ≡ t : .sort l)
    (hlevel : l.eval ν ≤ bound + 1) :
    ∃ domain : Dom.{u} m, (∀ γ, domain γ ∈ U_ bound) ∧
      ∀ γ ∈ reach, ε₁[ν; γ]⟦t⟧ = domain γ := by
  refine ⟨fun γ => if γ ∈ reach then ε₁[ν; γ]⟦t⟧ else ∅,
    fun γ => ?_, fun γ hγ => by simp [hγ]⟩
  by_cases hγ : γ ∈ reach
  · simpa [hγ] using mem_type_of_mem_sort hlevel (interp γ hγ).mem
  · simpa [hγ] using empty_mem_type

theorem TeleWF.modelExtensionAt (hdecl : SemDecls E₁ ε₁ ν)
    (hrule : SemDeclRules E₁ ε₁ ν) (hE : EnvWF E₁)
    {P : Level ℓ → Prop}
    (hls : ∀ {l}, P l → l.eval ν ≤ bound + 1)
    (base : StrongTeleModel E₁ ε₁ ν Γ) (hΔ : TeleWF E₁ P Γ Δ) :
    Nonempty (StrongTeleExtension E₁ ε₁ ν base Δ bound) := by
  induction hΔ with
  | nil => exact ⟨#t[], .nil, .nil⟩
  | @snoc m Δ t _ hA ih =>
    have ⟨model⟩ := ih
    have ⟨l, hl, ht⟩ := hA
    have ⟨_, hbounded, htype⟩ := SemDefeq.exists_domain
      (fun γ hγ => soundness hdecl hrule hE ht γ (model.semCtx γ hγ)) (hls hl)
    exact ⟨model.sem.snoc _, .snoc model.bounded hbounded, .snoc model.realizes htype⟩

theorem TeleWF.modelExtension (hdecl : SemDecls E₁ ε₁ ν)
    (hrule : SemDeclRules E₁ ε₁ ν) (hE : EnvWF E₁)
    (base : StrongTeleModel E₁ ε₁ ν Γ) (hΔ : TeleWF E₁ (fun _ => True) Γ Δ) :
    Nonempty (Σ bound, StrongTeleExtension E₁ ε₁ ν base Δ bound) := by
  induction hΔ with
  | nil => exact ⟨0, #t[], .nil, .nil⟩
  | @snoc m Δ t _ hA ih =>
    have ⟨level, model⟩ := ih
    have ⟨l, _, ht⟩ := hA
    have ⟨_, hbounded, htype⟩ := SemDefeq.exists_domain
      (fun γ hγ => soundness hdecl hrule hE ht γ (model.semCtx γ hγ)) (Nat.le_succ (l.eval ν))
    exact ⟨max level (l.eval ν), model.sem.snoc _,
      .snoc (model.bounded.mono (Nat.le_max_left _ _))
        (fun γ => type_mono (Nat.le_max_right _ _) (hbounded γ)),
      .snoc model.realizes htype⟩

theorem TeleWF.model (hdecl : SemDecls E₁ ε₁ ν) (hrule : SemDeclRules E₁ ε₁ ν) (hE : EnvWF E₁)
    (hΓ : TeleWF E₁ (fun _ => True) #t[] Γ) :
    Nonempty (StrongTeleModel E₁ ε₁ ν Γ) :=
  have ⟨_, extension⟩ := hΓ.modelExtension hdecl hrule hE ⟨#t[], ⟨0, .nil⟩, .nil⟩
  ⟨extension.sem, ⟨_, extension.bounded⟩,
    extension.realizes.monoReach fun _ _ => .nil trivial⟩

def StrongTeleModel.append (base : StrongTeleModel E₁ ε₁ ν Γ)
    (extension : StrongTeleExtension E₁ ε₁ ν base Δ bound) :
    StrongTeleModel E₁ ε₁ ν (Γ ++ Δ) where
  sem := base.sem ++ extension.sem
  bounded :=
    have ⟨baseLevel, hbase⟩ := base.bounded
    ⟨max baseLevel bound, (hbase.mono (Nat.le_max_left _ _)).append
      (extension.bounded.mono (Nat.le_max_right _ _))⟩
  realizes := base.realizes.append extension.realizes

end Metalean
