/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Strong.Defs
public import Metalean.Syntax.Weakening
import Metalean.Syntax.Structure.Projection
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.DefeqStrong

open CategoryTheory

variable {sig : Sig} {ζ ζ₁ ζ₂ : Sigs} {E : Env ζ} {E₁ : Env ζ₁} {E₂ : Env ζ₂}
  {ℓ n : Nat} {Γ : Ctx ζ ℓ 0 n} {Γ₁ : Ctx ζ₁ ℓ 0 n} {e₁ e₂ t : Expr ζ ℓ n}

theorem weakenEnv (entry : Entry ζ sig) :
    E[Γ] ⊢ₛ e₁ ≡ e₂ : t →
    (E.snoc entry)[Γ.weakenEnv] ⊢ₛ e₁.weakenEnv ≡ e₂.weakenEnv : t.weakenEnv := by
  intro h
  induction h with simp [Expr.weakenEnv, Expr.map] at *
  | var _ ih =>
      rw [← Ctx.get_map] at ih ⊢
      exact .var ih
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | sortDF => exact .sortDF
  | constDF _ ihtype =>
    rw [← dsimp% (Entry.constTypeNatTrans _ _).naturality_apply] at *
    exact .constDF ihtype
  | indDF _ _ ihps ihis =>
    rw [← dsimp% (Entry.blockNatTrans _).naturality_apply, ← Env.get_map_step] at ihps ihis
    have d := DefeqStrong.indDF ihps ihis
    simpa [Inductive.map] using d
  | ctorDF _ _ _ _ _ _ ihps ihfields ihrecFields
      ihfieldTypes ihrecFieldTypes ihtype =>
    rw [← dsimp% (Entry.blockNatTrans _).naturality_apply, ← Env.get_map_step] at ihps
    have d := DefeqStrong.ctorDF ihps
      (by simpa [Inductive.map, Ctor.map, Field.map] using ihfields)
      (by simpa [Inductive.map, Ctor.map] using ihrecFields)
      (by simpa [Inductive.map] using ihfieldTypes)
      (by simpa [Inductive.map] using ihrecFieldTypes)
      (by simpa [Inductive.map] using ihtype)
    simpa [Inductive.map] using d
  | recrDF hallowed _ _ _ _ _ _ ihps ihms ihmins
      ihis ihmaj ihresult =>
    have hallowed' := (Inductive.recAllowed_map _ (.step .refl : ζ ⟶ .snoc ζ sig) _).mpr hallowed
    rw [← dsimp% (Entry.blockNatTrans _).naturality_apply] at hallowed'
    have hps := by simpa using ihps
    have hms := by simpa using ihms
    have hmins := by simpa using ihmins
    have his := by simpa using ihis
    rw [← dsimp% (Entry.blockNatTrans _).naturality_apply] at hps hms hmins his
    simpa using
      .recrDF hallowed' hps hms hmins his ihmaj ihresult
  | appDF _ _ _ _ _ iht iht' ihf ihe ihtype =>
    exact .appDF iht iht' ihf ihe ihtype
  | lamDF _ _ _ _ _ iht iht' iht₂' ihbody ihbody' =>
    exact .lamDF iht iht' iht₂' ihbody ihbody'
  | forallEDF _ _ _ iht ihbody ihbody' =>
    exact .forallEDF iht ihbody ihbody'
  | defeqDF _ _ iht ihe => exact .defeqDF iht ihe
  | beta _ _ _ _ _ _ iht iht' ihbody ihe ihtype ihresult =>
    exact .beta iht iht' ihbody ihe ihtype ihresult
  | zeta _ _ _ _ iht ihv ihr ihbody =>
    exact .zeta iht ihv ihr (by simpa using ihbody)
  | eta _ _ _ _ _ iht iht' ihtwk ihewk ihe =>
    exact .eta iht iht' ihtwk ihewk ihe
  | @etaStruct _ _ _ η _ _ _ _ _ _ h _ _ _ ihps ihmaj ihrebuild =>
    have hblock : ((E.snoc entry).get (η.map (.step .refl))).block =
        (E.get η).block.map (.step .refl) := by simp
    generalize h.map (.step .refl) = hs at ihrebuild ⊢
    generalize hB : (E.get η).block.map (.step .refl) = B at hs ihps ihrebuild ⊢
    obtain rfl := hblock.trans hB
    exact .etaStruct hs ihps ihmaj ihrebuild
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | iota hallowed _ _ _ _ _ _ _ _ ihps ihms ihmins ihfields ihrecFields
      ihtype ihlhs ihrhs =>
    have hallowed' := (Inductive.recAllowed_map _
      (.step .refl : ζ ⟶ .snoc ζ sig) _).mpr hallowed
    rw [← dsimp% (Entry.blockNatTrans _).naturality_apply, ← Env.get_map_step] at hallowed'
    have hps := by simpa using ihps
    have hms := by simpa using ihms
    have hmins := by simpa using ihmins
    rw [← dsimp% (Entry.blockNatTrans _).naturality_apply] at hps hms hmins ihtype ihlhs ihrhs
    simpa using
      DefeqStrong.iota hallowed' hps hms hmins
        (by simpa [Inductive.map, Ctor.map, Field.map] using ihfields)
        (by simpa [Inductive.map, Ctor.map] using ihrecFields)
        ihtype ihlhs ihrhs
  | quotDF _ _ ihα ihr => exact .quotDF ihα ihr
  | quotMkDF _ _ _ ihα ihr iha => exact .quotMkDF ihα ihr iha
  | quotLiftDF _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    rw [← dsimp% Entry.eqHeadNatTrans.naturality_apply] at ihh
    exact .quotLiftDF ihα ihr ihβ ihf ihh iha
  | quotIndDF _ _ _ _ _ _ ihα ihr ihβ ihf iha ihresult =>
    exact .quotIndDF ihα ihr ihβ ihf iha ihresult
  | quotIota _ _ _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha ihlhs ihrhs =>
    rw [← dsimp% Entry.eqHeadNatTrans.naturality_apply] at ihh
    exact .quotIota ihα ihr ihβ ihf ihh iha ihlhs ihrhs
  | delta _ _ ihtype ihvalue =>
    rw [← dsimp% (Entry.constTypeNatTrans _ _).naturality_apply] at ihtype
    rw [← dsimp% (Entry.constTypeNatTrans _ _).naturality_apply,
      ← dsimp% (Entry.defValueNatTrans _).naturality_apply] at ihvalue ⊢
    exact .delta ihtype ihvalue

theorem envMono {e₁ e₂ t : Expr ζ₁ ℓ n} (pre : E₁.as ⟶ E₂.as) :
    E₁[Γ₁] ⊢ₛ e₁ ≡ e₂ : t →
    E₂[Γ₁.map pre.sigs] ⊢ₛ e₁.map pre.sigs ≡ e₂.map pre.sigs : t.map pre.sigs := by
  intro h
  induction pre with
  | refl =>
    simpa! [dsimp% [CategoryStruct.id] (Expr.functor ℓ n).map_id_apply ζ₁,
      dsimp% [CategoryStruct.id] (Ctx.functor ℓ 0 n).map_id_apply ζ₁ Γ₁] using h
  | step pre ih =>
    exact congr(_[$(Ctx.map_step pre.sigs Γ₁)] ⊢ₛ
      $(Expr.map_step pre.sigs e₁) ≡ $(Expr.map_step pre.sigs e₂) :
      $(Expr.map_step pre.sigs t)).mp ((ih h).weakenEnv _)

end Metalean.DefeqStrong

namespace Metalean

variable {ζ₁ ζ₂ : Sigs} {E₁ : Env ζ₁} {E₂ : Env ζ₂} {ℓ n : Nat} {Γ : Ctx ζ₁ ℓ 0 n}

theorem CtxWFStrong.envMono (pre : E₁.as ⟶ E₂.as) :
    E₁[Γ] ⊢ₛ ok →
    E₂[Γ.map pre.sigs] ⊢ₛ ok := by
  intro h
  induction h with
  | nil => exact .nil
  | snoc _ ht ih =>
    obtain ⟨u, ht⟩ := ht
    exact .snoc ih ⟨u, ht.envMono pre⟩

end Metalean
