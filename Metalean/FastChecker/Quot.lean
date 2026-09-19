/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Instantiate
public import Metalean.Export.Basic
public import Metalean.Frontend.Failure

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

variable {E : Σ ζ, Env ζ} {L : Literals} {ℓ n k : Nat}

namespace FExpr

def relType (α : FExpr) : FExpr :=
  .forallE α (.forallE α (.sort .zero))

def eqApp (eqPos : Nat) (l : FLevel) (α fe₁ fe₂ : FExpr) : FExpr :=
  .ind eqPos 0 #[l] #[α, fe₁] #[fe₂]

def compatType (eqPos : Nat) (l : FLevel) (α r β ff : FExpr) : FExpr :=
  .forallE α (.forallE α (.forallE (.app (.app r (.bvar 1)) (.bvar 0))
    (eqApp eqPos l β (.app ff (.bvar 2)) (.app ff (.bvar 1)))))

def quotMotiveType (pos : Nat) (l : FLevel) (α r : FExpr) : FExpr :=
  .forallE (.quot pos l α r) (.sort .zero)

def quotMinorType (pos : Nat) (l : FLevel) (α r β : FExpr) : FExpr :=
  .forallE α (.app β (.quotMk pos l α r (.bvar 0)))

def quotTerm (pos eqPos : Nat) : Export.QuotKind → List FLevel → Except Failure FExpr
  | .type, [u] =>
    pure (lamTele 0 #[.sort u, relType (.fvar 0)] (.quot pos u (.fvar 0) (.fvar 1)))
  | .ctor, [u] =>
    pure (lamTele 0 #[.sort u, relType (.fvar 0), .fvar 0]
      (.quotMk pos u (.fvar 0) (.fvar 1) (.fvar 2)))
  | .lift, [u, v] =>
    pure (lamTele 0
      #[.sort u, relType (.fvar 0), .sort v, .forallE (.fvar 0) (.fvar 2),
        compatType eqPos v (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3),
        .quot pos u (.fvar 0) (.fvar 1)]
      (.quotLift pos u v (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3) (.fvar 4) (.fvar 5)))
  | .ind, [u] =>
    pure (lamTele 0
      #[.sort u, relType (.fvar 0), quotMotiveType pos u (.fvar 0) (.fvar 1),
        quotMinorType pos u (.fvar 0) (.fvar 1) (.fvar 2), .quot pos u (.fvar 0) (.fvar 1)]
      (.quotInd pos u (.fvar 0) (.fvar 1) (.fvar 2) (.fvar 3) (.fvar 4)))
  | _, _ => throw (.reject .arity)

end FExpr

theorem FExpr.Denotes.relType {α : FExpr} {α' : Expr E.1 ℓ n} :
    FExpr.Denotes L E 0 α α' →
    FExpr.Denotes L E 0 (FExpr.relType α) (Quot.relType α') := fun hα =>
  .forallE hα (.forallE hα.wkOpen (.sort .zero))

theorem FExpr.Denotes.eqApp {k eqPos : Nat} {ηeq : Head E.1 (.inductive Eq.sig)}
    (hη : E.1.lookup eqPos = some ⟨.inductive Eq.sig, ηeq⟩) {l : FLevel} {l' : RawLevel ℓ}
    {α fe₁ fe₂ : FExpr} {α' e₁ e₂ : Expr E.1 ℓ n} :
    FLevel.Denotes l l' →
    FExpr.Denotes L E k α α' →
    FExpr.Denotes L E k fe₁ e₁ →
    FExpr.Denotes L E k fe₂ e₂ →
    FExpr.Denotes L E k (FExpr.eqApp eqPos l α fe₁ fe₂) (Quot.eqApp ηeq ⟦l'⟧ α' e₁ e₂) :=
  fun hl hα he₁ he₂ =>
    .ind rfl rfl rfl hη rfl
      (fun _ => by simpa using hl)
      (fun | ⟨0, _⟩ => hα | ⟨1, _⟩ => he₁)
      (fun ⟨0, _⟩ => he₂)

theorem FExpr.Denotes.compatType {eqPos : Nat} {ηeq : Head E.1 (.inductive Eq.sig)}
    (hη : E.1.lookup eqPos = some ⟨.inductive Eq.sig, ηeq⟩) {l : FLevel} {l' : RawLevel ℓ}
    {α r β ff : FExpr} {α' r' β' f : Expr E.1 ℓ n} :
    FLevel.Denotes l l' →
    FExpr.Denotes L E 0 α α' →
    FExpr.Denotes L E 0 r r' →
    FExpr.Denotes L E 0 β β' →
    FExpr.Denotes L E 0 ff f →
    FExpr.Denotes L E 0 (FExpr.compatType eqPos l α r β ff) (Quot.compatType ηeq ⟦l'⟧ α' r' β' f) :=
  fun hl hα hr hβ hf => .forallE hα (.forallE hα.wkOpen (.forallE
    (.app (.app (hr.wkNOpen 2) (.bvar (by omega) (by decide))) (.bvar (by omega) (by decide)))
    (FExpr.Denotes.eqApp hη hl
      (hβ.wkNOpen 3)
      (.app (hf.wkNOpen 3) (.bvar (by omega) (by decide)))
      (.app (hf.wkNOpen 3) (.bvar (by omega) (by decide))))))

theorem FExpr.Denotes.quotMotiveType {pos : Nat} {η : Head E.1 .quot}
    (hη : E.1.lookup pos = some ⟨.quot, η⟩) {l : FLevel} {l' : RawLevel ℓ} {α r : FExpr}
    {α' r' : Expr E.1 ℓ n} :
    FLevel.Denotes l l' →
    FExpr.Denotes L E 0 α α' →
    FExpr.Denotes L E 0 r r' →
    FExpr.Denotes L E 0 (FExpr.quotMotiveType pos l α r) (Quot.motiveType η ⟦l'⟧ α' r') :=
  fun hl hα hr => .forallE (.quot hη hl hα hr) (.sort .zero)

theorem FExpr.Denotes.quotMinorType {pos : Nat} {η : Head E.1 .quot}
    (hη : E.1.lookup pos = some ⟨.quot, η⟩) {l : FLevel} {l' : RawLevel ℓ} {α r β : FExpr}
    {α' r' β' : Expr E.1 ℓ n} :
    FLevel.Denotes l l' →
    FExpr.Denotes L E 0 α α' →
    FExpr.Denotes L E 0 r r' →
    FExpr.Denotes L E 0 β β' →
    FExpr.Denotes L E 0 (FExpr.quotMinorType pos l α r β) (Quot.minorType η ⟦l'⟧ α' r' β') :=
  fun hl hα hr hβ =>
    .forallE hα (.app hβ.wkOpen (.quotMk hη hl hα.wkOpen hr.wkOpen (.bvar (by omega) (by decide))))

end Metalean.FastChecker
