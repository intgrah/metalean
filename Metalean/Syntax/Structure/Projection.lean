/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Structure
import Metalean.Syntax.Substitution

@[expose] public section

namespace Metalean.Inductive

variable {ζ : Sigs} {ℓ n m : Nat} {ι : IndSig}
  {s : Fin ι.nsorts} {c : Fin (ι.nctors s)} {I : Inductive ζ ι}
  (h : I.IsStructure s c)
  (η : Head ζ (.inductive ι))
  (ls : Fin ι.nlevels → Level ℓ)
  (ps : Fin ι.nparams → Expr ζ ℓ n)
  (ms : Fin ι.nsorts → Expr ζ ℓ n)
  (f : Fin (ι.ctors s c).nfields)
  (maj : Expr ζ ℓ n)
  (σ : Subst ζ ℓ n m)
  (cut : Nat)

@[simp] theorem IsStructure.projTypeWith_subst
    (previous : Fin f.val → Expr ζ ℓ n)
    (σ : Subst ζ ℓ n m) :
    (projTypeWith I ls ps f previous).subst σ =
      projTypeWith I ls (fun param => (ps param).subst σ)
        f fun prior => (previous prior).subst σ := by
  simp [projTypeWith]

@[simp] theorem IsStructure.projTypeWith_wkFrom
    (previous : Fin f.val → Expr ζ ℓ n) (cut : Nat) :
    (projTypeWith I ls ps f previous).wkFrom cut =
      projTypeWith I ls (fun param => (ps param).wkFrom cut)
        f fun prior => (previous prior).wkFrom cut := by
  let ρ : Ren n (n + 1) := Ren.wkFrom cut
  have hrename (e : Expr ζ ℓ n) :
      e.subst (fun v => .var (ρ v)) = e.rename ρ := by
    rw [← Expr.subst_id (e.rename ρ), Expr.rename_subst]
    rfl
  simpa [Expr.wkFrom, hrename] using
    IsStructure.projTypeWith_subst ls ps f previous fun v => .var (ρ v)

include h

theorem IsStructure.projection_subst :
    (h.projection η ls ps f maj).map (Expr.subst σ) (Expr.subst σ) =
      h.projection η ls (fun param => (ps param).subst σ)
        f (maj.subst σ) := by
  fun_induction h.projection η ls ps f maj generalizing m with
  | case1 η ps f maj previous type u ms cases ihMajor ihMotive =>
    have ihMajorTerm := fun previous => congrArg Prod.snd (ihMajor previous σ)
    have ihMotiveTerm := fun previous => congrArg Prod.snd
      (ihMotive previous (σ.liftN (ι.nindices s + 1)))
    simp [Expr.subst] at ihMajorTerm ihMotiveTerm
    rw [projection, Prod.map]
    congr 1
    · rw [projTypeWith_subst]
      congr 1
      funext previous
      exact ihMajorTerm previous
    · simp only [Expr.subst]
      congr 1
      · funext other
        have hs := h.sort_unique other
        subst other
        simp [ms, ihMotiveTerm]
      · funext other otherCtor
        have hs := h.sort_unique other
        subst other
        have hc := h.ctor_unique otherCtor
        subst otherCtor
        rw [Ctx.lam_subst₃]
        change Ctx.lam
            (((ι.ctors s c).caseOrdinary f).subst
              ((ι.ctors s c).liftCaseSubst σ)) _ = _
        simp [ms, ihMotiveTerm]
      · exact funext h.no_indices.elim

theorem IsStructure.projection_wkFrom :
    (h.projection η ls ps f maj).map (Expr.wkFrom cut) (Expr.wkFrom cut) =
      h.projection η ls (fun param => (ps param).wkFrom cut)
        f (maj.wkFrom cut) := by
  simpa [Prod.map, Expr.wkFrom] using
    h.projection_subst η ls ps f maj fun v => .var (Ren.wkFrom cut v)

theorem IsStructure.motiveTeleHead :
    Expr.ind η s ls
        (fun param => (ps param).wkN (ι.nindices s))
        (fun index => .var ⟨n + index.val, by omega⟩) ≍
      Expr.ind η s ls ps h.indices := by
  have hni := Fin.eq_zero_of_isEmpty h.no_indices
  have hps : (fun param => (ps param).wkN (ι.nindices s)) ≍ ps := by
    refine Function.hfunext rfl ?_
    intro param param' hparam
    cases eq_of_heq hparam
    rw [hni]
    rfl
  have his :
      (fun index : Fin (ι.nindices s) =>
        (.var ⟨n + index.val, by omega⟩ : Expr ζ ℓ (n + ι.nindices s))) ≍
        (h.indices : Fin (ι.nindices s) → Expr ζ ℓ n) :=
    Function.hfunext rfl fun index => h.no_indices.elim index
  exact congr(Expr.ind (n := $(by omega)) $rfl $rfl $rfl $hps $his)

theorem IsStructure.foldr_indexTele
    {K : ∀ {k : Nat}, Expr ζ ℓ k → Expr ζ ℓ (k + 1) → Expr ζ ℓ k}
    {e₁ : Expr ζ ℓ (n + ι.nindices s)} {e₂ : Expr ζ ℓ n} (he : e₁ ≍ e₂) :
    Tele.foldr K e₁ (I.indexTele ls s ps) = e₂ := by
  have hni := Fin.eq_zero_of_isEmpty h.no_indices
  exact eq_of_heq
    (show Tele.foldr K e₁ (I.indexTele ls s ps) ≍ Tele.foldr K e₂ #t[] from
      congr(Tele.foldr (b := $(by omega)) $rfl $he
        $((I.indexTele ls s ps).heq_nil (by omega))))

theorem IsStructure.projectionMotiveLam :
    Ctx.lam
        (projTypeWith I ls
          (fun param => (ps param).wkN (ι.nindices s + 1)) f
          (fun previous => h.projTerm η ls
            (fun param => (ps param).wkN (ι.nindices s + 1))
            (previous.castLT (previous.isLt.trans f.isLt))
            (.var (Fin.last (n + ι.nindices s)))))
        (I.motiveTele η ls ps s) =
      .lam (.ind η s ls ps h.indices)
        (projTypeWith I ls (fun param => (ps param).wk) f
          (fun previous => h.projTerm η ls
            (fun param => (ps param).wk)
            (previous.castLT (previous.isLt.trans f.isLt))
            (.var (Fin.last n)))) := by
  have hni := Fin.eq_zero_of_isEmpty h.no_indices
  have hbody :
      projTypeWith I ls
          (fun param => (ps param).wkN (ι.nindices s + 1)) f
          (fun previous => h.projTerm η ls
            (fun param => (ps param).wkN (ι.nindices s + 1))
            (previous.castLT (previous.isLt.trans f.isLt))
            (.var (Fin.last (n + ι.nindices s)))) ≍
        projTypeWith I ls (fun param => (ps param).wk) f
          (fun previous => h.projTerm η ls
            (fun param => (ps param).wk)
            (previous.castLT (previous.isLt.trans f.isLt))
            (.var (Fin.last n))) := by
    have hps :
        (fun param => ((ps param).wkN (ι.nindices s)).wk) ≍
          (fun param => (ps param).wk) := by
      refine Function.hfunext rfl ?_
      intro param param' hparam
      cases eq_of_heq hparam
      rw [hni]
      rfl
    have hmaj :
        (Expr.var (Fin.last (n + ι.nindices s)) :
            Expr ζ ℓ (n + ι.nindices s + 1)) ≍
          (Expr.var (Fin.last n) : Expr ζ ℓ (n + 1)) := by
      have hv : Fin.last (n + ι.nindices s) ≍ Fin.last n :=
        (Fin.heq_ext_iff (by omega)).2 (by simp; exact hni)
      exact congr(Expr.var (n := $(by omega)) $hv)
    congr 1
    · omega
    · refine Function.hfunext rfl ?_
      intro previous previous' hprevious
      cases eq_of_heq hprevious
      congr 1
      omega
  exact h.foldr_indexTele ls ps
    congr(Expr.lam (n := $(by omega)) $(h.motiveTeleHead η ls ps) $hbody)

theorem IsStructure.projectionMotives_self :
    h.projectionMotives η ls ps f s =
      .lam (.ind η s ls ps h.indices)
        (h.projType η ls (fun p => (ps p).wk) f (.var (Fin.last n))) := by
  change Ctx.lam _ _ = _
  rw [h.projectionMotiveLam, projType, projection]
  rfl

theorem IsStructure.caseTeleOrdinary :
    I.caseTele η ls ps ms s c ≍
      (I.ctors s c).ordinaryFieldTele η ls ps := by
  have hnr := Fin.eq_zero_of_isEmpty h.no_recursive
  unfold Inductive.caseTele Ctor.fieldTele
  rw [Tele.append_assoc]
  refine HEq.trans ?_ (heq_of_eq (Tele.append_nil _))
  simp only [HAppend.hAppend]
  congr 1
  · omega
  · apply Tele.heq_nil
    omega

theorem IsStructure.caseOrdinaryField :
    ((ι.ctors s c).caseOrdinary f :
        Expr ζ ℓ
          (n + (ι.ctors s c).nfields +
            (ι.ctors s c).nrecFields +
            (ι.ctors s c).nrecFields)) ≍
      (Expr.boundVars n (ι.ctors s c).nfields 0 f :
        Expr ζ ℓ (n + (ι.ctors s c).nfields)) := by
  have hnr := Fin.eq_zero_of_isEmpty h.no_recursive
  simp [CtorSig.caseOrdinary, CtorSig.fieldOrdinary]
  congr 1
  · omega
  · exact (Fin.heq_ext_iff (by omega)).2 rfl

theorem IsStructure.projectionCases_self :
    h.projectionCases η ls ps f ms s c =
      Ctx.lam (Expr.boundVars n (ι.ctors s c).nfields 0 f)
        ((I.ctors s c).ordinaryFieldTele η ls ps) :=
  have hnr := Fin.eq_zero_of_isEmpty h.no_recursive
  eq_of_heq (congr(Ctx.lam (n := $(by omega))
    $(h.caseOrdinaryField f) $(h.caseTeleOrdinary η ls ps ms)))

theorem IsStructure.projType_eq_projTypeWith :
    h.projType η ls ps f maj =
      projTypeWith I ls ps f fun prior =>
        h.projTerm η ls ps (prior.castLE f.isLt.le) maj := by
  rw [projType, projection]
  rfl

theorem IsStructure.projType_eq :
    h.projType η ls ps f maj =
      (I.ctors s c).ordinaryFieldExpr ls ps
        (fun current => h.projTerm η ls ps current maj) f := by
  rw [projType, projection]
  rfl

@[simp] theorem IsStructure.projType_subst :
    (h.projType η ls ps f maj).subst σ =
      h.projType η ls (fun param => (ps param).subst σ)
        f (maj.subst σ) :=
  congrArg Prod.fst (h.projection_subst η ls ps f maj σ)

@[simp] theorem IsStructure.projTerm_subst :
    (h.projTerm η ls ps f maj).subst σ =
      h.projTerm η ls (fun param => (ps param).subst σ)
        f (maj.subst σ) :=
  congrArg Prod.snd (h.projection_subst η ls ps f maj σ)

@[simp] theorem IsStructure.projTerm_wkFrom :
    (h.projTerm η ls ps f maj).wkFrom cut =
      h.projTerm η ls (fun param => (ps param).wkFrom cut)
        f (maj.wkFrom cut) :=
  congrArg Prod.snd (h.projection_wkFrom η ls ps f maj cut)

theorem IsStructure.projectionMotives_subst (other : Fin ι.nsorts) :
    (h.projectionMotives η ls ps f other).subst σ =
      h.projectionMotives η ls (fun param => (ps param).subst σ) f other := by
  have he := h.projTerm_subst η ls ps f (.sort .zero) σ
  rw [projTerm_eq_recr, projTerm_eq_recr] at he
  injection he with _ _ _ _ _ _ _ hms
  exact congrFun hms other

theorem IsStructure.projectionMotives_wkN (k : Nat) (other : Fin ι.nsorts) :
    (h.projectionMotives η ls ps f other).wkN k =
      h.projectionMotives η ls (fun param => (ps param).wkN k) f other := by
  rw [Expr.wkN_eq_subst, h.projectionMotives_subst]
  congr 1
  funext param
  rw [Expr.wkN_eq_subst]

theorem IsStructure.motiveType_self (l : Level ℓ) :
    I.motiveType η ls ps l s = .forallE (.ind η s ls ps h.indices) (.sort l) := by
  have hni := Fin.eq_zero_of_isEmpty h.no_indices
  have hsort : (Expr.sort l : Expr ζ ℓ (n + ι.nindices s + 1)) ≍
      (Expr.sort l : Expr ζ ℓ (n + 1)) :=
    congr(Expr.sort (n := $(by omega)) $rfl)
  exact h.foldr_indexTele ls ps
    congr(Expr.forallE (n := $(by omega)) $(h.motiveTeleHead η ls ps) $hsort)

@[simp] theorem IsStructure.rebuildTerm_subst :
    (h.rebuildTerm η ls ps maj).subst σ =
      h.rebuildTerm η ls (fun param => (ps param).subst σ)
        (maj.subst σ) := by
  simp only [rebuildTerm, Expr.subst]
  congr 1
  · funext f
    exact h.projTerm_subst η ls ps f maj σ
  · exact funext h.no_recursive.elim

@[simp] theorem IsStructure.rebuildTerm_wkFrom :
    (h.rebuildTerm η ls ps maj).wkFrom cut =
      h.rebuildTerm η ls (fun param => (ps param).wkFrom cut)
        (maj.wkFrom cut) := by
  simp only [rebuildTerm, Expr.wkFrom_ctor]
  congr 1
  · funext f
    exact h.projTerm_wkFrom η ls ps f maj cut
  · exact funext h.no_recursive.elim

end Metalean.Inductive
