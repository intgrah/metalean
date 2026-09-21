/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.TypeTheory.Syntactic.Section
public import Metalean.Strong.Structure
public import Metalean.Semantics.Interpretation.Recursor.Fields
public import Metalean.TypeTheory.Syntactic.Telescope
import Metalean.TypeTheory.Syntactic.Comprehension
import Metalean.Syntax.Structure.Projection
import Metalean.Typing.Weakening

@[expose] public section

namespace Metalean.CoherentShape

variable {ζ : Sigs} {E : Env ζ} {ℓ : Nat}

open CategoryTheory Presheaf TypeTheory NaturalModel

variable {Γ₁ Γ₂ Γ₃ : CtxCat E ℓ} {ι : IndSig} {η : Head ζ (.inductive ι)} {s : Fin ι.nsorts}
  {c : Fin (ι.nctors s)} {ls : Fin ι.nlevels → Level ℓ} {l : Level ℓ}
  {ps : Fin ι.nparams → Expr ζ ℓ Γ₁.as.len} {ms : Fin ι.nsorts → Expr ζ ℓ Γ₁.as.len}
  {mins : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₁.as.len}

section Fields

variable (h : IndData Γ₁ η ls ps) (s : Fin ι.nsorts) (c : Fin (ι.nctors s))

def baseVar (v : Var Γ₁.as.len) : Var (CtxCat.ctorFields h s c).as.len :=
  (v.castAdd (ι.ctors s c).nfields).castAdd (ι.ctors s c).nrecFields

def fieldVar (i : Fin (CtorHead.mk η s c).arity) : Var (CtxCat.ctorFields h s c).as.len :=
  ⟨Γ₁.as.len + i.val, by
    have := i.isLt
    simp only [CtorHead.arity, CtorHead.sig] at this ⊢
    omega⟩

theorem fieldVar_natAdd (f : Fin (ι.ctors s c).nrecFields) :
    fieldVar h s c (Fin.natAdd (ι.ctors s c).nfields f) =
      Fin.natAdd (Γ₁.as.len + (ι.ctors s c).nfields) f := by
  ext
  simp [fieldVar, Nat.add_assoc]

theorem CtxCat.ctorFields_get_ordinary (f : Fin (ι.ctors s c).nfields) :
    Ctx.get (fieldVar h s c (Fin.castAdd (ι.ctors s c).nrecFields f))
        (CtxCat.ctorFields h s c).as.ctx =
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary f := by
  change Ctx.get ⟨Γ₁.as.len + f.val, by omega⟩
    (Γ₁.as.ctx ++ ((E.get η).block.ctors s c).fieldTele η ls ps) = _
  rw [← Expr.subst_id (Ctx.get _ _), Ctx.get_subst _ Subst.id _ (Γ₁.as.len + f.val) (by omega) rfl,
    Ctx.entry_append_right Γ₁.as.ctx _ (Nat.zero_le _) (by omega) (by omega), Ctor.fieldTele,
    Ctx.entry_append_left _ _ (by omega) (by omega) (by omega), Ctor.ordinaryFieldTele,
    Ctor.ordinaryFieldTeleAux_entry, Subst.liftN_eq_append, Expr.subst_subst]
  congr 1
  funext v
  cases v using Fin.addCases with
  | left param =>
    simp only [Subst.comp, Fin.append_left, CtorSig.fieldParams,
      Expr.wkN_eq_rename, Expr.rename_subst, Expr.rename_rename]
    rw [← Expr.subst_vars]
    rfl
  | right prior =>
    simp only [Subst.comp, Fin.append_right, CtorSig.fieldOrdinary, Expr.var_wkN]
    rfl

theorem CtxCat.ctorFields_get_recursive (f : Fin (ι.ctors s c).nrecFields) :
    Ctx.get (fieldVar h s c (Fin.natAdd (ι.ctors s c).nfields f))
        (CtxCat.ctorFields h s c).as.ctx =
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary f := by
  rw [fieldVar_natAdd]
  change Ctx.get (Fin.natAdd (Γ₁.as.len + (ι.ctors s c).nfields) f)
    (Γ₁.as.ctx ++ ((E.get η).block.ctors s c).fieldTele η ls ps) = _
  erw [Ctor.fieldTele, ← Tele.append_assoc,
    Ctor.recursiveFieldTeleAux, Ctx.get_append_ofTypes, RecField.instantiatedType_wkN]
  have hsubst :
      (fun v => ((Fin.append (fun i => (ps i).wkN (ι.ctors s c).nfields)
          (Expr.boundVars Γ₁.as.len (ι.ctors s c).nfields 0)) v).wkN
            (ι.ctors s c).nrecFields) =
        Fin.append ((ι.ctors s c).fieldParams ps)
          (ι.ctors s c).fieldOrdinary := by
    rw [CtorSig.targetSubst_fields]
    funext v
    exact Expr.wkN_eq_rename _ _
  rw [hsubst]
  rfl

theorem CtxCat.ctorFields_get_base (v : Var Γ₁.as.len) :
    Ctx.get (baseVar h s c v) (CtxCat.ctorFields h s c).as.ctx =
      ((Γ₁.as.ctx.get v).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields := by
  change Ctx.get ((v.castAdd _).castAdd _) (Γ₁.as.ctx ++ (((E.get η).block.ctors s c).ordinaryFieldTele η ls ps ++
    ((E.get η).block.ctors s c).recursiveFieldTele η ls (fun p => (ps p).wkN (ι.ctors s c).nfields)
      (Expr.boundVars Γ₁.as.len (ι.ctors s c).nfields 0))) = _
  rw [← Tele.append_assoc, Ctx.get_append, Ctx.get_append]

include h in
noncomputable abbrev CtxCat.majorCtx (hstruct : (E.get η).block.IsStructure s c) : CtxCat E ℓ :=
  Γ₁.extension (hstruct.indTypeStrong h.param)

variable (ls ps) in
noncomputable def projField (hstruct : (E.get η).block.IsStructure s c)
    (f : Fin (ι.ctors s c).nfields) : Expr ζ ℓ (Γ₁.as.len + 1) :=
  hstruct.projTerm η ls (fun p => (ps p).wk) f (.var (Fin.last Γ₁.as.len))

noncomputable def projSubst (hstruct : (E.get η).block.IsStructure s c) :
    Subst ζ ℓ (CtxCat.ctorFields h s c).as.len (CtxCat.majorCtx h s c hstruct).as.len :=
  Fin.append (Fin.append Subst.wk (projField ls ps s c hstruct)) hstruct.recursive

theorem projSubst_base (hstruct : (E.get η).block.IsStructure s c) (v : Var Γ₁.as.len) :
    projSubst h s c hstruct (baseVar h s c v) = .var v.castSucc :=
  (Fin.append_left _ hstruct.recursive (v.castAdd (ι.ctors s c).nfields)).trans
    (Fin.append_left Subst.wk (projField ls ps s c hstruct) v)

theorem projSubst_ordinary (hstruct : (E.get η).block.IsStructure s c)
    (f : Fin (ι.ctors s c).nfields) :
    projSubst h s c hstruct (fieldVar h s c (Fin.castAdd (ι.ctors s c).nrecFields f)) =
      projField ls ps s c hstruct f :=
  (Fin.append_left _ hstruct.recursive ⟨Γ₁.as.len + f.val, by omega⟩).trans
    (Fin.append_right Subst.wk (projField ls ps s c hstruct) f)

theorem ordinaryFieldExpr_projSubst (hstruct : (E.get η).block.IsStructure s c)
    (f : Fin (ι.ctors s c).nfields) :
    (((E.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary f).subst (projSubst h s c hstruct) =
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls (fun p => (ps p).wk)
        (projField ls ps s c hstruct) f := by
  rw [Ctor.ordinaryFieldExpr_subst]
  congr 1
  · exact funext fun p =>
      ((Expr.wkN_subst_append _ _ _).trans (Expr.wkN_subst_append _ _ _)).trans (Expr.subst_wk (ps p))
  · exact funext fun f =>
      (Expr.wkN_subst_append _ _ _).trans (Fin.append_right Subst.wk (projField ls ps s c hstruct) f)

theorem projSubstWF (hstruct : (E.get η).block.IsStructure s c) :
    E[(CtxCat.majorCtx h s c hstruct).as.ctx] ⊢ₛ projSubst h s c hstruct ⊣
      (CtxCat.ctorFields h s c).as.ctx := by
  intro v
  cases v using Fin.addCases with
  | left v =>
    cases v using Fin.addCases with
    | left v =>
      simpa [projSubst, Subst.wk, Ctor.fieldTele, ← Tele.append_assoc, Expr.subst_wk] using
        (CtxCat.majorCtx h s c hstruct).as.wf.var v.castSucc
    | right f =>
      erw [projSubst_ordinary h s c hstruct f, CtxCat.ctorFields_get_ordinary,
        ordinaryFieldExpr_projSubst]
      change E[_] ⊢ₛ _ : ((E.get η).block.ctors s c).ordinaryFieldExpr ls (fun p => (ps p).wk)
        (fun current => hstruct.projTerm η ls (fun p => (ps p).wk) current
          (.var (Fin.last Γ₁.as.len))) _
      erw [← Inductive.IsStructure.projType_eq]
      exact hstruct.projTerm_genericStrong h.block f Γ₁.as.wf h.param
  | right f => exact hstruct.no_recursive.elim f

noncomputable def projHom (hstruct : (E.get η).block.IsStructure s c) :
    (CtxCat.majorCtx h s c hstruct).as ⟶ (CtxCat.ctorFields h s c).as where
  subst := projSubst h s c hstruct
  typed := projSubstWF h s c hstruct

theorem map_projHom_varLabel_base (hstruct : (E.get η).block.IsStructure s c)
    (v : Var Γ₁.as.len) :
    (Tm E ℓ).map (RawCtx.toCtx.map (projHom h s c hstruct)).op
        (Tm.varLabel (CtxCat.ctorFields h s c) (baseVar h s c v)) =
      Tm.varLabel (CtxCat.majorCtx h s c hstruct) v.castSucc := by
  exact Tm.label_eq_var _ (projSubst_base h s c hstruct v)

theorem projHom_one_ordinary (hstruct : (E.get η).block.IsStructure s c)
    {maj : Expr ζ ℓ Γ₁.as.len} (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps hstruct.indices)
    (f : Fin (ι.ctors s c).nfields) :
    (RawCtx.Hom.one ⟨_, hstruct.indTypeStrong h.param⟩ hmaj ≫ projHom h s c hstruct).subst
        (fieldVar h s c (Fin.castAdd (ι.ctors s c).nrecFields f)) =
      hstruct.projTerm η ls ps f maj := by
  change (projSubst h s c hstruct (fieldVar h s c (Fin.castAdd (ι.ctors s c).nrecFields f))).subst
    (Subst.id.extend maj) = _
  rw [projSubst_ordinary, projField]
  simp [Expr.wk_subst_extend, Expr.subst]

theorem projHom_one_get_ordinary (hstruct : (E.get η).block.IsStructure s c)
    {maj : Expr ζ ℓ Γ₁.as.len} (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps hstruct.indices)
    (f : Fin (ι.ctors s c).nfields) :
    (Ctx.get (fieldVar h s c (Fin.castAdd (ι.ctors s c).nrecFields f))
        (CtxCat.ctorFields h s c).as.ctx).subst
      (RawCtx.Hom.one ⟨_, hstruct.indTypeStrong h.param⟩ hmaj ≫ projHom h s c hstruct).subst =
      hstruct.projType η ls ps f maj := by
  rw [CtxCat.ctorFields_get_ordinary]
  refine (Expr.subst_subst (projSubst h s c hstruct)
    (RawCtx.Hom.one ⟨_, hstruct.indTypeStrong h.param⟩ hmaj).subst _).symm.trans ?_
  rw [ordinaryFieldExpr_projSubst]
  change (((E.get η).block.ctors s c).ordinaryFieldExpr ls (fun p => (ps p).wk)
    (fun current => hstruct.projTerm η ls (fun p => (ps p).wk) current
      (.var (Fin.last Γ₁.as.len))) f).subst (Subst.id.extend maj) = _
  rw [← Inductive.IsStructure.projType_eq]
  simp [Expr.wk_subst_extend, Expr.subst]

end Fields

structure CtorSection (h : RecData Γ₁ η ls l ps ms mins) (s : Fin ι.nsorts)
    (c : Fin (ι.nctors s)) (σ : Γ₂ ⟶ Γ₁) where
  hom : Γ₂ ⟶ CtxCat.ctorFields h.toIndData s c
  base (v : Var Γ₁.as.len) :
    (Tm E ℓ).map hom.op
        (Tm.varLabel (CtxCat.ctorFields h.toIndData s c) (baseVar h.toIndData s c v)) =
      (Tm E ℓ).map σ.op (Tm.varLabel Γ₁ v)

namespace CtorSection

variable {h : RecData Γ₁ η ls l ps ms mins} {σ₁ σ₂ : Γ₂ ⟶ Γ₁}

noncomputable def names (sect : CtorSection h s c σ₁) :
    Fin (CtorHead.mk η s c).arity → Tm_ Γ₂ :=
  fun i => (Tm E ℓ).map sect.hom.op
    (Tm.varLabel (CtxCat.ctorFields h.toIndData s c) (fieldVar h.toIndData s c i))

noncomputable def ihName (sect : CtorSection h s c σ₁) (f : Fin (ι.ctors s c).nrecFields) :
    Tm_ Γ₂ :=
  (Tm E ℓ).map sect.hom.op ((CtorInstance.generic h.toIndData s c).ihName (h.fields s c) f)

def congr (sect : CtorSection h s c σ₁) (hσ : σ₁ = σ₂) : CtorSection h s c σ₂ where
  hom := sect.hom
  base v := by cases hσ; exact sect.base v

@[simp] theorem names_congr (sect : CtorSection h s c σ₁) (hσ : σ₁ = σ₂) :
    (sect.congr hσ).names = sect.names := rfl

@[simp] theorem ihName_congr (sect : CtorSection h s c σ₁) (hσ : σ₁ = σ₂)
    (f : Fin (ι.ctors s c).nrecFields) : (sect.congr hσ).ihName f = sect.ihName f := rfl

def pullback (sect : CtorSection h s c σ₁) (σ₃ : Γ₃ ⟶ Γ₂) : CtorSection h s c (σ₃ ≫ σ₁) where
  hom := σ₃ ≫ sect.hom
  base v := by
    rw [op_comp, Functor.map_comp_apply, sect.base v, ← Functor.map_comp_apply, ← op_comp]

@[simp] theorem hom_pullback (sect : CtorSection h s c σ₁) (σ₃ : Γ₃ ⟶ Γ₂) :
    (sect.pullback σ₃).hom = σ₃ ≫ sect.hom :=
  rfl

@[simp] theorem names_pullback (sect : CtorSection h s c σ₁) (σ₃ : Γ₃ ⟶ Γ₂) :
    (sect.pullback σ₃).names = fun i => (Tm E ℓ).map σ₃.op (sect.names i) := by
  funext i
  simp [names]

@[simp] theorem ihName_pullback (sect : CtorSection h s c σ₁) (σ₃ : Γ₃ ⟶ Γ₂)
    (f : Fin (ι.ctors s c).nrecFields) :
    (sect.pullback σ₃).ihName f = (Tm E ℓ).map σ₃.op (sect.ihName f) := by
  rw [ihName, ihName, hom_pullback, op_comp, Functor.map_comp_apply]

@[ext] theorem ext {sect sect₁ : CtorSection h s c σ₁} (hhom : sect.hom = sect₁.hom) :
    sect = sect₁ := by
  cases sect
  cases sect₁
  cases hhom
  rfl

theorem eq_of_names_eq {sect sect₁ : CtorSection h s c σ₁} (hn : sect.names = sect₁.names) :
    sect = sect₁ := by
  apply CtorSection.ext
  apply Tm.hom_ext
  intro v
  cases v using Fin.addCases with
  | left v =>
    cases v using Fin.addCases with
    | left v => exact (sect.base v).trans (sect₁.base v).symm
    | right f => exact congrFun hn (f.castAdd _)
  | right f => simpa [CtorSection.names, fieldVar_natAdd] using congrFun hn (Fin.natAdd _ f)

noncomputable def ofMajor (hstruct : (E.get η).block.IsStructure s c)
    {majorName : Tm_ Γ₂}
    (msect : Raw.ContextSection (hstruct.indTypeStrong h.param) σ₁ majorName) :
    CtorSection h s c σ₁ where
  hom := msect.hom ≫ RawCtx.toCtx.map (projHom h.toIndData s c hstruct)
  base v := by
    rw [op_comp, Functor.map_comp_apply, map_projHom_varLabel_base,
      ← Tm.map_rawProjection_varLabel, ← Functor.map_comp_apply, ← op_comp, msect.over]

def ProjectsFrom (sect : CtorSection h s c σ₁) (hstruct : (E.get η).block.IsStructure s c)
    (majorName : Tm_ Γ₂) : Prop :=
  ∃ msect : Raw.ContextSection (hstruct.indTypeStrong h.param) σ₁ majorName,
    sect.hom = msect.hom ≫ RawCtx.toCtx.map (projHom h.toIndData s c hstruct)

theorem ProjectsFrom.pullback {sect : CtorSection h s c σ₁}
    {hstruct : (E.get η).block.IsStructure s c} {majorName : Tm_ Γ₂}
    (hp : sect.ProjectsFrom hstruct majorName) (σ₃ : Γ₃ ⟶ Γ₂) :
    (sect.pullback σ₃).ProjectsFrom hstruct ((Tm E ℓ).map σ₃.op majorName) :=
  have ⟨msect, hm⟩ := hp
  ⟨msect.pullback σ₃, by rw [CtorSection.hom_pullback, hm]; exact (Category.assoc _ _ _).symm⟩

theorem ProjectsFrom.congr {sect : CtorSection h s c σ₁}
    {hstruct : (E.get η).block.IsStructure s c} {majorName : Tm_ Γ₂}
    (hp : sect.ProjectsFrom hstruct majorName) (hσ : σ₁ = σ₂) :
    (sect.congr hσ).ProjectsFrom hstruct majorName := by
  subst hσ
  exact hp

theorem eq_of_projectsFrom {majorName : Tm_ Γ₂}
    {hstruct : (E.get η).block.IsStructure s c} (sect sect₁ : CtorSection h s c σ₁)
    (hp : sect.ProjectsFrom hstruct majorName) (hp₁ : sect₁.ProjectsFrom hstruct majorName) :
    sect = sect₁ := by
  have ⟨msect, hm⟩ := hp
  have ⟨msect₁, hm₁⟩ := hp₁
  exact CtorSection.ext (by rw [hm, hm₁, Section.hom_eq msect msect₁])

theorem proj_name (sect : CtorSection h s c σ₁) (hs : (E.get η).block.IsStructure s c)
    {maj : Expr ζ ℓ Γ₁.as.len} (hmaj : E[Γ₁.as.ctx] ⊢ₛ maj : .ind η s ls ps hs.indices)
    (hp : sect.ProjectsFrom hs ((Tm E ℓ).map σ₁.op (Tm.label Γ₁.as hmaj)))
    (f : Fin (ι.ctors s c).nfields) :
    sect.names (Fin.castAdd (ι.ctors s c).nrecFields f) =
      (Tm E ℓ).map σ₁.op (Tm.label Γ₁.as
        (hs.projTerm_hasTypeStrong h.block f Γ₁.as.wf h.param hmaj)) := by
  let hA := hs.indTypeStrong h.param
  let ν := RawCtx.Hom.one (⟨_, hA⟩ : E[Γ₁.as.ctx] ⊢ₛ _ typ) hmaj
  let mcanon := (Raw.ContextSection.ofTerm hA hmaj).pullbackId σ₁
  have ⟨msect, hm⟩ := hp
  have hhom : sect.hom = σ₁ ≫ RawCtx.toCtx.map (ν ≫ projHom h.toIndData s c hs) := by
    rw [hm, Section.hom_eq msect mcanon]
    exact (Category.assoc ..).trans (congrArg (σ₁ ≫ ·) (RawCtx.toCtx.map_comp _ _).symm)
  rw [CtorSection.names, hhom, op_comp, Functor.map_comp_apply, Tm.map_varLabel]
  apply congrArg ((Tm E ℓ).map σ₁.op)
  congr 1
  · exact projHom_one_get_ordinary h.toIndData s c hs hmaj f
  · exact projHom_one_ordinary h.toIndData s c hs hmaj f

end CtorSection

namespace CtorInstance

variable {ps₂ : Fin ι.nparams → Expr ζ ℓ Γ₂.as.len} (inst : CtorInstance Γ₂ η s c ls ps₂)

section Subst

variable (h : IndData Γ₁ η ls ps) (σ : Γ₂.as ⟶ Γ₁.as) (hps : ∀ p, (ps p).subst σ.subst = ps₂ p)

def fieldsSubst :
    Subst ζ ℓ (Γ₁.as.len + (ι.ctors s c).nfields + (ι.ctors s c).nrecFields) Γ₂.as.len :=
  Fin.append (Fin.append σ.subst inst.fds) inst.recFds

theorem fieldsSubst_base (v : Var Γ₁.as.len) : inst.fieldsSubst σ (baseVar h s c v) = σ.subst v :=
  (Fin.append_left _ inst.recFds (v.castAdd (ι.ctors s c).nfields)).trans
    (Fin.append_left σ.subst inst.fds v)

theorem fieldsSubst_ordinary (f : Fin (ι.ctors s c).nfields) :
    inst.fieldsSubst σ (fieldVar h s c (Fin.castAdd (ι.ctors s c).nrecFields f)) = inst.fds f :=
  (Fin.append_left _ inst.recFds ⟨Γ₁.as.len + f.val, by omega⟩).trans
    (Fin.append_right σ.subst inst.fds f)

theorem fieldsSubst_recursive (f : Fin (ι.ctors s c).nrecFields) :
    inst.fieldsSubst σ (fieldVar h s c (Fin.natAdd (ι.ctors s c).nfields f)) = inst.recFds f := by
  rw [fieldVar_natAdd]
  exact Fin.append_right _ inst.recFds f

include hps

theorem ordinaryFieldExpr_fieldsSubst (f : Fin (ι.ctors s c).nfields) :
    (((E.get η).block.ctors s c).ordinaryFieldExpr ls ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary f).subst (inst.fieldsSubst σ) =
      ((E.get η).block.ctors s c).ordinaryFieldExpr ls ps₂ inst.fds f := by
  simp [fieldsSubst, CtorSig.fieldParams, CtorSig.fieldOrdinary, Expr.subst, hps]

theorem recursiveFieldExpr_fieldsSubst (f : Fin (ι.ctors s c).nrecFields) :
    (((E.get η).block.ctors s c).recursiveFieldExpr η ls ((ι.ctors s c).fieldParams ps)
        (ι.ctors s c).fieldOrdinary f).subst (inst.fieldsSubst σ) =
      ((E.get η).block.ctors s c).recursiveFieldExpr η ls ps₂ inst.fds f := by
  simp [fieldsSubst, CtorSig.fieldParams, CtorSig.fieldOrdinary, Expr.subst, hps]

def fieldsHom : Γ₂.as ⟶ (CtxCat.ctorFields h s c).as where
  subst := inst.fieldsSubst σ
  typed := by
    intro v
    cases v using Fin.addCases with
    | left v =>
      cases v using Fin.addCases with
      | left v =>
        change E[Γ₂.as.ctx] ⊢ₛ inst.fieldsSubst σ (baseVar h s c v) :
          (Ctx.get (baseVar h s c v) (CtxCat.ctorFields h s c).as.ctx).subst (inst.fieldsSubst σ)
        rw [inst.fieldsSubst_base h σ v, CtxCat.ctorFields_get_base, fieldsSubst, Expr.wkN_subst_append,
          Expr.wkN_subst_append]
        exact σ.typed v
      | right f =>
        change E[Γ₂.as.ctx] ⊢ₛ inst.fieldsSubst σ (fieldVar h s c (Fin.castAdd _ f)) :
          (Ctx.get (fieldVar h s c (Fin.castAdd _ f)) (CtxCat.ctorFields h s c).as.ctx).subst
            (inst.fieldsSubst σ)
        rw [inst.fieldsSubst_ordinary h σ f, CtxCat.ctorFields_get_ordinary,
          inst.ordinaryFieldExpr_fieldsSubst σ hps]
        exact inst.typed.ordinary f
    | right f =>
      rw [← fieldVar_natAdd h s c f, inst.fieldsSubst_recursive h σ f, CtxCat.ctorFields_get_recursive,
        inst.recursiveFieldExpr_fieldsSubst σ hps]
      exact inst.typed.recursive f

theorem map_fieldsHom_baseVar (v : Var Γ₁.as.len) :
    (Tm E ℓ).map (RawCtx.toCtx.map (inst.fieldsHom h σ hps)).op
        (Tm.varLabel (CtxCat.ctorFields h s c) (baseVar h s c v)) =
      (Tm E ℓ).map (RawCtx.toCtx.map σ).op (Tm.varLabel Γ₁ v) := by
  rw [Tm.map_varLabel, Tm.map_varLabel]
  congr 1
  · rw [CtxCat.ctorFields_get_base]
    simp [fieldsHom, fieldsSubst]
  · exact inst.fieldsSubst_base h σ v

theorem map_fieldsHom_fieldVar (i : Fin (CtorHead.mk η s c).arity) :
    (Tm E ℓ).map (RawCtx.toCtx.map (inst.fieldsHom h σ hps)).op
        (Tm.varLabel (CtxCat.ctorFields h s c) (fieldVar h s c i)) = inst.typed.names i := by
  rw [Tm.map_varLabel]
  cases i using Fin.addCases with
  | left f =>
    simp only [CtorTyping.names, Fin.append_left]
    congr 1
    · rw [fieldsHom, CtxCat.ctorFields_get_ordinary, inst.ordinaryFieldExpr_fieldsSubst σ hps]
    · exact inst.fieldsSubst_ordinary h σ f
  | right f =>
    simp only [CtorTyping.names, Fin.append_right]
    congr 1
    · rw [fieldsHom, CtxCat.ctorFields_get_recursive, inst.recursiveFieldExpr_fieldsSubst σ hps]
    · exact inst.fieldsSubst_recursive h σ f

end Subst

variable (h : RecData Γ₁ η ls l ps ms mins) (σ : Γ₂.as ⟶ Γ₁.as) (hps : ∀ p, (ps p).subst σ.subst = ps₂ p)

noncomputable def «section» : CtorSection h s c (RawCtx.toCtx.map σ) where
  hom := RawCtx.toCtx.map (inst.fieldsHom h.toIndData σ hps)
  base := inst.map_fieldsHom_baseVar h.toIndData σ hps

@[simp] theorem names_section : (inst.section h σ hps).names = inst.typed.names :=
  funext (inst.map_fieldsHom_fieldVar h.toIndData σ hps)

variable {ms₂ : Fin ι.nsorts → Expr ζ ℓ Γ₂.as.len}
  {mins₂ : (s : Fin ι.nsorts) → Fin (ι.nctors s) → Expr ζ ℓ Γ₂.as.len}
  (hms : ∀ t, (ms t).subst σ.subst = ms₂ t) (hmins : ∀ t c, (mins t c).subst σ.subst = mins₂ t c)

include hps hms hmins

theorem ih_fieldsSubst (f : Fin (ι.ctors s c).nrecFields) :
    ((generic h.toIndData s c).ih l
      (fun t => ((ms t).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
      (fun t c₁ => ((mins t c₁).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields) f).subst
      (inst.fieldsSubst σ) = inst.ih l ms₂ mins₂ f := by
  simp [ih, generic, fieldsSubst, CtorSig.fieldParams, CtorSig.fieldOrdinary,
    CtorSig.fieldRecursive, Expr.subst, hps, hms, hmins]

omit hmins in
theorem ihType_fieldsSubst (f : Fin (ι.ctors s c).nrecFields) :
    (((E.get η).block.ctors s c).ihTypeWith ls
      (fun t => ((ms t).wkN (ι.ctors s c).nfields).wkN (ι.ctors s c).nrecFields)
      ((ι.ctors s c).fieldParams ps) (generic h.toIndData s c).fds (generic h.toIndData s c).recFds f).subst
      (inst.fieldsSubst σ) =
      ((E.get η).block.ctors s c).ihTypeWith ls ms₂ ps₂ inst.fds inst.recFds f := by
  simp [generic, fieldsSubst, CtorSig.fieldParams, CtorSig.fieldOrdinary,
    CtorSig.fieldRecursive, Expr.subst, hps, hms]

theorem ihName_section (h₂ : RecData Γ₂ η ls l ps₂ ms₂ mins₂) (f : Fin (ι.ctors s c).nrecFields) :
    (inst.section h σ hps).ihName f = inst.ihName h₂ f := by
  change (Tm E ℓ).map (RawCtx.toCtx.map (inst.fieldsHom h.toIndData σ hps)).op
    (Tm.label (CtxCat.ctorFields h.toIndData s c).as ((generic h.toIndData s c).ih_typed (h.fields s c) f)) =
      Tm.label Γ₂.as (inst.ih_typed h₂ f)
  rw [Tm.map_label]
  congr 1 <;> simp [fieldsHom, inst.ihType_fieldsSubst h σ hps hms,
    inst.ih_fieldsSubst h σ hps hms hmins]

end CtorInstance

end Metalean.CoherentShape
