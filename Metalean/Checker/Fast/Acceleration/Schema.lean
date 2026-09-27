/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Checker.Fast.Acceleration.Check
public import Metalean.Checker.Acceleration.Rule
import Metalean.Typing.InstLevel
import Metalean.Typing.Telescope

@[expose] public section

namespace Metalean.Checker.Fast

open Frontend (Failure)

theorem FExpr.NoProj.instFVarsCore {args : Array FExpr} (hargs : ∀ a ∈ args, a.NoProj)
    {fe : FExpr} :
    fe.NoProj →
    (fe.instFVarsCore args).NoProj := by
  intro h
  induction h with
  | bvar i =>
    rw [FExpr.instFVarsCore]
    exact .bvar i
  | fvar i =>
    rw [FExpr.instFVarsCore]
    cases hi : args[i]? with
    | none => exact .fvar i
    | some a => exact hargs a (Array.mem_of_getElem? hi)
  | sort l =>
    rw [FExpr.instFVarsCore]
    exact .sort l
  | const pos ls =>
    rw [FExpr.instFVarsCore]
    exact .const pos ls
  | ind _ _ ihps ihis =>
    rw [FExpr.instFVarsCore]
    refine .ind ?_ ?_ <;> simp only [Array.mem_map] <;> rintro _ ⟨x, hx, rfl⟩
    · exact ihps x hx
    · exact ihis x hx
  | ctor _ _ _ ihps ihfds ihrecFds =>
    rw [FExpr.instFVarsCore]
    refine .ctor ?_ ?_ ?_ <;> simp only [Array.mem_map] <;> rintro _ ⟨x, hx, rfl⟩
    · exact ihps x hx
    · exact ihfds x hx
    · exact ihrecFds x hx
  | recr _ _ _ _ _ ihps ihms ihmins ihis ihmaj =>
    rw [FExpr.instFVarsCore]
    refine .recr ?_ ?_ ?_ ?_ ihmaj <;> simp only [Array.mem_map] <;> rintro _ ⟨x, hx, rfl⟩
    · exact ihps x hx
    · exact ihms x hx
    · exact ihmins x hx
    · exact ihis x hx
  | quot _ _ ihα ihr =>
    rw [FExpr.instFVarsCore]
    exact .quot ihα ihr
  | quotMk _ _ _ ihα ihr iha =>
    rw [FExpr.instFVarsCore]
    exact .quotMk ihα ihr iha
  | quotLift _ _ _ _ _ _ ihα ihr ihβ ihf ihh iha =>
    rw [FExpr.instFVarsCore]
    exact .quotLift ihα ihr ihβ ihf ihh iha
  | quotInd _ _ _ _ _ ihα ihr ihβ ihf iha =>
    rw [FExpr.instFVarsCore]
    exact .quotInd ihα ihr ihβ ihf iha
  | app _ _ ihf iha =>
    rw [FExpr.instFVarsCore]
    exact .app ihf iha
  | lam _ _ iht ihb =>
    rw [FExpr.instFVarsCore]
    exact .lam iht ihb
  | forallE _ _ iht ihb =>
    rw [FExpr.instFVarsCore]
    exact .forallE iht ihb
  | letE _ _ _ iht ihv ihb =>
    rw [FExpr.instFVarsCore]
    exact .letE iht ihv ihb
  | natLit nat num =>
    rw [FExpr.instFVarsCore]
    exact .natLit nat num
  | strLit P str =>
    rw [FExpr.instFVarsCore]
    exact .strLit P str

theorem FExpr.Denotes.levelFree {E : Σ ζ, Env ζ} {n k : Nat} {fe : FExpr}
    {e : Expr E.1 0 n} (ℓ : Nat) (hl : fe.data.hasLevelParam = false) :
    FExpr.Denotes E k fe e →
    FExpr.Denotes E k fe (e{fun p : Param 0 => (p.elim0 : Level ℓ)} : Expr E.1 ℓ n) := by
  intro h
  have h' := h.instL (us := #[]) (σ := fun p : Param 0 => (p.elim0 : RawLevel ℓ)) rfl (fun i => i.elim0)
  have hfe : fe{(#[] : Array FLevel)} = fe := by
    change FExpr.instL #[] fe = fe
    rw [FExpr.instL, hl]
    rfl
  rw [hfe] at h'
  convert h' using 2

theorem FExpr.Denotes.sort_inv {E : Σ ζ, Env ζ} {ℓ n k : Nat} {l : FLevel}
    {es : Expr E.1 ℓ n} :
    FExpr.Denotes E k (.sort l) es →
    ∃ l' : RawLevel ℓ, FLevel.Denotes l l' ∧ es = .sort ⟦l'⟧
  | .sort hl => ⟨_, hl, rfl⟩

section

variable {ζ : Sigs} (E : Env ζ)

structure FEq (a b t : FExpr) : Prop where
  noProjLeft : a.NoProj
  noProjRight : b.NoProj
  noProjType : t.NoProj
  defeq : ∀ ⦃ℓ n : Nat⦄ (Γ : Ctx ζ ℓ 0 n),
    ∃ ea eb et : Expr ζ ℓ n,
      FExpr.Denotes ⟨ζ, E⟩ 0 a ea ∧ FExpr.Denotes ⟨ζ, E⟩ 0 b eb ∧
        FExpr.Denotes ⟨ζ, E⟩ 0 t et ∧ E[Γ] ⊢ ea ≡ eb : et

variable {E}

theorem FEq.trans {a b c t : FExpr} :
    FEq E a b t →
    FEq E b c t →
    FEq E a c t := by
  intro h₁ h₂
  refine ⟨h₁.noProjLeft, h₂.noProjRight, h₁.noProjType, fun ℓ n Γ => ?_⟩
  have ⟨ea, eb, et, hda, hdb, hdt, d₁⟩ := h₁.defeq Γ
  have ⟨eb', ec, et', hdb', hdc, hdt', d₂⟩ := h₂.defeq Γ
  obtain rfl := hdb'.unique hdb h₁.noProjRight
  obtain rfl := hdt'.unique hdt h₁.noProjType
  exact ⟨ea, ec, _, hda, hdc, hdt', d₁.trans d₂⟩

theorem FEq.conv {a b t t' : FExpr} {l : FLevel} :
    FEq E a b t →
    FEq E t t' (.sort l) →
    FEq E a b t' := by
  intro h ht
  refine ⟨h.noProjLeft, h.noProjRight, ht.noProjRight, fun ℓ n Γ => ?_⟩
  have ⟨ea, eb, et, hda, hdb, hdt, d⟩ := h.defeq Γ
  have ⟨et₁, et', es, hdt₁, hdt', hds, dt⟩ := ht.defeq Γ
  obtain rfl := hdt₁.unique hdt h.noProjType
  have ⟨_, _, hes⟩ := hds.sort_inv
  subst hes
  exact ⟨ea, eb, et', hda, hdb, hdt', .defeqDF dt d⟩

theorem FEq.symm {a b t : FExpr} :
    FEq E a b t →
    FEq E b a t := by
  intro h
  refine ⟨h.noProjRight, h.noProjLeft, h.noProjType, fun ℓ n Γ => ?_⟩
  have ⟨ea, eb, et, hda, hdb, hdt, d⟩ := h.defeq Γ
  exact ⟨eb, ea, et, hdb, hda, hdt, d.symm⟩

end

section

variable (F : FEnv)

def CtxSpec (Δ : FCtx) : Prop :=
  ∀ ⦃ζ : Sigs⦄ ⦃E : Env ζ⦄,
  FEnv.Denotes F E →
  EnvWF E →
  ∃ (n : Nat) (Γ₀ : Ctx ζ 0 0 n), Sem F Δ E Γ₀

variable (hints : PArray Export.Hints)

def checkCtx (Δ : FCtx) : EIO Failure (PLift (CtxSpec F Δ)) :=
  if h : Δ.size = 0 then
    pure ⟨fun _ _ hF hE => ⟨0, .nil, by
      rw [Array.eq_empty_of_size_eq_zero h]
      exact Sem.nil hF hE⟩⟩
  else do
    let ⟨hpre⟩ ← checkCtx Δ.pop
    let ⟨hwf⟩ ← FExpr.wf F 0 Δ.pop.size 0 Δ.back!
    let ⟨hsort⟩ ← (inferSorted F 0 hints {} Δ.pop Δ.back!).eval
    pure ⟨fun _ E hF hE => by
      have ⟨n, Γ₀, hS⟩ := hpre hF hE
      obtain rfl := hS.size
      have ⟨t₀, ht₀⟩ := hwf (E := ⟨_, E⟩) hF
      have ⟨t, u, ht, hty⟩ := hsort hS ht₀
      have hS' := hS.snoc ht hty
      rw [← Array.eq_push_pop_back!_of_size_ne_zero h] at hS'
      exact ⟨_, _, hS'⟩⟩
termination_by Δ.size
decreasing_by simp; omega

structure Schema where
  ctx : FCtx
  ty : FExpr
  lhs : FExpr
  rhs : FExpr

declare_syntax_cat schemaBinder

syntax "(" ident " : " term ")" : schemaBinder
syntax "schema% " schemaBinder* " ⊢ " term:51 " ≡ " term:51 " : " term : term
syntax "schema% " schemaBinder* " ⊢ " term:51 " : " term : term

macro_rules
  | `(schema% $bs:schemaBinder* ⊢ $lhs ≡ $rhs : $ty) => do
    let mut names : Array (Lean.TSyntax `ident) := #[]
    let mut tys : Array Lean.Term := #[]
    for b in bs do
      match b with
      | `(schemaBinder| ($x:ident : $t)) =>
        names := names.push x
        tys := tys.push t
      | _ => Lean.Macro.throwUnsupported
    let mut ctx ← `((#[] : FCtx))
    for t in tys do
      ctx ← `(($ctx).push $t)
    let mut body ← `(({ ctx := $ctx, ty := $ty, lhs := $lhs, rhs := $rhs } : Schema))
    for i in (List.range names.size).reverse do
      body ← `(let $(names[i]!) : FExpr := .fvar $(Lean.quote i); $body)
    return body
  | `(schema% $bs:schemaBinder* ⊢ $e : $ty) => `(schema% $bs:schemaBinder* ⊢ $e ≡ $e : $ty)

structure Schema.Spec (s : Schema) : Prop where
  ctx : CtxSpec F s.ctx
  noProjCtx : ∀ t ∈ s.ctx, t.NoProj
  levelFreeCtx : ∀ t ∈ s.ctx, t.data.hasLevelParam = false
  noProjTy : s.ty.NoProj
  noProjLhs : s.lhs.NoProj
  noProjRhs : s.rhs.NoProj
  levelFreeTy : s.ty.data.hasLevelParam = false
  levelFreeLhs : s.lhs.data.hasLevelParam = false
  levelFreeRhs : s.rhs.data.hasLevelParam = false
  wfTy : WFSpec F 0 s.ctx.size 0 s.ty
  wfLhs : WFSpec F 0 s.ctx.size 0 s.lhs
  wfRhs : WFSpec F 0 s.ctx.size 0 s.rhs
  defeq : DefEqAtSpec F 0 s.ctx s.ty s.lhs s.rhs

def FExpr.checkLevelFree (fe : FExpr) : Except Failure (PLift (fe.data.hasLevelParam = false)) :=
  if h : fe.data.hasLevelParam = false then pure ⟨h⟩ else throw .internal

def FExpr.checkNoProj (fe : FExpr) : Except Failure (PLift fe.NoProj) :=
  match fe.noProj with
  | some h => pure h
  | none => throw .internal

def Schema.check (s : Schema) : EIO Failure (PLift (s.Spec F)) := do
  let ⟨hctx⟩ ← checkCtx F hints s.ctx
  let ⟨hnpCtx⟩ ← Array.forallM s.ctx (fun i hi => (s.ctx[i]'hi).NoProj)
    fun i hi => FExpr.checkNoProj (s.ctx[i]'hi)
  let ⟨hlfCtx⟩ ← Array.forallM s.ctx (fun i hi => (s.ctx[i]'hi).data.hasLevelParam = false)
    fun i hi => FExpr.checkLevelFree (s.ctx[i]'hi)
  let ⟨hnpTy⟩ ← FExpr.checkNoProj s.ty
  let ⟨hnpLhs⟩ ← FExpr.checkNoProj s.lhs
  let ⟨hnpRhs⟩ ← FExpr.checkNoProj s.rhs
  let ⟨hlfTy⟩ ← FExpr.checkLevelFree s.ty
  let ⟨hlfLhs⟩ ← FExpr.checkLevelFree s.lhs
  let ⟨hlfRhs⟩ ← FExpr.checkLevelFree s.rhs
  let ⟨hwfTy⟩ ← FExpr.wf F 0 s.ctx.size 0 s.ty
  let ⟨hwfLhs⟩ ← FExpr.wf F 0 s.ctx.size 0 s.lhs
  let ⟨hwfRhs⟩ ← FExpr.wf F 0 s.ctx.size 0 s.rhs
  let ⟨hdefeq⟩ ← (isDefEqAt F 0 hints {} s.ctx s.ty s.lhs s.rhs).eval
  pure ⟨{
    ctx := hctx
    noProjCtx := fun _ ht =>
      have ⟨i, hi, hti⟩ := Array.mem_iff_getElem.mp ht
      hti ▸ hnpCtx i hi
    levelFreeCtx := fun _ ht =>
      have ⟨i, hi, hti⟩ := Array.mem_iff_getElem.mp ht
      hti ▸ hlfCtx i hi
    noProjTy := hnpTy
    noProjLhs := hnpLhs
    noProjRhs := hnpRhs
    levelFreeTy := hlfTy
    levelFreeLhs := hlfLhs
    levelFreeRhs := hlfRhs
    wfTy := hwfTy
    wfLhs := hwfLhs
    wfRhs := hwfRhs
    defeq := hdefeq }⟩

end

variable {F}

theorem Schema.Spec.inst {s : Schema} (h : s.Spec F) {ζ : Sigs} {E : Env ζ}
    (hF : FEnv.Denotes F E) (hE : EnvWF E)
    {as bs : Array FExpr} (has : as.size = s.ctx.size) (hbs : bs.size = s.ctx.size)
    (hargs' : ∀ i, i < s.ctx.size → FEq E as[i]! bs[i]! (s.ctx[i]!.instFVars as)) :
    FEq E (s.lhs.instFVars as) (s.rhs.instFVars bs) (s.ty.instFVars as) := by
  have hargs : ∀ i (hi : i < s.ctx.size),
      FEq E (as[i]'(has ▸ hi)) (bs[i]'(hbs ▸ hi)) ((s.ctx[i]'hi).instFVars as) := fun i hi => by
    have := hargs' i hi
    rwa [getElem!_pos as i (by omega), getElem!_pos bs i (by omega),
      getElem!_pos s.ctx i hi] at this
  have hnpAs : ∀ a ∈ as, a.NoProj := fun a ha => by
    have ⟨i, hi, hai⟩ := Array.mem_iff_getElem.mp ha
    exact hai ▸ (hargs i (has ▸ hi)).noProjLeft
  have hnpBs : ∀ b ∈ bs, b.NoProj := fun b hb => by
    have ⟨i, hi, hbi⟩ := Array.mem_iff_getElem.mp hb
    exact hbi ▸ (hargs i (hbs ▸ hi)).noProjRight
  refine ⟨h.noProjLhs.instFVarsCore hnpAs, h.noProjRhs.instFVarsCore hnpBs,
    h.noProjTy.instFVarsCore hnpAs, fun ℓ n Γ => ?_⟩
  have ⟨k, Γ₀, hS⟩ := h.ctx hF hE
  obtain rfl := hS.size
  have ⟨t₀, ht₀⟩ := h.wfTy (E := ⟨ζ, E⟩) hF
  have ⟨e₁, he₁⟩ := h.wfLhs (E := ⟨ζ, E⟩) hF
  have ⟨e₂, he₂⟩ := h.wfRhs (E := ⟨ζ, E⟩) hF
  have d₀ := h.defeq hS ht₀ he₁ he₂
  let ls : Param 0 → Level ℓ := fun p => (p.elim0 : Level ℓ)
  have d₁ := d₀.instLevel ls
  have hΓ₀ := hS.ctxWF.instLevel ls
  have hch : ∀ v : Fin s.ctx.size, ∃ ea eb et : Expr ζ ℓ n,
      FExpr.Denotes ⟨ζ, E⟩ 0 (as[v.val]'(by omega)) ea ∧
      FExpr.Denotes ⟨ζ, E⟩ 0 (bs[v.val]'(by omega)) eb ∧
      FExpr.Denotes ⟨ζ, E⟩ 0 ((s.ctx[v.val]'v.isLt).instFVars as) et ∧
      E[Γ] ⊢ ea ≡ eb : et :=
    fun v => (hargs v.val v.isLt).defeq Γ
  choose σ₁ σ₂ τ hσ₁ hσ₂ hτ hd using hch
  have hA : ArgsDenote ⟨ζ, E⟩ as σ₁ := ⟨has, hσ₁⟩
  have hB : ArgsDenote ⟨ζ, E⟩ bs σ₂ := ⟨hbs, hσ₂⟩
  have hσ : E[Γ] ⊢ σ₁ ≡ σ₂ ⊣ Γ₀{ls} := fun v => by
    have hget := ((hS.ctx.get v.val v.isLt).levelFree ℓ
      (h.levelFreeCtx _ (Array.getElem_mem _))).instFVars hA
    rw [Ctx.get_instL] at hget
    rw [← hτ v |>.unique hget (hargs v.val v.isLt).noProjType]
    exact hd v
  have d₂ := Defeq.substitution_congr hΓ₀ hσ d₁
  exact ⟨_, _, _, (he₁.levelFree ℓ h.levelFreeLhs).instFVars hA,
    (he₂.levelFree ℓ h.levelFreeRhs).instFVars hB,
    (ht₀.levelFree ℓ h.levelFreeTy).instFVars hA, d₂⟩

theorem Schema.Spec.closed {ty lhs rhs : FExpr} (h : Schema.Spec F ⟨#[], ty, lhs, rhs⟩)
    {ζ : Sigs} {E : Env ζ} (hF : FEnv.Denotes F E) (hE : EnvWF E) :
    FEq E lhs rhs ty := by
  refine ⟨h.noProjLhs, h.noProjRhs, h.noProjTy, fun ℓ n Γ => ?_⟩
  have ⟨k, Γ₀, hS⟩ := h.ctx hF hE
  obtain rfl : 0 = k := hS.size
  cases Γ₀
  have ⟨t₀, ht₀⟩ := h.wfTy (E := ⟨ζ, E⟩) hF
  have ⟨e₁, he₁⟩ := h.wfLhs (E := ⟨ζ, E⟩) hF
  have ⟨e₂, he₂⟩ := h.wfRhs (E := ⟨ζ, E⟩) hF
  have d := (h.defeq hS ht₀ he₁ he₂).instLevel (fun p : Param 0 => (p.elim0 : Level ℓ))
  exact ⟨_, _, _, (he₁.levelFree ℓ h.levelFreeLhs).wkClosed n,
    (he₂.levelFree ℓ h.levelFreeRhs).wkClosed n, (ht₀.levelFree ℓ h.levelFreeTy).wkClosed n,
    d.wkClosed⟩

end Metalean.Checker.Fast
