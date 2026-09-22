/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.FastChecker.Reduce
import Metalean.Checker.Eta
public import Metalean.Metatheory.Unique
public import Metalean.Typing.Structure
import Metalean.Meta.IfRfl
import Metalean.Typing.Env

@[expose] public section

namespace Metalean.FastChecker

open Frontend (Failure)

section

variable (L : Literals) (F : FEnv) (ℓ : Nat) (hints : Array Export.Hints)
  (accel : Accel L F)

include hints accel

def caseFnTypeOf (ι : IndSig) (I : FInductive) (pos : Nat) (ls : Array FLevel)
    (ps ms : FCtx) (n : Nat) (hctorsLt : ∀ t : Fin ι.nsorts, t.val < I.ctors.size)
    (hctorLt : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)),
      c.val < (I.ctors[t.val]'(hctorsLt t)).size)
    (hrecs : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)),
      ((I.ctors[t.val]'(hctorsLt t))[c.val]'(hctorLt t c)).recursive.size =
        (ι.ctors t c).nrecFields)
    (hmsLt : ∀ t : Fin ι.nsorts, t.val < ms.size)
    (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) : FExpr :=
  ((I.ctors[t.val]'(hctorsLt t))[c.val]'(hctorLt t c)).caseFnType pos t.val c.val ls ps n
    (fun r => ((ι.ctors t c).recursiveTarget (r.cast (hrecs t c))).val)
    (fun r => ms[((ι.ctors t c).recursiveTarget (r.cast (hrecs t c))).val]'
      (hmsLt ((ι.ctors t c).recursiveTarget (r.cast (hrecs t c)))))
    (ms[t.val]'(hmsLt t))

structure KTarget (ι : IndSig) (I : FInductive) (s : Nat) : Prop where
  level : I.level = .zero
  sort : s < ι.nsorts
  single : ι.nsorts = 1
  ctor : ι.nctors ⟨s, sort⟩ = 1
  fields : (ι.ctors ⟨s, sort⟩ ⟨0, by omega⟩).nfields = 0
  recFields : (ι.ctors ⟨s, sort⟩ ⟨0, by omega⟩).nrecFields = 0
  row : s < I.ctors.size
  col : 0 < (I.ctors[s]'row).size

def KTarget.check (ι : IndSig) (I : FInductive) (s : Nat) : Option (PLift (KTarget ι I s)) := do
  let ⟨hl⟩ ← guardProof (I.level = .zero)
  let ⟨hs⟩ ← guardProof (s < ι.nsorts)
  let ⟨h₁⟩ ← guardProof (ι.nsorts = 1)
  let ⟨hc⟩ ← guardProof (ι.nctors ⟨s, hs⟩ = 1)
  have h₀ : 0 < ι.nctors ⟨s, hs⟩ := by omega
  let ⟨hf⟩ ← guardProof ((ι.ctors ⟨s, hs⟩ ⟨0, h₀⟩).nfields = 0)
  let ⟨hr⟩ ← guardProof ((ι.ctors ⟨s, hs⟩ ⟨0, h₀⟩).nrecFields = 0)
  let ⟨hrow⟩ ← guardProof (s < I.ctors.size)
  let ⟨hcol⟩ ← guardProof (0 < (I.ctors[s]'hrow).size)
  pure ⟨hl, hs, h₁, hc, hf, hr, hrow, hcol⟩

def ancestorsOf (G : FCtx) : CheckM L F ℓ (FCtx.Ancestors G) := do
  if let some ⟨G₁, a⟩ := (← get).ancestors.get? G.addr then
    if h : G₁ = G then return a.cast h
  let a := FCtx.Ancestors.root G
  modify fun c => { c with ancestors := c.ancestors.insert G.addr ⟨G, a⟩ }
  return a

def prefixFor (G : FCtx) (fe : FExpr) : CheckM L F ℓ FCtx := do
  if fe.data.looseBVarRange.toNat = 0 ∧ fe.fvarRange < G.size then
    if let some ⟨_, a⟩ := (← get).ancestors.get? G.addr then
      if h : fe.fvarRange < a.arr.size then return a.arr[fe.fvarRange]
  return G

def pushCtx (G : FCtx) (t : FExpr) : CheckM L F ℓ {G' : FCtx // G' = G.push t} := do
  let ⟨t', ht⟩ ← (do
    if let some t' := (← get).intern.get? t then
      if h : t' = t then return ⟨t', h⟩
    modify fun c => { c with intern := c.intern.insert t t }
    return ⟨t, rfl⟩ : CheckM L F ℓ {t' : FExpr // t' = t})
  let key := (G.addr, t'.addr)
  if let some ⟨k, G', h⟩ := (← get).push.get? key then
    if hk : k = (G, t') then
      return ⟨G', by
        subst hk ht
        exact h⟩
  let a ← ancestorsOf L F ℓ G
  let G' : {G' : FCtx // G' = G.push t'} := ⟨G.push t', rfl⟩
  modify fun c =>
    { c with
      push := c.push.insert key ⟨(G, t'), G'⟩
      ancestors := c.ancestors.insert G'.1.addr ⟨G'.1, a.push t' G'.1 G'.2⟩ }
  return ⟨G'.1, by rw [G'.2, ht]⟩

mutual
partial def prefixInfer (G : FCtx) (fe : FExpr) :
    CheckM L F ℓ (Option ((G₀ : FCtx) × (ft : FExpr) ×'
      FCtx.Extends G₀ G ∧ fe.fvarRange ≤ G₀.size ∧ fe.data.looseBVarRange.toNat = 0 ∧
        InferSpec L F ℓ G₀ fe ft)) := do
  if hc : fe.data.looseBVarRange.toNat = 0 then
    if fe.fvarRange < G.size then
      if let some ⟨G₁, a⟩ := (← get).ancestors.get? G.addr then
        if hG : G₁ = G then
          if hi : fe.fvarRange < a.arr.size then
            if (a.arr[fe.fvarRange]'hi).size < G.size then
              match ← tryCatch (some <$> infer (a.arr[fe.fvarRange]'hi) fe) fun _ => pure none with
              | some ⟨ft, h⟩ =>
                return some ⟨a.arr[fe.fvarRange]'hi, ft, hG ▸ (a.spec _ hi).2, (a.spec _ hi).1, hc, h⟩
              | none => pure ()
  return none

partial def prefixDefEq (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (Option ((G₀ : FCtx) × (ft₁ : FExpr) × (ft₂ : FExpr) ×'
      FCtx.Extends G₀ G ∧ fe₁.fvarRange ≤ G₀.size ∧ fe₂.fvarRange ≤ G₀.size ∧
        fe₁.data.looseBVarRange.toNat = 0 ∧ fe₂.data.looseBVarRange.toNat = 0 ∧
        InferSpec L F ℓ G₀ fe₁ ft₁ ∧ InferSpec L F ℓ G₀ fe₂ ft₂)) := do
  let k := max fe₁.fvarRange fe₂.fvarRange
  if hc₁ : fe₁.data.looseBVarRange.toNat = 0 then
    if hc₂ : fe₂.data.looseBVarRange.toNat = 0 then
      if k < G.size then
        if let some ⟨G₁, a⟩ := (← get).ancestors.get? G.addr then
          if hG : G₁ = G then
            if hi : k < a.arr.size then
              if (a.arr[k]'hi).size < G.size then
                if let some ⟨ft₁, h₁⟩ ←
                    tryCatch (some <$> infer (a.arr[k]'hi) fe₁) fun _ => pure none then
                  if let some ⟨ft₂, h₂⟩ ←
                      tryCatch (some <$> infer (a.arr[k]'hi) fe₂) fun _ => pure none then
                    have hk := (a.spec k hi).1
                    return some ⟨a.arr[k]'hi, ft₁, ft₂, hG ▸ (a.spec k hi).2,
                      by omega, by omega, hc₁, hc₂, h₁, h₂⟩
  return none

partial def whnf (G : FCtx) (fe₁ : FExpr) :
    CheckM L F ℓ {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂} := do
  if fe₁ matches .bvar _ | .fvar _ | .sort _ | .forallE .. | .natLit _ | .strLit _ then
    return ⟨fe₁, RedSpec.refl fe₁⟩
  if let some ⟨G₀, _, hx, hr, hc, hinf⟩ ← prefixInfer G fe₁ then
    let ⟨fe₂, h⟩ ← whnf G₀ fe₁
    return ⟨fe₂, h.extend hr hc hinf hx⟩
  match (← get).whnf.get? (G, fe₁) with
  | some r => return r
  | none => pure ()
  let ⟨fe₂, h⟩ ← whnfLoop G fe₁
  modify fun c =>
    { c with whnf := c.whnf.insert (G, fe₁) ⟨fe₂, h⟩ }
  pure ⟨fe₂, h⟩

partial def whnfLoop (G : FCtx) (fe₁ : FExpr) :
    CheckM L F ℓ {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂} := do
  let ⟨fe₂, h₁⟩ ← whnfCore G false fe₁
  if let some ⟨fe₃, h₂⟩ ← reduceNat G fe₂ then
    return ⟨fe₃, RedSpec.trans h₁ h₂⟩
  match ← unfoldHeadM G fe₂ with
  | some ⟨fe₃, h₂⟩ =>
    let ⟨fe₄, h₃⟩ ← whnfLoop G fe₃
    pure ⟨fe₄, RedSpec.trans h₁ (RedSpec.trans (RedSpec.ofRed h₂) h₃)⟩
  | none => pure ⟨fe₂, h₁⟩

partial def reduceNat (G : FCtx) :
    (fe₁ : FExpr) → CheckM L F ℓ (Option {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂})
  | .app (.app (.const pos ls) x) a => do
    unless accelOp L F accel pos do return none
    let ⟨x₂, hx₂⟩ ← whnf G x
    let some ⟨num₁, hx₃⟩ := natLitExt L F ℓ G x₂ | return none
    let ⟨y₂, hy₂⟩ ← whnf G a
    let some ⟨num₂, hy₃⟩ := natLitExt L F ℓ G y₂ | return none
    let hargs : RedSpec L F ℓ G (.app (.app (.const pos ls) x) a)
        (.app (.app (.const pos ls) (.natLit num₁)) (.natLit num₂)) :=
      RedSpec.trans (RedSpec.frame (.app a) (RedSpec.arg (RedSpec.trans hx₂ hx₃)))
        (RedSpec.arg (RedSpec.trans hy₂ hy₃))
    let some ⟨fe₂, hfold⟩ ← liftM (foldOp L F ℓ accel G pos ls (.natLit num₁) (.natLit num₂)).run
      | return none
    return some ⟨fe₂, RedSpec.trans hargs hfold⟩
  | .ctor pos s c ls ps fds recFds => do
    unless pos = L.nat do return none
    let some z := (recFds[0]? : Option FExpr) | return none
    match hfe : F[L.nat]?,
        hsucc : FExpr.ctor pos s c ls ps fds recFds == .ctor L.nat 0 1 #[] #[] #[] #[z] with
    | some (.inductive ι _), true =>
      if hι : ι = Literals.Nat.sig then
        let ⟨z₂, hz₂⟩ ← whnf G z
        let some ⟨num, hz₃⟩ := natLitExt L F ℓ G z₂ | return none
        bounded (num + 1)
        return some ⟨.natLit (num + 1), by
          subst hι
          rw [eq_of_beq hsucc]
          exact RedSpec.trans ((RedSpec.trans hz₂ hz₃).succArg hfe) (RedSpec.succLit hfe num)⟩
      else return none
    | _, _ => return none
  | _ => return none

partial def whnfCore (G : FCtx) (cheapProj : Bool) (fe₁ : FExpr) :
    CheckM L F ℓ {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂} := do
  if fe₁ matches .app .. | .recr .. | .letE .. | .quotLift .. | .quotInd .. | .proj .. then
    if !cheapProj then
      if let some ⟨G₀, _, hx, hr, hc, hinf⟩ ← prefixInfer G fe₁ then
        let ⟨fe₂, h⟩ ← whnfCore G₀ cheapProj fe₁
        return ⟨fe₂, h.extend hr hc hinf hx⟩
      match (← get).whnfCore.get? (G, fe₁) with
      | some r => return r
      | none => pure ()
    let r ← whnfCoreNode G cheapProj fe₁
    if !cheapProj then
      modify fun c =>
        { c with whnfCore := c.whnfCore.insert (G, fe₁) r }
    return r
  return ⟨fe₁, RedSpec.refl fe₁⟩

partial def whnfCoreNode (G : FCtx) (cheapProj : Bool) :
    (fe₁ : FExpr) → CheckM L F ℓ {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂}
  | .app f₁ a => whnfApp G cheapProj (.app f₁ a)
  | .recr pos s ls l ps ms mins is maj₁ => do
    let ⟨maj₂, h₁⟩ ← toCtorWhenK G pos s maj₁
    let ⟨maj₃, h₂⟩ ← whnf G maj₂
    let ⟨maj₄, h₃⟩ ← majorToCtor G pos s ls maj₃
    let hmaj := RedSpec.trans h₁ (RedSpec.trans h₂ h₃)
    match iotaStep L F G.size pos s ls l ps ms mins is maj₄ with
    | some ⟨fe₂, hiota⟩ =>
      let ⟨fe₃, h₄⟩ ← whnfCore G cheapProj fe₂
      pure ⟨fe₃, RedSpec.trans (RedSpec.frame (.recr pos s ls l ps ms mins is) hmaj)
        (RedSpec.trans (RedSpec.ofRed (.single hiota)) h₄)⟩
    | none => pure ⟨.recr pos s ls l ps ms mins is maj₁, RedSpec.refl _⟩
  | .letE ft v b => do
    let ⟨fe₂, h⟩ ← whnfCore G cheapProj (FExpr.instAt v 0 b)
    pure ⟨fe₂, RedSpec.trans (RedSpec.ofRed (.single (.zeta ft v b))) h⟩
  | .quotLift pos l₁ l₂ α r β f g a₁ => do
    match ← whnf G a₁ with
    | ⟨.quotMk pos₂ _ _ _ a, h₁⟩ =>
      if hpos : pos₂ = pos then
        let ⟨fe₂, h₂⟩ ← whnfCore G cheapProj (.app f a)
        pure ⟨fe₂, RedSpec.trans (RedSpec.frame (.quotLift pos l₁ l₂ α r β f g) h₁)
          (RedSpec.trans (RedSpec.ofRed (.single (.quotIota hpos))) h₂)⟩
      else pure ⟨.quotLift pos l₁ l₂ α r β f g a₁, RedSpec.refl _⟩
    | _ => pure ⟨.quotLift pos l₁ l₂ α r β f g a₁, RedSpec.refl _⟩
  | .quotInd pos l α r β f a₁ => do
    match ← whnf G a₁ with
    | ⟨.quotMk pos₂ _ _ _ a, h₁⟩ =>
      if hpos : pos₂ = pos then
        let ⟨fe₂, h₂⟩ ← whnfCore G cheapProj (.app f a)
        pure ⟨fe₂, RedSpec.trans (RedSpec.frame (.quotInd pos l α r β f) h₁)
          (RedSpec.trans (RedSpec.ofRed (.single (.quotIndIota hpos))) h₂)⟩
      else pure ⟨.quotInd pos l α r β f a₁, RedSpec.refl _⟩
    | _ => pure ⟨.quotInd pos l α r β f a₁, RedSpec.refl _⟩
  | .proj pos s idx e₁ => do
    let ⟨e₂, h₁⟩ ← if cheapProj then whnfCore G cheapProj e₁ else whnf G e₁
    let struct : {e₃ : FExpr // RedSpec L F ℓ G e₁ e₃} ← match e₂, h₁ with
      | .strLit str, h₁ => do
        let ⟨e₃, h₂⟩ ← whnf G (FExpr.strLitExpand L str)
        pure ⟨e₃, RedSpec.trans h₁ (RedSpec.trans (RedSpec.strLit str) h₂)⟩
      | e₂, h₁ => pure ⟨e₂, h₁⟩
    match struct with
    | ⟨.ctor pos₂ s₂ _ _ _ fds _, h₁⟩ =>
      if hsel : pos₂ = pos ∧ s₂ = s ∧ idx < fds.size then
        let ⟨fe₃, h₃⟩ ← whnfCore G cheapProj (fds[idx]'hsel.2.2)
        pure ⟨fe₃, RedSpec.trans (RedSpec.frame (.proj pos s idx) h₁)
          (RedSpec.trans (RedSpec.projCtor hsel.1 hsel.2.1 hsel.2.2) h₃)⟩
      else pure ⟨.proj pos s idx e₁, RedSpec.refl _⟩
    | _ => pure ⟨.proj pos s idx e₁, RedSpec.refl _⟩
  | fe₁ => pure ⟨fe₁, RedSpec.refl _⟩

partial def whnfApp (G : FCtx) (cheapProj : Bool) (fe : FExpr) :
    CheckM L F ℓ {fe₂ : FExpr // RedSpec L F ℓ G fe fe₂} := do
  let ⟨(f₀, as), hfe⟩ := fe.spine
  let ⟨f, h₁⟩ ← whnfCore G cheapProj f₀
  match FExpr.peelLams as.length f with
  | ⟨0, _⟩ =>
    if f = f₀ then pure ⟨fe, RedSpec.refl fe⟩
    else
      let ⟨r, h₂⟩ ← whnfCore G cheapProj (FExpr.appList f as)
      pure ⟨r, hfe ▸ (h₁.appList as).trans h₂⟩
  | ⟨m + 1, b, hb, hm⟩ =>
    let ⟨r, h₂⟩ ← whnfCore G cheapProj
      (FExpr.appList (FExpr.instMany (as.take (m + 1)) b) (as.drop (m + 1)))
    pure ⟨r, hfe ▸ (h₁.appList as).trans ((RedSpec.betaMany as hm hb).trans h₂)⟩

partial def unfoldHeadM (G : FCtx) :
    (fe₁ : FExpr) → CheckM L F ℓ (Option {fe₂ : FExpr // FWHRedS L F G.size fe₁ fe₂})
  | .const pos ls => do
    match hfe : F[pos]? with
    | some (.def nlevels t v) =>
      if hsize : ls.size = nlevels then
        if ls.isEmpty then return some ⟨v.instL ls, .single (.delta hfe hsize)⟩
        if let some ⟨r, hr⟩ := (← get).unfold.get? (pos, ls) then
          return some ⟨r, by rw [hr nlevels t v hfe]; exact .single (.delta hfe hsize)⟩
        let r := v.instL ls
        let entry : {v' : FExpr // UnfoldsTo F pos ls v'} :=
          ⟨r, fun _ _ _ h => by rw [hfe] at h; cases h; rfl⟩
        modify fun c => { c with unfold := c.unfold.insert (pos, ls) entry }
        return some ⟨r, .single (.delta hfe hsize)⟩
      else return none
    | _ => return none
  | .app f a => do
    match ← unfoldHeadM G f with
    | some ⟨f₂, h⟩ => return some ⟨.app f₂ a, h.frame (.app a)⟩
    | none => return none
  | _ => return none

partial def unfoldDefinition (G : FCtx) (fe₁ : FExpr) :
    CheckM L F ℓ (Option {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂}) := do
  (← unfoldHeadM G fe₁).mapM fun ⟨fe₂, h₁⟩ => do
    let ⟨fe₃, h₂⟩ ← whnfCore G true fe₂
    pure ⟨fe₃, RedSpec.trans (RedSpec.ofRed h₁) h₂⟩

partial def infer (G : FCtx) (fe : FExpr) :
    CheckM L F ℓ {ft : FExpr // InferSpec L F ℓ G fe ft} := do
  if hc : fe.data.looseBVarRange.toNat = 0 then
    if fe.fvarRange < G.size then
      if let some ⟨G₁, a⟩ := (← get).ancestors.get? G.addr then
        if hG : G₁ = G then
          if hi : fe.fvarRange < a.arr.size then
            if (a.arr[fe.fvarRange]'hi).size < G.size then
              let ⟨ft, h⟩ ← infer (a.arr[fe.fvarRange]'hi) fe
              return ⟨ft, h.extend (a.spec _ hi).1 hc (hG ▸ (a.spec _ hi).2)⟩
  match (← get).infer.get? (G, fe) with
  | some r => return r
  | none => pure ()
  let r ← inferCore G fe
  modify fun c =>
    { c with infer := c.infer.insert (G, fe) r }
  pure r

partial def inferCore (G : FCtx) :
    (fe : FExpr) → CheckM L F ℓ {t : FExpr // InferSpec L F ℓ G fe t}
  | .bvar _ => throw .internal
  | .fvar i =>
    if hi : i < G.size then pure ⟨G[i], InferSpec.fvar hi⟩
    else throw .internal
  | .sort l => pure ⟨.sort (.succ l), InferSpec.sort l⟩
  | .const pos ls =>
    match hfe : F[pos]? with
    | some fe =>
      match hct : fe.constType? with
      | some (nlevels, t) =>
        pure ⟨t.instL ls, fun {_ _ _ _ _} hS (.const hls hη hls') => by
          have ⟨_, η₀, hη₀, ht⟩ := FEnv.Denotes.constType (E := ⟨_, _⟩) hfe hct hS.env
          cases hη.symm.trans hη₀
          exact ⟨_, _, .const hls hη hls', ((ht.instL hls hls').wkClosed _),
            .constDF ((hS.ordered.entryWF η₀).constType _).choose_spec⟩⟩
      | none => throw (.reject .shape)
    | none => throw .internal
  | .proj pos s idx e => do
    let ⟨te, hte⟩ ← infer G e
    let ⟨t, ht⟩ ← whnf G te
    match hq : t with
    | .ind pos₂ s₂ ls₂ ps₂ is₂ =>
      match hfe : F[pos]? with
      | some (.inductive ι I) => do
        let ⟨hsame⟩ ← guardProofOr (pos₂ = pos ∧ s₂ = s) (.reject .shape)
        let ⟨hstruct⟩ ← guardProofOr (I.isStructure s 0 = true) (.reject .shape)
        let ⟨hsc⟩ ← guardProofOr (s < I.ctors.size) (.reject .shape)
        let ⟨hcc⟩ ← guardProofOr (0 < (I.ctors[s]'hsc).size) (.reject .shape)
        let ⟨hidx⟩ ← guardProofOr (idx < ((I.ctors[s]'hsc)[0]'hcc).ordinary.size) (.reject .shape)
        pure ⟨((I.ctors[s]'hsc)[0]'hcc).projType pos s ls₂ ps₂ idx hidx e,
          fun {ζ E n Γ _} hS hden => by
          have .proj (η := η) (s' := s') (c' := c') (f' := f') hstructD hη hs' hidx' hed := hden
          obtain ⟨rfl, rfl⟩ := hsame
          subst hs' hidx'
          have ⟨_, _, hed', hted, hety⟩ := hte hS hed
          have ⟨_, hu⟩ := hety.regular
          have hred : RedSpec L F ℓ G te (.ind pos₂ s'.val ls₂ ps₂ is₂) := hq ▸ ht
          have ⟨_, .ind (ls' := ls₂') (ps' := ps₂') (is' := isD) hls₂ hps₂ his₂ hη₂ hs₂ hls₂''
            hps₂'' his₂', hc⟩ := hred hS hted hu
          cases hη₂.symm.trans hη
          obtain rfl := (Fin.ext hs₂).symm
          have hmaj₂ := (TypeEq.ofDefEq hc).conv hety
          have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
          cases hη.symm.trans hη₀
          have ⟨_, hindTy⟩ := hmaj₂.regular
          have ⟨_, _, hpsw, _, _⟩ := hindTy.ind_inv
          have hB := (hS.ordered.entryWF η₀).block
          have hind : E[Γ] ⊢ .ind η₀ s' (⟦ls₂' ·⟧) ps₂' isD ≡
              .ind η₀ s' (⟦ls₂' ·⟧) ps₂' hstructD.indices typ :=
            .ofDefEq (Defeq.indDF (fun p => Inductive.paramType_conv hB p hpsw)
              fun i => hstructD.no_indices.elim i)
          have hmaj := hind.conv hmaj₂
          have hty := hstructD.projTerm_hasType hB f' hS.wf
            (fun p => Inductive.paramType_conv hB p hpsw) hmaj
          have hn1 := Fin.eq_one_of_unique c' hstructD.ctor_unique
          have hc0 : c'.val = 0 := by
            omega
          obtain rfl : c' = ⟨0, hn1 ▸ Nat.zero_lt_one⟩ := Fin.ext hc0
          have hd := (hI.ctors _ ⟨0, hn1 ▸ Nat.zero_lt_one⟩).projType hls₂ hls₂'' ⟨hps₂, hps₂''⟩
            hη hstructD hed' f'
          exact ⟨_, _, .proj (ls' := ls₂') (ps' := ps₂') hstructD hη rfl rfl hed', hd, hty⟩⟩
      | _ => throw (.reject .shape)
    | _ => throw (.reject .shape)
  | .app f a => do
    let ⟨tf, hf⟩ ← infer G f
    let ⟨ft₁, b, hpi⟩ ← ensureForall G tf
    let ⟨ha⟩ ← checkAgainst G a ft₁
    pure ⟨FExpr.instAt a 0 b, hf.app hpi ha⟩
  | .lam t b => do
    let ⟨(ds, ty), h⟩ ← inferLamTele G 0 (Nat.zero_le _) (.lam t b)
    pure ⟨FExpr.mkPi G.size ty ds, fun {_ _ _ _ _} hS hden => h hS hden⟩
  | .forallE t b => do
    let ⟨l, h⟩ ← inferPiTele G 0 (Nat.zero_le _) (.forallE t b)
    pure ⟨.sort l, fun {_ _ _ _ _} hS hden => h hS hden⟩
  | .letE _ _ _ => throw .internal
  | .ind pos s ls ps is =>
    match hfe : F[pos]? with
    | some (.inductive ι I) => do
      let ⟨hps⟩ ← guardProofOr (ps.size = I.params.size) (.reject .arity)
      let ⟨hs⟩ ← guardProofOr (s < I.indices.size) (.reject .shape)
      let ⟨his⟩ ← guardProofOr (is.size = (I.indices[s]'hs).size) (.reject .arity)
      let hpsT ← Fin.sequenceM fun p : Fin ps.size =>
        checkTyped G (ps[p.val]'p.isLt) (I.paramType ls ps p.val (by omega))
      let hisT ← Fin.sequenceM fun i : Fin is.size =>
        checkTyped G (is[i.val]'i.isLt) (I.indexType ls ps s hs is i.val (by omega))
      pure ⟨.sort (I.level.inst ls),
        fun {_ E _ Γ _} hS (.ind (s' := s') (ls' := ls') hls hps' his' hη hs' hls' hps'' his'') => by
          have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
          cases hη.symm.trans hη₀
          subst hs'
          have hB := (hS.ordered.entryWF η₀).block
          have ⟨_, hl, hleq⟩ := hI.levelInst hls hls'
          have ⟨eps, hepsD, hepsT⟩ := TypedSpec.fixArgs hS hps'
            (fts := fun p => I.paramType ls ps p.val (by omega))
            (fun e p => (E.get η₀).block.paramType (⟦ls' ·⟧) e p) hps''
            (fun e he p => hI.paramType hls hls' ⟨hps', he⟩ p)
            (fun e p h => Inductive.paramType_isType hB p h)
            (fun p => hpsT.down ⟨p.val, by omega⟩)
          have ⟨eis, heisD, heisT⟩ := TypedSpec.fixArgs hS his'
            (fts := fun i => I.indexType ls ps _ hs is i.val (by omega))
            (fun e i => (E.get η₀).block.indexType (⟦ls' ·⟧) s' eps e i) his''
            (fun e he i => hI.indexType hls hls' ⟨hps', hepsD⟩ _ ⟨his', he⟩ i)
            (fun e i h => Inductive.indexType_isType (hB.indices _) i hS.wf hepsT h)
            (fun i => hisT.down ⟨i.val, by omega⟩)
          refine ⟨_, _, .ind hls hps' his' hη rfl hls' hepsD heisD, .sort hl, ?_⟩
          rw [hleq]
          exact .indDF hepsT heisT⟩
    | _ => throw (.reject .shape)
  | .ctor pos s c ls ps fds recFds =>
    match hfe : F[pos]? with
    | some (.inductive ι I) => do
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .shape)
      let ⟨hc⟩ ← guardProofOr (c < ι.nctors ⟨s, hs⟩) (.reject .shape)
      let ⟨hsc⟩ ← guardProofOr (s < I.ctors.size) (.reject .shape)
      let ⟨hcc⟩ ← guardProofOr (c < (I.ctors[s]'hsc).size) (.reject .shape)
      let ctor := (I.ctors[s]'hsc)[c]'hcc
      let ⟨hrec⟩ ← guardProofOr (ctor.recursive.size = (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nrecFields)
        (.reject .shape)
      let ⟨hps⟩ ← guardProofOr (ps.size = I.params.size) (.reject .arity)
      let ⟨hfds⟩ ← guardProofOr (fds.size = ctor.ordinary.size) (.reject .arity)
      let ⟨hrecFds⟩ ← guardProofOr (recFds.size = ctor.recursive.size) (.reject .arity)
      let ⟨hordSize⟩ ← guardProofOr (ctor.ordinary.size = (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nfields)
        (.reject .shape)
      have hordLt : ∀ f : Fin (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nfields, f.val < ctor.ordinary.size :=
        fun f => by omega
      have hrecLt : ∀ r : Fin (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nrecFields, r.val < ctor.recursive.size :=
        fun r => by omega
      have hfdsLt : ∀ f : Fin (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nfields, f.val < fds.size :=
        fun f => by omega
      have hrecFdsLt : ∀ r : Fin (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nrecFields, r.val < recFds.size :=
        fun r => by omega
      let hpsT ← Fin.sequenceM fun p : Fin ps.size =>
        checkTyped G (ps[p.val]'p.isLt) (I.paramType ls ps p.val (by omega))
      let ⟨hfdsT⟩ ← Fin.sequenceM fun f : Fin (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nfields =>
        checkTyped G (fds[f.val]'(hfdsLt f)) (ctor.ordinaryFieldExpr ls ps fds f.val (hordLt f))
      let ⟨hrecFdsT⟩ ← Fin.sequenceM fun r : Fin (ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).nrecFields =>
        checkTyped G (recFds[r.val]'(hrecFdsLt r))
          (ctor.recursiveFieldExpr pos ls ps fds G.size
            ((ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).recursiveTarget r).val r.val (hrecLt r))
      pure ⟨.ind pos s ls ps (ctor.instTargetIndices ls ps fds), by
        intro ζ E _ Γ _ hS hden
        have hn := hS.size
        subst hn
        have .ctor (ls' := ls') hls hps' hfds' hrecFds' hη hs' hc' hls' hps'' hfds'' hrecFds'' :=
          hden
        have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
        cases hη.symm.trans hη₀
        obtain rfl : _ = (⟨s, hs⟩ : Fin ι.nsorts) := Fin.ext hs'
        obtain rfl : _ = (⟨c, hc⟩ : Fin (ι.nctors ⟨s, hs⟩)) := Fin.ext hc'
        have hcd := hI.ctors ⟨s, hs⟩ ⟨c, hc⟩
        have hB := (hS.ordered.entryWF η₀).block
        have hctor := hB.ctors ⟨s, hs⟩ ⟨c, hc⟩
        have ⟨eps, hepsD, hepsT⟩ := TypedSpec.fixArgs hS hps'
          (fts := fun p => I.paramType ls ps p.val (by omega))
          (fun e p => (E.get η₀).block.paramType (⟦ls' ·⟧) e p) hps''
          (fun e he p => hI.paramType hls hls' ⟨hps', he⟩ p)
          (fun e p h => Inductive.paramType_isType hB p h)
          (fun p => hpsT.down ⟨p.val, by omega⟩)
        have hpsA : ArgsDenote L ⟨_, _⟩ ps _ := ⟨hps', hepsD⟩
        have ⟨efds, hefdsD, hefdsT⟩ := TypedSpec.fixArgs hS hfds'
          (fts := fun f => ctor.ordinaryFieldExpr ls ps fds f.val (hordLt f))
          (fun e f => ((E.get η₀).block.ctors ⟨s, hs⟩ ⟨c, hc⟩).ordinaryFieldExpr (⟦ls' ·⟧) eps e f)
          hfds''
          (fun e he f => hcd.ordinaryFieldExpr hls hls' hpsA ⟨hfds', he⟩ f)
          (fun e f h => ⟨_, hctor.ordinaryFieldExpr_congr hB.params f hepsT h⟩)
          (fun f => hfdsT f)
        have hfdsA : ArgsDenote L ⟨_, _⟩ fds _ := ⟨hfds', hefdsD⟩
        have ⟨erec, herecD, herecT⟩ := TypedSpec.fixArgs hS hrecFds'
          (fts := fun r => ctor.recursiveFieldExpr pos ls ps fds G.size
            ((ι.ctors ⟨s, hs⟩ ⟨c, hc⟩).recursiveTarget r).val r.val (hrecLt r))
          (fun _ r => ((E.get η₀).block.ctors ⟨s, hs⟩ ⟨c, hc⟩).recursiveFieldExpr η₀
            (⟦ls' ·⟧) eps efds r)
          hrecFds''
          (fun _ _ r => hcd.recursiveFieldExpr hls hls' hpsA hfdsA hη r)
          (fun _ r _ => ⟨_, (hctor.recursiveFieldExpr_congr hB.params rfl r hepsT
            hefdsT).choose_spec⟩)
          (fun r => hrecFdsT r)
        have hindD : FExpr.Denotes L ⟨_, _⟩ 0 (.ind pos s ls ps (ctor.instTargetIndices ls ps fds)) _ :=
          .ind hls hps' hcd.instTargetIndices_size hη rfl hls' hepsD
            (hcd.instTargetIndices hls hls' hpsA hfdsA)
        have hind' := Defeq.indDF hepsT fun i =>
          hctor.targetIndex_congr hB.params i hepsT hefdsT
        exact ⟨_, _, .ctor hls hps' hfds' hrecFds' hη rfl rfl hls' hepsD hefdsD herecD, hindD,
          .ctorDF (fieldLevels := fun f => (hefdsT f).regular.choose)
            (recFieldLevels := fun r => (herecT r).regular.choose) hepsT hefdsT herecT
            (fun f => (hefdsT f).regular.choose_spec) (fun r => (herecT r).regular.choose_spec)
            hind'⟩⟩
    | _ => throw (.reject .shape)
  | .recr pos s ls l ps ms mins is maj =>
    match hfe : F[pos]? with
    | some (.inductive ι I) => do
      let ⟨hrec⟩ ← guardProofOr (I.recAllowed l = true) (.reject .recursorLevel)
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .shape)
      let ⟨hIi⟩ ← guardProofOr (I.indices.size = ι.nsorts) (.reject .shape)
      let ⟨hIc⟩ ← guardProofOr (I.ctors.size = ι.nsorts) (.reject .shape)
      let ⟨hps⟩ ← guardProofOr (ps.size = I.params.size) (.reject .arity)
      let ⟨hms⟩ ← guardProofOr (ms.size = ι.nsorts) (.reject .arity)
      let ⟨hmins⟩ ← guardProofOr (mins.size = Fin.sum ι.nctors) (.reject .arity)
      have hsIdx : s < I.indices.size := by omega
      let ⟨his⟩ ← guardProofOr (is.size = (I.indices[s]'hsIdx).size) (Failure.reject .arity)
      let hpsT ← Fin.sequenceM fun p : Fin ps.size =>
        checkTyped G (ps[p.val]'p.isLt) (I.paramType ls ps p.val (by omega))
      let hmsT ← Fin.sequenceM fun t : Fin ι.nsorts =>
        checkTyped G (ms[t.val]'(by omega)) (I.motiveType pos ls ps G.size t.val (by omega) l)
      have hctorsLt : ∀ t : Fin ι.nsorts, t.val < I.ctors.size := fun t => by omega
      let ⟨hrowsP⟩ ← Fin.sequenceM fun t : Fin ι.nsorts =>
        guardProofOr ((I.ctors[t.val]'(hctorsLt t)).size = ι.nctors t) (Failure.reject .shape)
      have hrows : ∀ t : Fin ι.nsorts, (I.ctors[t.val]'(hctorsLt t)).size = ι.nctors t :=
        fun t => hrowsP t
      have hctorLt : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)),
          c.val < (I.ctors[t.val]'(hctorsLt t)).size := fun t c => by have := (hrows t); omega
      let hrecsP ← Fin.sequenceM fun t : Fin ι.nsorts => Fin.sequenceM fun c : Fin (ι.nctors t) =>
        guardProofOr (((I.ctors[t.val]'(hctorsLt t))[c.val]'(hctorLt t c)).recursive.size =
          (ι.ctors t c).nrecFields) (Failure.reject .shape)
      have hrecs : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)),
          ((I.ctors[t.val]'(hctorsLt t))[c.val]'(hctorLt t c)).recursive.size =
            (ι.ctors t c).nrecFields := fun t c => hrecsP.down t c
      have hminLt : ∀ (t : Fin ι.nsorts) (c : Fin (ι.nctors t)),
          (minorIndex ι t c).val < mins.size := fun t c => by
        omega
      have hmsLt : ∀ t : Fin ι.nsorts, t.val < ms.size := fun t => by omega
      let ⟨hminsT⟩ ← Fin.sequenceM fun t : Fin ι.nsorts => Fin.sequenceM fun c : Fin (ι.nctors t) =>
        checkTyped G (mins[(minorIndex ι t c).val]'(hminLt t c))
          (caseFnTypeOf ι I pos ls ps ms G.size hctorsLt hctorLt hrecs hmsLt t c)
      let hisT ← Fin.sequenceM fun i : Fin is.size =>
        checkTyped G (is[i.val]'i.isLt) (I.indexType ls ps s (by omega) is i.val (by omega))
      let ⟨hmaj⟩ ← checkTyped G maj (.ind pos s ls ps is)
      have hsLt : s < ms.size := by omega
      pure ⟨FExpr.motiveResult (ms[s]'hsLt) is maj, fun {ζ E n Γ _} hS hden => by
        have hn := hS.size
        subst hn
        have .recr (ls' := ls') (l' := l') hls hps' hms' hmins' his' hη hs' hls' hl hps'' hms''
          hmins'' his'' hmajd := hden
        have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
        cases hη.symm.trans hη₀
        obtain rfl : _ = (⟨s, hs⟩ : Fin ι.nsorts) := Fin.ext hs'
        have hB := (hS.ordered.entryWF η₀).block
        have ⟨eps, hepsD, hepsT⟩ := TypedSpec.fixArgs hS hps'
          (fts := fun p => I.paramType ls ps p.val (by omega))
          (fun e p => (E.get η₀).block.paramType (⟦ls' ·⟧) e p) hps''
          (fun e he p => hI.paramType hls hls' ⟨hps', he⟩ p)
          (fun e p h => Inductive.paramType_isType hB p h)
          (fun p => hpsT.down ⟨p.val, by omega⟩)
        have hpsA : ArgsDenote L ⟨_, _⟩ ps _ := ⟨hps', hepsD⟩
        have ⟨ems, hemsD, hemsT⟩ := TypedSpec.fixArgs hS hms'
          (fts := fun t => I.motiveType pos ls ps G.size t.val (by omega) l)
          (fun _ t => (E.get η₀).block.motiveType η₀ (⟦ls' ·⟧) eps ⟦l'⟧ t) hms''
          (fun _ _ t => hI.motiveType hls hls' hpsA hη t hl)
          (fun _ t _ => (Inductive.motiveType_congr hB hS.wf hepsT).left)
          (fun t => hmsT.down t)
        have ⟨emins, heminsD, heminsT⟩ := TypedSpec.fixArgs hS hmins'
          (fts := fun j => caseFnTypeOf ι I pos ls ps ms G.size hctorsLt hctorLt hrecs hmsLt
            (Fin.decodeSigma ι.nctors j).1 (Fin.decodeSigma ι.nctors j).2)
          (e₀ := fun j => _)
          (fun _ j => (E.get η₀).block.caseFnType η₀ (⟦ls' ·⟧) eps ems
            (Fin.decodeSigma ι.nctors j).1 (Fin.decodeSigma ι.nctors j).2)
          (fun j => by
            simpa using hmins'' (Fin.decodeSigma ι.nctors j).1 (Fin.decodeSigma ι.nctors j).2)
          (fun _ _ j => (hI.ctors _ _).caseFnType hls hls' hpsA hη (fun r => rfl)
            (fun r => hemsD _) (hemsD _))
          (fun _ j _ => (Inductive.caseFnType_congr hB hS.wf hepsT hemsT).left)
          (fun j => by
            simpa [minorIndex] using hminsT (Fin.decodeSigma ι.nctors j).1 (Fin.decodeSigma ι.nctors j).2)
        have ⟨eis, heisD, heisT⟩ := TypedSpec.fixArgs hS his'
          (fts := fun i => I.indexType ls ps s (by omega) is i.val (by omega))
          (fun e i => (E.get η₀).block.indexType (⟦ls' ·⟧) ⟨s, hs⟩ eps e i) his''
          (fun e he i => hI.indexType hls hls' hpsA _ ⟨his', he⟩ i)
          (fun e i h => Inductive.indexType_isType (hB.indices _) i hS.wf hepsT h)
          (fun i => hisT.down ⟨i.val, by omega⟩)
        have hindD₀ : FExpr.Denotes L ⟨_, _⟩ 0 (.ind pos s ls ps is) _ :=
          .ind hls hps' his' hη rfl hls' hps'' his''
        have hindD : FExpr.Denotes L ⟨_, _⟩ 0 (.ind pos s ls ps is) _ :=
          .ind hls hps' his' hη rfl hls' hepsD heisD
        have ⟨_, _, hmajD, hTD, hmty⟩ := hmaj hS hmajd hindD₀
        have ⟨_, hTty⟩ := hmty.regular
        have hmaj' := (TypeEq.ofDefEq (FExpr.Denotes.defeq hS.ordered hS.wf hTD hindD hTty
          (Defeq.indDF hepsT heisT))).conv hmty
        have hminsD (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) :=
          heminsD (Fin.encodeSigma ι.nctors ⟨t, c⟩)
        have hminsT' (t : Fin ι.nsorts) (c : Fin (ι.nctors t)) :
            E[Γ] ⊢ emins (Fin.encodeSigma ι.nctors ⟨t, c⟩) :
              (E.get η₀).block.caseFnType η₀ (⟦ls' ·⟧) eps ems t c := by
          have := heminsT (Fin.encodeSigma ι.nctors ⟨t, c⟩)
          generalize hx : Fin.decodeSigma ι.nctors (Fin.encodeSigma ι.nctors ⟨t, c⟩) = x at this
          rw [Fin.decodeSigma_encodeSigma] at hx
          subst hx
          exact this
        have hresD := (hemsD ⟨s, hs⟩).motiveResult his' heisD hmajD
        have hres' := hB.motiveResult_congr hS.wf hepsT hemsT heisT hmaj'
        exact ⟨.recr η₀ ⟨s, hs⟩ _ _ eps ems
            (fun t c => emins (Fin.encodeSigma ι.nctors ⟨t, c⟩)) eis _, _,
          .recr hls hps' hms' hmins' his' hη rfl hls' hl hepsD hemsD hminsD heisD hmajD, hresD,
          .recrDF (hI.recAllowed hrec hl) hepsT hemsT hminsT' heisT hmaj' hres'⟩⟩
    | _ => throw (.reject .shape)
  | .quot pos l α r => do
    let ⟨hα⟩ ← checkTyped G α (.sort l)
    let ⟨hr⟩ ← checkTyped G r (FExpr.relType α)
    pure ⟨.sort l, fun {_ _ _ _ _} hS (.quot hη hl hαd hrd) =>
      have ⟨_, hα'D, hα'T⟩ := hα.at hS hαd (.sort hl) ⟨_, .sortDF⟩
      have ⟨_, hr'D, hr'T⟩ := hr.at hS hrd hα'D.relType ⟨_, Quot.relType_congr hα'T⟩
      ⟨_, _, .quot hη hl hα'D hr'D, .sort hl, .quotDF hα'T hr'T⟩⟩
  | .quotMk pos l α r a => do
    let ⟨hα⟩ ← checkTyped G α (.sort l)
    let ⟨hr⟩ ← checkTyped G r (FExpr.relType α)
    let ⟨ha⟩ ← checkTyped G a α
    pure ⟨.quot pos l α r, fun {_ _ _ _ _} hS (.quotMk hη hl hαd hrd had) =>
      have ⟨_, hα'D, hα'T⟩ := hα.at hS hαd (.sort hl) ⟨_, .sortDF⟩
      have ⟨_, hr'D, hr'T⟩ := hr.at hS hrd hα'D.relType ⟨_, Quot.relType_congr hα'T⟩
      have ⟨_, ha'D, ha'T⟩ := ha.at hS had hα'D ⟨_, hα'T⟩
      ⟨_, _, .quotMk hη hl hα'D hr'D ha'D, .quot hη hl hα'D hr'D, .quotMkDF hα'T hr'T ha'T⟩⟩
  | .quotLift pos l₁ l₂ α r β f h a =>
    match hfe : F[pos]? with
    | some (.quot eqPos) => do
      let ⟨hα⟩ ← checkTyped G α (.sort l₁)
      let ⟨hr⟩ ← checkTyped G r (FExpr.relType α)
      let ⟨hβ⟩ ← checkTyped G β (.sort l₂)
      let ⟨hf⟩ ← checkTyped G f (.forallE α β)
      let ⟨hh⟩ ← checkTyped G h (FExpr.compatType eqPos l₂ α r β f)
      let ⟨ha⟩ ← checkTyped G a (.quot pos l₁ α r)
      pure ⟨β, fun {_ _ _ _ _} hS (.quotLift hη hl₁ hl₂ hαd hrd hβd hfd hhd had) => by
        have ⟨η₀, hη₀, hηeq⟩ := FEnv.Denotes.quot (E := ⟨_, _⟩) hfe hS.env
        cases hη.symm.trans hη₀
        have ⟨_, hα'D, hα'T⟩ := hα.at hS hαd (.sort hl₁) ⟨_, .sortDF⟩
        have ⟨_, hr'D, hr'T⟩ := hr.at hS hrd hα'D.relType ⟨_, Quot.relType_congr hα'T⟩
        have ⟨_, hβ'D, hβ'T⟩ := hβ.at hS hβd (.sort hl₂) ⟨_, .sortDF⟩
        have ⟨_, hf'D, hf'T⟩ := hf.at hS hfd (.forallE hα'D hβ'D.wkOpen)
          ⟨_, .forallEDF hα'T (hβ'T.wk _) (hβ'T.wk _)⟩
        have ⟨_, hh'D, hh'T⟩ := hh.at hS hhd
          (FExpr.Denotes.compatType hηeq hl₂ hα'D hr'D hβ'D hf'D)
          (Quot.compatType_isType (hS.eqBlock _) hα'T hr'T hβ'T hf'T)
        have ⟨_, ha'D, ha'T⟩ := ha.at hS had (.quot hη hl₁ hα'D hr'D) ⟨_, .quotDF hα'T hr'T⟩
        exact ⟨_, _, .quotLift hη hl₁ hl₂ hα'D hr'D hβ'D hf'D hh'D ha'D, hβ'D,
          .quotLiftDF hα'T hr'T hβ'T hf'T hh'T ha'T⟩⟩
    | _ => throw (.reject .shape)
  | .quotInd pos l α r β f a => do
    let ⟨hα⟩ ← checkTyped G α (.sort l)
    let ⟨hr⟩ ← checkTyped G r (FExpr.relType α)
    let ⟨hβ⟩ ← checkTyped G β (FExpr.quotMotiveType pos l α r)
    let ⟨hf⟩ ← checkTyped G f (FExpr.quotMinorType pos l α r β)
    let ⟨ha⟩ ← checkTyped G a (.quot pos l α r)
    pure ⟨.app β a, fun {_ _ _ _ _} hS (.quotInd hη hl hαd hrd hβd hfd had) =>
      have ⟨_, hα'D, hα'T⟩ := hα.at hS hαd (.sort hl) ⟨_, .sortDF⟩
      have ⟨_, hr'D, hr'T⟩ := hr.at hS hrd hα'D.relType ⟨_, Quot.relType_congr hα'T⟩
      have ⟨_, hβ'D, hβ'T⟩ := hβ.at hS hβd (FExpr.Denotes.quotMotiveType hη hl hα'D hr'D)
        (Quot.motiveType_isType hα'T hr'T)
      have ⟨_, hf'D, hf'T⟩ := hf.at hS hfd (FExpr.Denotes.quotMinorType hη hl hα'D hr'D hβ'D)
        (Quot.minorType_isType hα'T hr'T hβ'T)
      have ⟨_, ha'D, ha'T⟩ := ha.at hS had (.quot hη hl hα'D hr'D) ⟨_, .quotDF hα'T hr'T⟩
      ⟨_, _, .quotInd hη hl hα'D hr'D hβ'D hf'D ha'D, .app hβ'D ha'D,
        .quotIndDF hα'T hr'T hβ'T hf'T ha'T
          (.appDF (t' := .prop) (.quotDF hα'T hr'T) .sortDF hβ'T ha'T .sortDF)⟩⟩
  | .natLit num =>
    match hfe : F[L.nat]? with
    | some (.inductive ι _) => do
      bounded num
      let ⟨rfl⟩ ← guardProofOr (ι = Literals.Nat.sig) (Failure.decline .literal)
      pure ⟨FExpr.nat L, fun {_ _ _ _ _} _ (.natLit hη) =>
        ⟨_, _, .natLit hη, .nat hη, Literals.natLit_typed _ num⟩⟩
    | _ => throw (.decline .literal)
  | .strLit str => do
    let ⟨ft, h⟩ ← infer G (FExpr.strLitExpand L str)
    pure ⟨ft, fun {_ _ _ _ _} hS hden => by
      have ⟨_, _, hd, htd, hty⟩ := h hS hden.ofStrLit
      obtain rfl := hd.unique hden.ofStrLit (FExpr.strLitExpand_noProj L str)
      exact ⟨_, _, hden, htd, hty⟩⟩

partial def inferOnly (G : FCtx) (fe : FExpr) :
    CheckM L F ℓ {ft : FExpr // InferOnlySpec L F ℓ G fe ft} := do
  match (← get).inferOnly.get? (G, fe) with
  | some r => return r
  | none => pure ()
  let r ← inferOnlyCore G fe
  modify fun c =>
    { c with inferOnly := c.inferOnly.insert (G, fe) r }
  pure r

partial def inferOnlyArgs (G : FCtx) (f : FExpr) (rev : List FExpr) (ftype : FExpr)
    (hf : InferOnlySpec L F ℓ G f (FExpr.instManyRev rev ftype)) :
    (as : List FExpr) → CheckM L F ℓ {t : FExpr // InferOnlySpec L F ℓ G (FExpr.appList f as) t}
  | [] => pure ⟨FExpr.instManyRev rev ftype, hf⟩
  | a :: as =>
    match ftype, hf with
    | .forallE _ b, hf => inferOnlyArgs G (.app f a) (a :: rev) b hf.appPending as
    | ftype, hf => do
      let ⟨_, b, hpi⟩ ← ensureForall G (FExpr.instManyRev rev ftype)
      inferOnlyArgs G (.app f a) [a] b (hf.app hpi) as

partial def inferOnlyCore (G : FCtx) :
    (fe : FExpr) → CheckM L F ℓ {t : FExpr // InferOnlySpec L F ℓ G fe t}
  | .app f a => do
    let ⟨(f₀, as), hfe⟩ := (FExpr.app f a).spine
    let ⟨tf, hf⟩ ← inferOnly G f₀
    let ⟨t, h⟩ ← inferOnlyArgs G f₀ [] tf hf as
    pure ⟨t, hfe ▸ h⟩
  | .lam t b => do
    let ⟨(ds, ty), h⟩ ← inferOnlyLamTele G 0 (Nat.zero_le _) (.lam t b)
    pure ⟨FExpr.mkPi G.size ty ds, fun {_ _ _ _ _ _} hS hden he => h hS hden he⟩
  | .forallE t b => do
    let ⟨l, h⟩ ← inferOnlyPiTele G 0 (Nat.zero_le _) (.forallE t b)
    pure ⟨.sort l, fun {_ _ _ _ _ _} hS hden he => h hS hden he⟩
  | .letE t v b => inferOnlyLetTele G [] (.letE t v b)
  | .ind pos s ls ps is =>
    match hfe : F[pos]? with
    | some (.inductive _ I) =>
      pure ⟨.sort (I.level.inst ls), fun {_ _ _ _ _ _} hS hden he => by
        have .ind hls _ _ hη _ hls' _ _ := hden
        have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
        cases hη.symm.trans hη₀
        have ⟨_, hl, hleq⟩ := hI.levelInst hls hls'
        have ⟨_, _, _, _, ht⟩ := he.ind_inv
        refine ⟨_, .sort hl, ?_⟩
        rw [hleq]
        exact ht.conv he⟩
    | _ => throw (.reject .shape)
  | .ctor pos s c ls ps fds recFds =>
    match hfe : F[pos]? with
    | some (.inductive ι I) => do
      let ⟨hs⟩ ← guardProofOr (s < ι.nsorts) (.reject .shape)
      let ⟨hc⟩ ← guardProofOr (c < ι.nctors ⟨s, hs⟩) (.reject .shape)
      let ⟨hsc⟩ ← guardProofOr (s < I.ctors.size) (.reject .shape)
      let ⟨hcc⟩ ← guardProofOr (c < (I.ctors[s]'hsc).size) (.reject .shape)
      let ctor := (I.ctors[s]'hsc)[c]'hcc
      pure ⟨.ind pos s ls ps (ctor.instTargetIndices ls ps fds), by
        intro ζ E _ Γ _ _ hS hden he
        have hn := hS.size
        subst hn
        have .ctor (η := η) (s' := s') (c' := c') hls hps' hfds' hrecFds' hη hs' hc' hls' hps''
          hfds'' hrecFds'' := hden
        have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
        cases hη.symm.trans hη₀
        obtain rfl : s' = ⟨s, hs⟩ := Fin.ext hs'
        obtain rfl : c' = ⟨c, hc⟩ := Fin.ext hc'
        have hcd := hI.ctors ⟨s, hs⟩ ⟨c, hc⟩
        have hpsA : ArgsDenote L ⟨_, _⟩ ps _ := ⟨hps', hps''⟩
        have hfdsA : ArgsDenote L ⟨_, _⟩ fds _ := ⟨hfds', hfds''⟩
        have hB := (hS.ordered.entryWF η₀).block
        have ⟨_, _, _, hpsw, hfdsw, _, _, ht⟩ := he.ctor_inv
        have hind := Defeq.indDF hpsw fun i =>
          (hB.ctors _ _).targetIndex_congr hB.params i hpsw hfdsw
        exact ⟨_, .ind hls hps' hcd.instTargetIndices_size hη rfl hls' hps''
            (hcd.instTargetIndices hls hls' hpsA hfdsA),
          (ht.trans (.ofDefEq hind)).conv he⟩⟩
    | _ => throw (.reject .shape)
  | .recr pos s ls l ps ms mins is maj => do
    let ⟨hsLt⟩ ← guardProofOr (s < ms.size) (.reject .shape)
    pure ⟨FExpr.motiveResult (ms[s]'hsLt) is maj, fun {_ _ _ _ _ _} hS hden he => by
      have .recr (η := η) (s' := s') hls hps' hms' hmins' his' hη hs' hls' hl hps'' hms'' hmins''
        his'' hmajd := hden
      subst hs'
      have hB := (hS.ordered.entryWF η).block
      have ⟨_, _, _, _, _, _, hpsw, hmsw, _, hisw, hmajw, _, ht⟩ := he.recr_inv
      have hres := hB.motiveResult_congr hS.wf hpsw hmsw hisw hmajw
      exact ⟨_, (hms'' s').motiveResult his' his'' hmajd,
        (ht.trans (.ofDefEq hres)).conv he⟩⟩
  | .quot pos l α r =>
    pure ⟨.sort l, fun {_ _ _ _ _ _} _ (.quot _ hl _ _) he =>
      ⟨_, .sort hl, he.quot_inv.conv he⟩⟩
  | .quotMk pos l α r a =>
    pure ⟨.quot pos l α r, fun {_ _ _ _ _ _} _ (.quotMk hη hl hαd hrd _) he =>
      ⟨_, .quot hη hl hαd hrd, he.quotMk_inv.conv he⟩⟩
  | .quotLift pos l₁ l₂ α r β f h a =>
    pure ⟨β, fun {_ _ _ _ _ _} _ (.quotLift _ _ _ _ _ hβd _ _ _) he =>
      ⟨_, hβd, he.quotLift_inv.conv he⟩⟩
  | .quotInd pos l α r β f a =>
    pure ⟨.app β a, fun {_ _ _ _ _ _} _ (.quotInd _ _ _ _ hβd _ had) he =>
      have ⟨_, _, _, _, _, _, _, _, _, _, hres, ht⟩ := he.quotInd_prem
      ⟨_, .app hβd had, (ht.trans (.ofDefEq hres)).conv he⟩⟩
  | .proj pos s idx e => do
    let ⟨te, hte⟩ ← inferOnly G e
    let ⟨t, ht⟩ ← whnf G te
    match hq : t with
    | .ind pos₂ s₂ ls₂ ps₂ is₂ =>
      match hfe : F[pos]? with
      | some (.inductive ι I) => do
        let ⟨hsame⟩ ← guardProofOr (pos₂ = pos ∧ s₂ = s) (.reject .shape)
        let ⟨hsc⟩ ← guardProofOr (s < I.ctors.size) (.reject .shape)
        let ⟨hcc⟩ ← guardProofOr (0 < (I.ctors[s]'hsc).size) (.reject .shape)
        let ⟨hidx⟩ ← guardProofOr (idx < ((I.ctors[s]'hsc)[0]'hcc).ordinary.size) (.reject .shape)
        pure ⟨((I.ctors[s]'hsc)[0]'hcc).projType pos s ls₂ ps₂ idx hidx e,
          fun {ζ E n Γ _ _} hS hden he => by
          have .proj (η := η) (s' := s') (c' := c') (f' := f') hstructD hη hs' hidx' hed := hden
          obtain ⟨rfl, rfl⟩ := hsame
          subst hs' hidx'
          have he' := he
          rw [Inductive.IsStructure.projTerm_eq_recr] at he'
          have ⟨_, _, _, _, _, _, _, _, _, _, hmajw, _, _⟩ := he'.recr_inv
          have ⟨_, hted, hety⟩ := hte hS hed hmajw.right
          have ⟨_, hu⟩ := hety.regular
          have hred : RedSpec L F ℓ G te (.ind pos₂ s'.val ls₂ ps₂ is₂) := hq ▸ ht
          have ⟨_, .ind (ls' := ls₂') (ps' := ps₂') (is' := isD) hls₂ hps₂ his₂ hη₂ hs₂ hls₂''
            hps₂'' his₂', hc⟩ := hred hS hted hu
          cases hη₂.symm.trans hη
          obtain rfl := (Fin.ext hs₂).symm
          have hmaj₂ := (TypeEq.ofDefEq hc).conv hety
          have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
          cases hη.symm.trans hη₀
          have ⟨_, hindTy⟩ := hmaj₂.regular
          have ⟨_, _, hpsw, _, _⟩ := hindTy.ind_inv
          have hB := (hS.ordered.entryWF η₀).block
          have hind : E[Γ] ⊢ .ind η₀ s' (⟦ls₂' ·⟧) ps₂' isD ≡
              .ind η₀ s' (⟦ls₂' ·⟧) ps₂' hstructD.indices typ :=
            .ofDefEq (Defeq.indDF (fun p => Inductive.paramType_conv hB p hpsw)
              fun i => hstructD.no_indices.elim i)
          have hty₂ := hstructD.projTerm_hasType hB f' hS.wf
            (fun p => Inductive.paramType_conv hB p hpsw) (hind.conv hmaj₂)
          have hP := Inductive.IsStructure.projTerm_congr_defeq hstructD hstructD
            f' f' rfl hS.ordered hS.wf he hty₂ fun ht₁ _ => ht₁
          have hn1 := Fin.eq_one_of_unique c' hstructD.ctor_unique
          have hc0 : c'.val = 0 := by
            omega
          obtain rfl : c' = ⟨0, hn1 ▸ Nat.zero_lt_one⟩ := Fin.ext hc0
          have hd := (hI.ctors _ ⟨0, hn1 ▸ Nat.zero_lt_one⟩).projType hls₂ hls₂'' ⟨hps₂, hps₂''⟩
            hη hstructD hed f'
          exact ⟨_, hd, (Defeq.retype hS.ordered hS.wf hP.symm hty₂).right⟩⟩
      | _ => throw (.reject .shape)
    | _ => throw (.reject .shape)
  | .strLit str => do
    let ⟨ft, h⟩ ← inferOnly G (FExpr.strLitExpand L str)
    pure ⟨ft, fun {_ _ _ _ _ _} hS hden he => h hS hden.ofStrLit he⟩
  | fe => do
    let ⟨ft, h⟩ ← inferCore G fe
    pure ⟨ft, h.toOnly⟩

partial def inferLamTele (G : FCtx) (k : Nat) (hk : k ≤ G.size) :
    (fe : FExpr) →
    CheckM L F ℓ {r : List FExpr × FExpr //
      InferTeleSpec L F ℓ G k fe (FExpr.mkPi G.size r.2 r.1)}
  | .lam t b => do
    let ⟨tt, htt⟩ ← infer G (t.openBVars (G.size - k) k)
    let ⟨_, hl⟩ ← ensureSort G tt
    let ⟨G', hG'⟩ ← pushCtx L F ℓ G (t.openBVars (G.size - k) k)
    let ⟨(ds, ty), hr⟩ ← inferLamTele G' (k + 1) (by subst hG'; simp; omega) b
    pure ⟨(t.openBVars (G.size - k) k :: ds, ty), InferTeleSpec.lam hk htt hl (hG' ▸ hr)⟩
  | fe => do
    let ⟨ty, h⟩ ← infer G (fe.openBVars (G.size - k) k)
    pure ⟨([], ty), InferTeleSpec.base hk h⟩

partial def inferPiTele (G : FCtx) (k : Nat) (hk : k ≤ G.size) :
    (fe : FExpr) → CheckM L F ℓ {l : FLevel // InferTeleSpec L F ℓ G k fe (.sort l)}
  | .forallE t b => do
    let ⟨tt, htt⟩ ← infer G (t.openBVars (G.size - k) k)
    let ⟨l₁, hl₁⟩ ← ensureSort G tt
    let ⟨G', hG'⟩ ← pushCtx L F ℓ G (t.openBVars (G.size - k) k)
    let ⟨l₂, hr⟩ ← inferPiTele G' (k + 1) (by subst hG'; simp; omega) b
    pure ⟨.imax l₁ l₂, InferTeleSpec.pi hk htt hl₁ (hG' ▸ hr)⟩
  | fe => do
    let ⟨tb, htb⟩ ← infer G (fe.openBVars (G.size - k) k)
    let ⟨l, hl⟩ ← ensureSort G tb
    pure ⟨l, InferTeleSpec.baseSort hk htb hl⟩

partial def inferOnlyLamTele (G : FCtx) (k : Nat) (hk : k ≤ G.size) :
    (fe : FExpr) →
    CheckM L F ℓ {r : List FExpr × FExpr //
      InferOnlyTeleSpec L F ℓ G k fe (FExpr.mkPi G.size r.2 r.1)}
  | .lam t b => do
    let ⟨G', hG'⟩ ← pushCtx L F ℓ G (t.openBVars (G.size - k) k)
    let ⟨(ds, ty), hr⟩ ← inferOnlyLamTele G' (k + 1) (by subst hG'; simp; omega) b
    pure ⟨(t.openBVars (G.size - k) k :: ds, ty), fun {_ _ _ _ _ _} hS hden he => by
      subst hG'
      have hn := hS.size
      subst hn
      have .lam htd hbd := hden
      have hd := htd.openBVars (base := G.size - k) (by omega)
      have ⟨_, hb', hchain⟩ := he.lam_inv hS.wf
      have ⟨_, hpi⟩ := hchain.right
      have ⟨_, hts⟩ := hpi.forallE_inv.1
      have ⟨_, htb', hbty⟩ := hr (hS.snoc hd hts) hbd hb'
      have ⟨_, htb''⟩ := hbty.regular
      simp only [Array.size_push] at htb'
      exact ⟨_, .forallE hd (htb'.abstractAt (by omega)), .lamDF hts htb'' htb'' hbty hbty⟩⟩
  | fe => do
    let ⟨ty, h⟩ ← inferOnly G (fe.openBVars (G.size - k) k)
    pure ⟨([], ty), fun {_ _ _ _ _ _} hS hden he => by
      have hn := hS.size
      subst hn
      exact h hS (hden.openBVars (by omega)) he⟩

partial def inferOnlyLetTele (G : FCtx) (rev : List FExpr) :
    (fe : FExpr) →
    CheckM L F ℓ {ty : FExpr // InferOnlySpec L F ℓ G (FExpr.instManyRev rev fe) ty}
  | .letE _ v b => do
    let ⟨r, hr⟩ ← inferOnlyLetTele G (FExpr.instManyRev rev v :: rev) b
    pure ⟨r, InferOnlySpec.letPending hr⟩
  | fe => inferOnly G (FExpr.instManyRev rev fe)

partial def inferOnlyPiTele (G : FCtx) (k : Nat) (hk : k ≤ G.size) :
    (fe : FExpr) → CheckM L F ℓ {l : FLevel // InferOnlyTeleSpec L F ℓ G k fe (.sort l)}
  | .forallE t b => do
    let ⟨tt, htt⟩ ← inferOnly G (t.openBVars (G.size - k) k)
    let ⟨l₁, hl₁⟩ ← ensureSort G tt
    let ⟨G', hG'⟩ ← pushCtx L F ℓ G (t.openBVars (G.size - k) k)
    let ⟨l₂, hr⟩ ← inferOnlyPiTele G' (k + 1) (by subst hG'; simp; omega) b
    pure ⟨.imax l₁ l₂, fun {_ _ _ _ _ _} hS hden he => by
      subst hG'
      have hn := hS.size
      subst hn
      have .forallE htd hbd := hden
      have hd := htd.openBVars (base := G.size - k) (by omega)
      have ⟨⟨_, ht₀⟩, ⟨_, hb₀⟩⟩ := he.forallE_inv
      have ⟨_, htt', htty⟩ := htt hS hd ht₀
      have ⟨_, hl₁', hconv₁⟩ := hl₁ hS htt' htty.regular
      have hts := hconv₁.conv htty
      have ⟨_, hs, hbs⟩ := hr (hS.snoc hd hts) hbd hb₀
      have .sort hl₂' := hs
      exact ⟨_, .sort (.imax hl₁' hl₂'), .forallEDF hts hbs hbs⟩⟩
  | fe => do
    let ⟨tb, htb⟩ ← inferOnly G (fe.openBVars (G.size - k) k)
    let ⟨l, hl⟩ ← ensureSort G tb
    pure ⟨l, fun {_ _ _ _ _ _} hS hden he => by
      have hn := hS.size
      subst hn
      have ⟨_, htb', hbty⟩ := htb hS (hden.openBVars (by omega)) he
      have ⟨_, hl', hconv⟩ := hl hS htb' hbty.regular
      exact ⟨_, .sort hl', hconv.conv hbty⟩⟩

partial def isTypeEqOpen (G : FCtx) (k : Nat) (hk : k ≤ G.size) (ft₁ ft₂ : FExpr) :
    CheckM L F ℓ (PLift (TypeEqTeleSpec L F ℓ G k ft₁ ft₂)) := do
  if heq : ft₁ = ft₂ then
    return ⟨fun {_ _ _ _ _ _} hS hd₁ hd₂ ⟨_, ht₁⟩ ⟨_, ht₂⟩ => by
      subst heq
      exact .ofDefEq (FExpr.Denotes.defeq hS.ordered hS.wf hd₁ hd₂ ht₁ ht₂)⟩
  let ⟨h⟩ ← checkTypeEq G (ft₁.openBVars (G.size - k) k) (ft₂.openBVars (G.size - k) k)
  pure ⟨fun {_ _ _ _ _ _} hS hd₁ hd₂ ht₁ ht₂ => by
    have hn := hS.size
    subst hn
    exact h hS (hd₁.openBVars (by omega)) (hd₂.openBVars (by omega)) ht₁ ht₂⟩

partial def isDefEqPiTele (G : FCtx) (k : Nat) (hk : k ≤ G.size) :
    (fe₁ fe₂ : FExpr) → CheckM L F ℓ (PLift (TypeEqTeleSpec L F ℓ G k fe₁ fe₂))
  | .forallE t₁ b₁, .forallE t₂ b₂ => do
    let ⟨hdom⟩ ← isTypeEqOpen G k hk t₁ t₂
    let ⟨G', hG'⟩ ← pushCtx L F ℓ G (t₁.openBVars (G.size - k) k)
    let ⟨hcod⟩ ← isDefEqPiTele G' (k + 1) (by subst hG'; simp; omega) b₁ b₂
    pure ⟨TypeEqTeleSpec.forallE hk hdom (hG' ▸ hcod)⟩
  | fe₁, fe₂ => isTypeEqOpen G k hk fe₁ fe₂

partial def isDefEqLamTele (G : FCtx) (k : Nat) (hk : k ≤ G.size) :
    (fe₁ fe₂ : FExpr) → CheckM L F ℓ (PLift (DefEqTeleSpec L F ℓ G k fe₁ fe₂))
  | .lam t₁ b₁, .lam t₂ b₂ => do
    let ⟨hdom⟩ ← isTypeEqOpen G k hk t₁ t₂
    let ⟨G', hG'⟩ ← pushCtx L F ℓ G (t₁.openBVars (G.size - k) k)
    let ⟨hbody⟩ ← isDefEqLamTele G' (k + 1) (by subst hG'; simp; omega) b₁ b₂
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
      subst hG'
      have hn := hS.size
      subst hn
      have .lam hdt₁ hb₁ := hd₁
      have .lam hdt₂ hb₂ := hd₂
      have ⟨_, hb₁', hchain₁⟩ := he₁.lam_inv hS.wf
      have ⟨_, hb₂', hchain₂⟩ := he₂.lam_inv hS.wf
      have ⟨_, hpi₁⟩ := hchain₁.right
      have ⟨_, hpi₂⟩ := hchain₂.right
      have ht₁ := hpi₁.forallE_inv.1
      have ht₂ := hpi₂.forallE_inv.1
      have hd := hdom hS hdt₁ hdt₂ ht₁ ht₂
      have ⟨_, ht₁'⟩ := ht₁
      have hb₂'' := Defeq.snocConvTy hd.symm hb₂'
      have hb := hbody (hS.snoc (hdt₁.openBVars (by omega)) ht₁') hb₁ hb₂ hb₁' hb₂''
      have ⟨_, hdl⟩ := hd.sort_uniq hS.ordered hS.wf
      have ⟨_, htb⟩ := hb₁'.regular
      have htb₂ := Defeq.snocConvTy hd htb
      have hb₂ := Defeq.snocConvTy hd hb
      have hlam := Defeq.lamDF hdl htb htb₂ hb hb₂
      exact hchain₁.symm.conv hlam⟩
  | fe₁, fe₂ => do
    let ⟨h⟩ ← isDefEq G (fe₁.openBVars (G.size - k) k) (fe₂.openBVars (G.size - k) k)
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
      have hn := hS.size
      subst hn
      exact h hS (hd₁.openBVars (by omega)) (hd₂.openBVars (by omega)) he₁ he₂⟩

partial def ensureSort (G : FCtx) (ft : FExpr) :
    CheckM L F ℓ {l : FLevel // SortSpec L F ℓ G ft l} := do
  let ⟨ft₂, hred⟩ ← whnf G ft
  match ht : ft₂ with
  | .sort l =>
    pure ⟨l, fun {_ _ _ _ _} hS htd ⟨_, htu⟩ =>
      have hred' : RedSpec L F ℓ G ft (.sort l) := ht ▸ hred
      have ⟨_, .sort hl, hr⟩ := hred' hS htd htu
      ⟨_, hl, .ofDefEq hr⟩⟩
  | _ => throw (Failure.reject .notSort)

partial def ensureForall (G : FCtx) (ft : FExpr) :
    CheckM L F ℓ ((ft₁ : FExpr) × {b : FExpr // ForallSpec L F ℓ G ft ft₁ b}) := do
  let ⟨ft₂, hred⟩ ← whnf G ft
  match ht : ft₂ with
  | .forallE ft₁ b =>
    pure ⟨ft₁, b, fun {_ _ _ _ _} hS htd ⟨_, htu⟩ =>
      have hred' : RedSpec L F ℓ G ft (.forallE ft₁ b) := ht ▸ hred
      have ⟨_, .forallE ht₁ hb, hr⟩ := hred' hS htd htu
      ⟨_, _, ht₁, hb, .ofDefEq hr⟩⟩
  | _ => throw (Failure.reject .notForall)

partial def checkAgainst (G : FCtx) (fe ft : FExpr) :
    CheckM L F ℓ (PLift (CheckSpec L F ℓ G fe ft)) := do
  let ⟨te, he⟩ ← infer G fe
  let ⟨hconv⟩ ← checkTypeEq G te ft
  pure ⟨CheckSpec.ofInfer he hconv⟩

partial def checkTyped (G : FCtx) (fe ft : FExpr) :
    CheckM L F ℓ (PLift (TypedSpec L F ℓ G fe ft)) := do
  let ⟨tt, htt⟩ ← infer G ft
  let ⟨_, hl⟩ ← ensureSort G tt
  let ⟨hc⟩ ← checkAgainst G fe ft
  pure ⟨TypedSpec.ofCheck htt hl hc⟩

partial def checkTypeEq (G : FCtx) (ft₁ ft₂ : FExpr) :
    CheckM L F ℓ (PLift (TypeEqSpec L F ℓ G ft₁ ft₂)) := do
  if heq : ft₁ = ft₂ then
    return ⟨fun {_ _ _ _ _ _} hS hd₁ hd₂ ⟨_, ht₁⟩ ⟨_, ht₂⟩ => by
      subst heq
      exact .ofDefEq (FExpr.Denotes.defeq hS.ordered hS.wf hd₁ hd₂ ht₁ ht₂)⟩
  let ⟨hc⟩ ← isDefEq G ft₁ ft₂
  pure ⟨fun {_ _ _ _ _ _} hS hd₁ hd₂ ⟨_, ht₁⟩ ⟨_, ht₂⟩ => .ofDefEq (hc hS hd₁ hd₂ ht₁ ht₂)⟩

partial def isDefEq (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂)) := do
  if let some ⟨G₀, _, _, hx, hr₁, hr₂, hc₁, hc₂, hi₁, hi₂⟩ ← prefixDefEq G fe₁ fe₂ then
    let ⟨h⟩ ← isDefEq G₀ fe₁ fe₂
    return ⟨h.extend hr₁ hr₂ hc₁ hc₂ hi₁ hi₂ hx⟩
  let r ← isDefEqMain G fe₁ fe₂
  modify fun c =>
    { c with defEq := c.defEq.insert (G, fe₁, fe₂) r }
  pure r

partial def quickDefEq (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (Option (PLift (DefEqSpec L F ℓ G fe₁ fe₂))) := do
  if heq : fe₁ = fe₂ then return some ⟨heq ▸ DefEqSpec.refl fe₁⟩
  if let some h ← succeededBefore G fe₁ fe₂ then return some h
  quickDefEqKind G fe₁ fe₂

partial def quickDefEqKind (G : FCtx) :
    (fe₁ fe₂ : FExpr) → CheckM L F ℓ (Option (PLift (DefEqSpec L F ℓ G fe₁ fe₂)))
  | .lam t₁ b₁, .lam t₂ b₂ => some <$> isDefEqCore G (.lam t₁ b₁) (.lam t₂ b₂)
  | .forallE t₁ b₁, .forallE t₂ b₂ => some <$> isDefEqCore G (.forallE t₁ b₁) (.forallE t₂ b₂)
  | .sort l₁, .sort l₂ => some <$> isDefEqCore G (.sort l₁) (.sort l₂)
  | .natLit num₁, .natLit num₂ => do
    if hnum : num₁ = num₂ then return some ⟨hnum ▸ DefEqSpec.refl _⟩
    throw (.reject .notDefEq)
  | .strLit str₁, .strLit str₂ => do
    if hstr : str₁ = str₂ then return some ⟨hstr ▸ DefEqSpec.refl _⟩
    throw (.reject .notDefEq)
  | _, _ => pure none

partial def isDefEqMain (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂)) := do
  if let some h ← quickDefEq G fe₁ fe₂ then return h
  if !fe₁.data.hasFVar && fe₂ == FExpr.boolLit L true then
    let ⟨fe₃, hr⟩ ← whnf G fe₁
    if heq : fe₃ = fe₂ then
      return ⟨DefEqSpec.ofRedSpec hr (RedSpec.refl fe₂) (heq ▸ DefEqSpec.refl fe₃)⟩
  let ⟨fe₃, hr₁⟩ ← whnfCore G true fe₁
  let ⟨fe₄, hr₂⟩ ← whnfCore G true fe₂
  if !(FExpr.ptrEq fe₃ fe₁ && FExpr.ptrEq fe₄ fe₂) then
    if let some ⟨h⟩ ← quickDefEq G fe₃ fe₄ then return ⟨h.ofRedSpec hr₁ hr₂⟩
  let ⟨h⟩ ← isDefEqReduced G fe₃ fe₄
  pure ⟨h.ofRedSpec hr₁ hr₂⟩

partial def isDefEqReduced (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂)) := do
  match ← tryProofIrrel G fe₁ fe₂ with
  | some h => return h
  | none => pure ()
  match ← lazyDelta G true fe₁ fe₂ with
  | .eq h => pure ⟨h⟩
  | .stuck fe₃ fe₄ hr₁ hr₂ => do
    let ⟨h⟩ ← isDefEqStuck G fe₃ fe₄
    pure ⟨h.ofRedSpec hr₁ hr₂⟩

partial def reduceProjCtor (G : FCtx) (pos s idx : Nat) {e₁ : FExpr} :
    (struct : {e₂ : FExpr // RedSpec L F ℓ G e₁ e₂}) →
    Option {fe : FExpr // RedSpec L F ℓ G (.proj pos s idx e₁) fe}
  | ⟨.ctor pos₂ s₂ _ _ _ fds _, h⟩ =>
    if hsel : pos₂ = pos ∧ s₂ = s ∧ idx < fds.size then
      some ⟨fds[idx]'hsel.2.2, RedSpec.trans (RedSpec.frame (.proj pos s idx) h)
        (RedSpec.projCtor hsel.1 hsel.2.1 hsel.2.2)⟩
    else none
  | _ => none

partial def reduceProjCore (G : FCtx) (pos s idx : Nat) :
    (e₁ : FExpr) → CheckM L F ℓ (Option {fe : FExpr // RedSpec L F ℓ G (.proj pos s idx e₁) fe})
  | .strLit str => do
    let ⟨e₂, h⟩ ← whnf G (FExpr.strLitExpand L str)
    pure (reduceProjCtor G pos s idx ⟨e₂, RedSpec.trans (RedSpec.strLit str) h⟩)
  | e₁ => pure (reduceProjCtor G pos s idx ⟨e₁, RedSpec.refl _⟩)

partial def lazyDeltaProj (G : FCtx) (pos s idx : Nat) (e₁ e₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G (.proj pos s idx e₁) (.proj pos s idx e₂))) := do
  match ← lazyDelta G false e₁ e₂ with
  | .eq h => pure ⟨h.proj⟩
  | .stuck e₃ e₄ hr₁ hr₂ => do
    if let some ⟨f₁, hf₁⟩ ← reduceProjCore G pos s idx e₃ then
      if let some ⟨f₂, hf₂⟩ ← reduceProjCore G pos s idx e₄ then
        let ⟨h⟩ ← isDefEq G f₁ f₂
        return ⟨h.ofRedSpec (RedSpec.trans (RedSpec.frame (.proj pos s idx) hr₁) hf₁)
          (RedSpec.trans (RedSpec.frame (.proj pos s idx) hr₂) hf₂)⟩
    let ⟨h⟩ ← isDefEq G e₃ e₄
    pure ⟨(h.ofRedSpec hr₁ hr₂).proj⟩

partial def tryLazyDeltaProj (G : FCtx) :
    (fe₁ fe₂ : FExpr) → CheckM L F ℓ (Option (PLift (DefEqSpec L F ℓ G fe₁ fe₂)))
  | .proj pos₁ s₁ idx₁ e₁, .proj pos₂ s₂ idx₂ e₂ => do
    if hsame : pos₂ = pos₁ ∧ s₂ = s₁ ∧ idx₂ = idx₁ then
      tryCatch (do
        let ⟨h⟩ ← lazyDeltaProj G pos₁ s₁ idx₁ e₁ e₂
        pure (some ⟨by obtain ⟨rfl, rfl, rfl⟩ := hsame; exact h⟩)) fun _ => pure none
    else pure none
  | _, _ => pure none

partial def isDefEqStuck (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂)) := do
  if let some h ← tryLazyDeltaProj G fe₁ fe₂ then return h
  let ⟨fe₃, hr₁⟩ ← whnfCore G false fe₁
  let ⟨fe₄, hr₂⟩ ← whnfCore G false fe₂
  if !(fe₃ == fe₁ && fe₄ == fe₂) then
    let ⟨h⟩ ← isDefEq G fe₃ fe₄
    return ⟨h.ofRedSpec hr₁ hr₂⟩
  isDefEqCore G fe₁ fe₂ <|> isDefEqStruct G fe₁ fe₂ <|> isDefEqUnitLike G fe₁ fe₂

partial def toCtorWhenK (G : FCtx) (pos s : Nat) (maj : FExpr) :
    CheckM L F ℓ {maj₂ : FExpr // RedSpec L F ℓ G maj maj₂} := do
  match hfe : F[pos]? with
  | some (.inductive ι I) =>
    let some ⟨hK⟩ := KTarget.check ι I s | return ⟨maj, RedSpec.refl maj⟩
    let ⟨ft, ht⟩ ← inferOnly G maj
    let ⟨ft₂, hr⟩ ← whnf G ft
    match hq : ft₂ with
    | .ind pos₂ s₂ ls ps is =>
      if hsame : pos₂ = pos ∧ s₂ = s then
        let fctor := (I.ctors[s]'hK.row)[0]'hK.col
        let ctorTy : FExpr := .ind pos s ls ps (fctor.instTargetIndices ls ps #[])
        match ← tryCatch (some <$> isDefEq G (.ind pos₂ s₂ ls ps is) ctorTy) fun _ => pure none with
        | none => return ⟨maj, RedSpec.refl maj⟩
        | some ⟨hc⟩ =>
          return ⟨.ctor pos s 0 ls ps #[] #[], fun {ζ E n Γ _ _} hS hd he => by
            obtain ⟨rfl, rfl⟩ := hsame
            have ⟨_, hdt, hty⟩ := ht hS hd he
            have ⟨_, htu⟩ := hty.regular
            have hred : RedSpec L F ℓ G ft (.ind pos₂ s₂ ls ps is) := hq ▸ hr
            have ⟨_, hdI, hTc⟩ := hred hS hdt htu
            have .ind (ls' := ls') (ps' := ps') hls hps' his' hη hs' hls' hps'' his'' := hdI
            have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
            cases hη.symm.trans hη₀
            obtain rfl : _ = (⟨s₂, hK.sort⟩ : Fin ι.nsorts) := Fin.ext hs'
            have hcd := hI.ctors ⟨s₂, hK.sort⟩ ⟨0, by rw [hK.ctor]; exact Nat.zero_lt_one⟩
            have hfE : IsEmpty (Fin (ι.ctors ⟨s₂, hK.sort⟩ ⟨0, _⟩).nfields) :=
              ⟨fun f => (hK.fields ▸ f : Fin 0).elim0⟩
            have hrE : IsEmpty (Fin (ι.ctors ⟨s₂, hK.sort⟩ ⟨0, _⟩).nrecFields) :=
              ⟨fun r => (hK.recFields ▸ r : Fin 0).elim0⟩
            have hmajT := (TypeEq.ofDefEq hTc).conv hty
            have ⟨_, hindTy⟩ := hmajT.regular
            have ⟨_, _, hpsw, _, hsortEq⟩ := hindTy.ind_inv
            have hB := (hS.ordered.entryWF η₀).block
            have hpsT p := Inductive.paramType_conv hB p hpsw
            have hpsA : ArgsDenote L ⟨_, _⟩ ps _ := ⟨hps', hps''⟩
            have hfdsA : ArgsDenote L ⟨ζ, E⟩ (#[] : Array FExpr)
                (fun f => hfE.elim f : Fin _ → Expr ζ ℓ n) :=
              ⟨by simp [hK.fields], fun f => hfE.elim f⟩
            have hctorD : FExpr.Denotes L ⟨_, _⟩ 0 (.ctor pos₂ s₂ 0 ls ps #[] #[])
                (.ctor η₀ ⟨s₂, hK.sort⟩ ⟨0, _⟩ (⟦ls' ·⟧) ps' (fun f => hfE.elim f)
                  fun r => hrE.elim r) :=
              .ctor hls hps' (by simp [hK.fields]) (by simp [hK.recFields]) hη rfl rfl hls' hps''
                (fun f => hfE.elim f) (fun r => hrE.elim r)
            have htyD : FExpr.Denotes L ⟨_, _⟩ 0 ctorTy _ :=
              .ind hls hps' (hcd.instTargetIndices_size) hη rfl hls' hps''
                (hcd.instTargetIndices hls hls' hpsA hfdsA)
            have hctorT := Defeq.nullaryCtor (fds := fun f => hfE.elim f)
              (recFds := fun r => hrE.elim r) hB hfE hrE hpsT
            have ⟨_, hctorTyT⟩ := hctorT.regular
            have hcc := hc hS (.ind hls hps' his' hη rfl hls' hps'' his'') htyD hindTy hctorTyT
            have hctor₂ := (TypeEq.ofDefEq hcc).symm.conv hctorT
            have ⟨l₀, hl₀, hl₀'⟩ := hI.level
            rw [hK.level] at hl₀
            have hzero : (E.get η₀).block.level.inst (⟦ls' ·⟧) = Level.zero := by
              rw [← hl₀', hl₀.eq_zero]
              exact Level.inst_zero _
            rw [hzero] at hsortEq
            have hprop := hsortEq.conv hindTy
            have hm := Defeq.proofIrrel hprop hmajT hctor₂
            exact ⟨_, hctorD, Defeq.retype hS.ordered hS.wf hm he⟩⟩
      else return ⟨maj, RedSpec.refl maj⟩
    | _ => return ⟨maj, RedSpec.refl maj⟩
  | _ => return ⟨maj, RedSpec.refl maj⟩

partial def majorToCtor (G : FCtx) (pos s : Nat) (ls : Array FLevel) :
    (maj : FExpr) → CheckM L F ℓ {maj₂ : FExpr // RedSpec L F ℓ G maj maj₂}
  | .natLit num => do
    let ⟨maj₂, h⟩ := litToCtor L F G.size (.natLit num)
    pure ⟨maj₂, RedSpec.ofRed h⟩
  | .strLit str => do
    let ⟨maj₂, h⟩ ← whnf G (FExpr.strLitExpand L str)
    pure ⟨maj₂, RedSpec.trans (RedSpec.strLit str) h⟩
  | maj => etaMajor G pos s ls maj

partial def etaMajor (G : FCtx) (pos s : Nat) (ls : Array FLevel) (maj : FExpr) :
    CheckM L F ℓ {maj' : FExpr // RedSpec L F ℓ G maj maj'} := do
  match F[pos]? with
  | some (.inductive _ I) =>
    if maj matches .ctor .. || !I.isStructure s 0 then
      return ⟨maj, RedSpec.refl maj⟩
    if !(I.level.inst ls).nonZeroWhenPositive then return ⟨maj, RedSpec.refl maj⟩
    match ← etaStruct G maj with
    | some r => pure r
    | none => pure ⟨maj, RedSpec.refl maj⟩
  | _ => pure ⟨maj, RedSpec.refl maj⟩

partial def etaStruct (G : FCtx) (fe₁ : FExpr) :
    CheckM L F ℓ (Option {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂}) :=
  tryCatch (some <$> etaStructCore G fe₁) fun _ => pure none

partial def etaStructCore (G : FCtx) (fe₁ : FExpr) :
    CheckM L F ℓ {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂} := do
  if fe₁ matches .ctor .. then throw (Failure.reject .notDefEq)
  let ⟨ft, ht⟩ ← inferOnly G fe₁
  let ⟨ft₂, hred⟩ ← whnf G ft
  match hq : ft₂ with
  | .ind pos s ls ps is =>
    match hfe : F[pos]? with
    | some (.inductive ι I) => do
      let ⟨hstruct⟩ ← guardProofOr (I.isStructure s 0 = true) (Failure.reject .notDefEq)
      let ⟨hsc⟩ ← guardProofOr (s < I.ctors.size) (Failure.reject .notDefEq)
      let ⟨hcc⟩ ← guardProofOr (0 < (I.ctors[s]'hsc).size) (Failure.reject .notDefEq)
      let ctor := (I.ctors[s]'hsc)[0]'hcc
      let ⟨hsI⟩ ← guardProofOr (s < I.indices.size) (Failure.reject .notDefEq)
      let ⟨hps⟩ ← guardProofOr (ps.size = I.params.size) (Failure.reject .notDefEq)
      pure ⟨ctor.rebuildTerm pos s ls ps fe₁,
        fun {_ _ _ _ _ _} hS hd₁ he₁ => by
          have hn := hS.size
          subst hn
          have hred' : RedSpec L F ℓ G ft (.ind pos s ls ps is) := hq ▸ hred
          have ⟨_, hdt, hty⟩ := ht hS hd₁ he₁
          have ⟨u, htu⟩ := hty.regular
          have ⟨_, .ind hls hps' his' hη hs' hls' hps'' his'', hc⟩ := hred' hS hdt htu
          have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
          cases hη.symm.trans hη₀
          subst hs'
          have hc0 : 0 < ι.nctors _ := hI.ctorsRow _ ▸ hcc
          have hstruct' := hI.isStructure _ ⟨0, hc0⟩ hstruct
          have hcd := hI.ctors _ ⟨0, hc0⟩
          have hpsA : ArgsDenote L ⟨_, _⟩ ps _ := ⟨hps', hps''⟩
          have hind := (TypeEq.ofDefEq hc).conv hty
          have ⟨_, hindTy⟩ := hind.regular
          have ⟨_, _, hpsw, _, _⟩ := hindTy.ind_inv
          have hpsT' p := Inductive.paramType_conv (hS.ordered.entryWF η₀).block p hpsw
          have heta := Checker.structure_eta hstruct' hS.ordered hS.wf hpsT' hind
          exact ⟨_, FCtor.Denotes.rebuildTerm hls hls' hpsA hη hstruct' hd₁ hcd,
            Defeq.retype hS.ordered hS.wf heta he₁⟩⟩
    | _ => throw (Failure.reject .notDefEq)
  | _ => throw (Failure.reject .notDefEq)

partial def isDefEqStruct (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂)) :=
  (do
    unless fe₁ matches .ctor .. do throw (.reject .notDefEq)
    let ⟨fe₃, hη⟩ ← etaStructCore G fe₂
    let ⟨hc⟩ ← isDefEq G fe₁ fe₃
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ =>
      have ⟨_, hd₃, hred⟩ := hη hS hd₂ he₂
      have hc' := hc hS hd₁ hd₃ he₁ hred.right
      hc'.trans (Defeq.retype hS.ordered hS.wf hred.symm hc'.right)⟩) <|>
  do
    unless fe₂ matches .ctor .. do throw (.reject .notDefEq)
    let ⟨fe₃, hη⟩ ← etaStructCore G fe₁
    let ⟨hc⟩ ← isDefEq G fe₃ fe₂
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ =>
      have ⟨_, hd₃, hred⟩ := hη hS hd₁ he₁
      hred.trans (hc hS hd₃ hd₂ hred.right he₂)⟩

partial def isDefEqUnitLike (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂)) := do
  let ⟨ft₁, ht₁⟩ ← inferOnly G fe₁
  let ⟨ft₂, ht₂⟩ ← inferOnly G fe₂
  let ⟨ft, hred⟩ ← whnf G ft₁
  match hq : ft with
  | .ind pos s ls ps is =>
    match hfe : F[pos]? with
    | some (.inductive ι I) => do
      let ⟨hstruct⟩ ← guardProofOr (I.isStructure s 0 = true) (Failure.reject .notDefEq)
      let ⟨hsc⟩ ← guardProofOr (s < I.ctors.size) (Failure.reject .notDefEq)
      let ⟨hcc⟩ ← guardProofOr (0 < (I.ctors[s]'hsc).size) (Failure.reject .notDefEq)
      let ctor := (I.ctors[s]'hsc)[0]'hcc
      let ⟨hfields⟩ ← guardProofOr (ctor.ordinary.size = 0) (Failure.reject .notDefEq)
      let ⟨hps⟩ ← guardProofOr (ps.size = I.params.size) (Failure.reject .notDefEq)
      let ⟨hteq⟩ ← checkTypeEq G ft₁ ft₂
      pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
        have hn := hS.size
        subst hn
        have ⟨_, hdt₁, hty₁⟩ := ht₁ hS hd₁ he₁
        have ⟨_, hdt₂, hty₂⟩ := ht₂ hS hd₂ he₂
        have ⟨u, htu⟩ := hty₁.regular
        have hred' : RedSpec L F ℓ G ft₁ (.ind pos s ls ps is) := hq ▸ hred
        have ⟨_, .ind hls hps' his' hη hs' hls' hps'' his'', hc⟩ := hred' hS hdt₁ htu
        have ⟨η₀, hη₀, hI⟩ := hS.env.inductive hfe
        cases hη.symm.trans hη₀
        subst hs'
        have hc0 : 0 < ι.nctors _ := hI.ctorsRow _ ▸ hcc
        have hstruct' := hI.isStructure _ ⟨0, hc0⟩ hstruct
        have hcd := hI.ctors _ ⟨0, hc0⟩
        have hnf : (ι.ctors _ ⟨0, hc0⟩).nfields = 0 := by
          rw [← hcd.ordinarySize]
          exact hfields
        have hfields' : IsEmpty (Fin (ι.ctors _ ⟨0, hc0⟩).nfields) :=
          ⟨fun f => absurd f.isLt (by omega)⟩
        have hind₁ := (TypeEq.ofDefEq hc).conv hty₁
        have ⟨_, hindTy⟩ := hind₁.regular
        have ⟨_, _, hpsw, _, _⟩ := hindTy.ind_inv
        have hpsT' p := Inductive.paramType_conv (hS.ordered.entryWF η₀).block p hpsw
        have hteq' := hteq hS hdt₁ hdt₂ hty₁.regular hty₂.regular
        have hind₂ := (TypeEq.ofDefEq hc).conv (hteq'.symm.conv hty₂)
        have h := Checker.unit_like_eta hstruct' hfields' hS.ordered hS.wf hpsT' hind₁ hind₂
        exact Defeq.retype hS.ordered hS.wf h he₁⟩
    | _ => throw (Failure.reject .notDefEq)
  | _ => throw (Failure.reject .notDefEq)

partial def inferSorted (G : FCtx) (fe : FExpr) :
    CheckM L F ℓ (PLift (SortedSpec L F ℓ G fe)) := do
  let ⟨_, ⟨h⟩⟩ ← inferSortedLevel G fe
  pure ⟨fun {_ _ _ _ _} hS hd =>
    have ⟨_, _, hd', _, hty⟩ := h hS hd
    ⟨_, _, hd', hty⟩⟩

partial def inferSortedLevel (G : FCtx) (fe : FExpr) :
    CheckM L F ℓ ((l : FLevel) × PLift (SortedAtSpec L F ℓ G fe l)) := do
  let ⟨tt, ht⟩ ← infer G fe
  let ⟨l, hl⟩ ← ensureSort G tt
  pure ⟨l, ⟨fun {_ _ _ _ _} hS hd =>
    have ⟨_, _, hd', htt, hty⟩ := ht hS hd
    have ⟨l', hl', hconv⟩ := hl hS htt hty.regular
    ⟨_, l', hd', hl', hconv.conv hty⟩⟩⟩

partial def isProp (G : FCtx) (ft : FExpr) :
    CheckM L F ℓ (Option (PLift (PropSpec L F ℓ G ft))) := do
  let ⟨s, hs⟩ ← inferOnly G ft
  let ⟨l, hl⟩ ← ensureSort G s
  if hz : l.alwaysZero then
    pure (some ⟨fun {_ _ _ _ _} hS htd ⟨_, htt⟩ => by
      have ⟨_, hs', hty⟩ := hs hS htd htt
      have ⟨_, hl', hr⟩ := hl hS hs' hty.regular
      rw [hl'.interp_eq_zero hz] at hr
      exact hr.conv hty⟩)
  else pure none

partial def tryProofIrrel (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (Option (PLift (DefEqSpec L F ℓ G fe₁ fe₂))) := do
  let ⟨p₁, hp₁⟩ ← inferOnly G fe₁
  match ← isProp G p₁ with
  | none => pure none
  | some ⟨hprop⟩ => do
    let ⟨p₂, hp₂⟩ ← inferOnly G fe₂
    let ⟨hpeq⟩ ← checkTypeEq G p₁ p₂
    pure (some ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
      have ⟨_, hp₁', he₁'⟩ := hp₁ hS hd₁ he₁
      have ⟨_, hp₂', he₂'⟩ := hp₂ hS hd₂ he₂
      have hp := hprop hS hp₁' he₁'.regular
      have ⟨_, hpq⟩ := (hpeq hS hp₁' hp₂' he₁'.regular he₂'.regular).sort_uniq hS.ordered hS.wf
      have h := Defeq.proofIrrel hp he₁' (.defeqDF hpq.symm he₂')
      exact Defeq.retype hS.ordered hS.wf h he₁⟩)

partial def isDefEqOffset (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (Option (PLift (DefEqSpec L F ℓ G fe₁ fe₂))) := do
  match natLitExt L F ℓ G fe₁, natLitExt L F ℓ G fe₂ with
  | some ⟨num₁, h₁⟩, some ⟨num₂, h₂⟩ =>
    if hnum : num₁ = num₂ then
      return some ⟨DefEqSpec.ofRedSpec h₁ h₂ (hnum ▸ DefEqSpec.refl (.natLit num₁))⟩
    throw (.reject .notDefEq)
  | _, _ => pure ()
  match succForm L F ℓ G fe₁, succForm L F ℓ G fe₂ with
  | some ⟨fe₃, h₃⟩, some ⟨fe₄, h₄⟩ =>
    let ⟨h⟩ ← isDefEqCore G fe₃ fe₄
    return some ⟨h.ofRedSpec h₃ h₄⟩
  | _, _ => return none

partial def tryUnfoldProjApp (G : FCtx) (fe₁ : FExpr) :
    CheckM L F ℓ (Option {fe₂ : FExpr // RedSpec L F ℓ G fe₁ fe₂}) := do
  unless fe₁.appHead matches .proj .. do return none
  let ⟨fe₂, h⟩ ← whnfCore G false fe₁
  if fe₂ == fe₁ then return none
  return some ⟨fe₂, h⟩

partial def failedBefore (fe₁ fe₂ : FExpr) : CheckM L F ℓ Bool := do
  let failure := (← get).failure
  return failure.contains (fe₁, fe₂) || failure.contains (fe₂, fe₁)

partial def lazyDelta (G : FCtx) (offsets : Bool) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (Lazy L F ℓ G fe₁ fe₂) := do
  if offsets then
    if let some ⟨h⟩ ← isDefEqOffset G fe₁ fe₂ then return .eq h
  if offsets && !fe₁.data.hasFVar && !fe₂.data.hasFVar then
    if let some ⟨fe₃, hr⟩ ← reduceNat G fe₁ then
      let ⟨h⟩ ← isDefEq G fe₃ fe₂
      return .eq (h.ofRedSpec hr (RedSpec.refl _))
    if let some ⟨fe₄, hr⟩ ← reduceNat G fe₂ then
      let ⟨h⟩ ← isDefEq G fe₁ fe₄
      return .eq (h.ofRedSpec (RedSpec.refl _) hr)
  match isDelta F hints fe₁, isDelta F hints fe₂ with
  | none, none => pure (.stuck fe₁ fe₂ (RedSpec.refl _) (RedSpec.refl _))
  | some _, none => do
    if let some ⟨fe₄, hr⟩ ← tryUnfoldProjApp G fe₂ then
      return Lazy.ofRed (RedSpec.refl _) hr (← lazyStep G offsets fe₁ fe₄)
    let some ⟨fe₃, hr⟩ ← unfoldDefinition G fe₁ | throw .internal
    pure (Lazy.ofRed hr (RedSpec.refl _) (← lazyStep G offsets fe₃ fe₂))
  | none, some _ => do
    if let some ⟨fe₃, hr⟩ ← tryUnfoldProjApp G fe₁ then
      return Lazy.ofRed hr (RedSpec.refl _) (← lazyStep G offsets fe₃ fe₂)
    let some ⟨fe₄, hr⟩ ← unfoldDefinition G fe₂ | throw .internal
    pure (Lazy.ofRed (RedSpec.refl _) hr (← lazyStep G offsets fe₁ fe₄))
  | some (pos₁, h₁), some (pos₂, h₂) => do
    match Hints.compare h₁ h₂ with
    | .lt => do
      let some ⟨fe₃, hr⟩ ← unfoldDefinition G fe₁ | throw .internal
      pure (Lazy.ofRed hr (RedSpec.refl _) (← lazyStep G offsets fe₃ fe₂))
    | .gt => do
      let some ⟨fe₄, hr⟩ ← unfoldDefinition G fe₂ | throw .internal
      pure (Lazy.ofRed (RedSpec.refl _) hr (← lazyStep G offsets fe₁ fe₄))
    | .eq => do
      if fe₁ matches .app .. && fe₂ matches .app .. && pos₁ == pos₂ && h₁ matches .regular _ then
        unless ← failedBefore fe₁ fe₂ do
          match ← tryCatch (some <$> isDefEqArgs G fe₁ fe₂) fun _ => pure none with
          | some ⟨h⟩ => return .eq h
          | none => modify fun c => { c with failure := c.failure.insert (fe₁, fe₂) }
      let some ⟨fe₃, hr₁⟩ ← unfoldDefinition G fe₁ | throw .internal
      let some ⟨fe₄, hr₂⟩ ← unfoldDefinition G fe₂ | throw .internal
      pure (Lazy.ofRed hr₁ hr₂ (← lazyStep G offsets fe₃ fe₄))

partial def lazyStep (G : FCtx) (offsets : Bool) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (Lazy L F ℓ G fe₁ fe₂) := do
  if let some ⟨h⟩ ← quickDefEq G fe₁ fe₂ then return .eq h
  lazyDelta G offsets fe₁ fe₂

partial def succeededBefore (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (Option (PLift (DefEqSpec L F ℓ G fe₁ fe₂))) := do
  match (← get).defEq.get? (G, fe₁, fe₂) with
  | some h => return some h
  | none => pure ()
  match (← get).defEq.get? (G, fe₂, fe₁) with
  | some h => return some ⟨h.down.symm⟩
  | none => pure ()
  return none

partial def isDefEqArgs (G : FCtx) (fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂)) := do
  if let .const pos₁ ls₁ := fe₁.appHead then
    if let .const pos₂ ls₂ := fe₂.appHead then
      unless pos₁ == pos₂ do throw (.reject .notDefEq)
      let _ ← isDefEqLevels ls₁ ls₂
  isDefEqApp G fe₁ fe₂

partial def isDefEqApp (G : FCtx) :
    (fe₁ fe₂ : FExpr) → CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂))
  | .app f a, .app g b => do
    let ⟨ha⟩ ← isDefEq G a b
    let ⟨hf⟩ ← isDefEqApp G f g
    pure ⟨DefEqSpec.app hf ha⟩
  | .const pos₁ ls₁, .const pos₂ ls₂ => do
    let ⟨rfl⟩ ← guardProofOr (pos₁ = pos₂) (.reject .notDefEq)
    let ⟨hl⟩ ← isDefEqLevels ls₁ ls₂
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
      have .const hls₁ hη₁ hls₁' := hd₁
      have .const hls₂ hη₂ hls₂' := hd₂
      cases hη₁.symm.trans hη₂
      rw [hl hls₁ hls₂ hls₁' hls₂'] at he₁ ⊢
      exact he₁⟩
  | fe₁, fe₂ => do
    if heq : fe₁ = fe₂ then return ⟨heq ▸ DefEqSpec.refl fe₁⟩
    throw (.reject .notDefEq)

partial def isDefEqSpine (G : FCtx) :
    (fe₁ fe₂ : FExpr) → CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂))
  | .app f a, .app g b => do
    let ⟨hf⟩ ← isDefEqSpine G f g
    let ⟨ha⟩ ← isDefEq G a b
    pure ⟨DefEqSpec.app hf ha⟩
  | fe₁, fe₂ => isDefEq G fe₁ fe₂

partial def isDefEqLevels (ls₁ ls₂ : Array FLevel) :
    CheckM L F ℓ (PLift (∀ {m : Nat} {ls₁' ls₂' : Fin m → RawLevel ℓ}
      (h₁ : ls₁.size = m) (h₂ : ls₂.size = m),
      (∀ i, FLevel.Denotes (ls₁[i.val]'(h₁.symm ▸ i.isLt)) (ls₁' i)) →
      (∀ i, FLevel.Denotes (ls₂[i.val]'(h₂.symm ▸ i.isLt)) (ls₂' i)) →
      (fun i => (⟦ls₁' i⟧ : Level ℓ)) = (⟦ls₂' ·⟧))) := do
  let ⟨hls⟩ ← guardProofOr (ls₁.size = ls₂.size) (.reject .notDefEq)
  let hl ← Fin.sequenceM fun i : Fin ls₁.size =>
    isDefEqLevel ℓ (ls₁[i.val]) (ls₂[i.val]'(hls ▸ i.isLt))
  pure ⟨fun h₁ _ hd₁ hd₂ => funext fun i =>
    hl.down ⟨i.val, h₁.symm ▸ i.isLt⟩ (hd₁ i) (hd₂ i)⟩

partial def isDefEqArr (G : FCtx) (xs ys : FCtx) (h : ys.size = xs.size) :
    CheckM L F ℓ (PLift (∀ i : Fin xs.size,
      DefEqSpec L F ℓ G (xs[i.val]'i.isLt) (ys[i.val]'(by omega)))) :=
  Fin.sequenceM fun i => isDefEq G (xs[i.val]'i.isLt) (ys[i.val]'(by omega))

partial def isDefEqInd (G : FCtx) (pos₁ s₁ : Nat) (ls₁ : Array FLevel) (ps₁ is₁ : FCtx) (pos₂ s₂ : Nat)
    (ls₂ : Array FLevel) (ps₂ is₂ : FCtx) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G (.ind pos₁ s₁ ls₁ ps₁ is₁) (.ind pos₂ s₂ ls₂ ps₂ is₂))) := do
  let ⟨rfl⟩ ← guardProofOr (pos₁ = pos₂) (.reject .notDefEq)
  let ⟨rfl⟩ ← guardProofOr (s₁ = s₂) (.reject .notDefEq)
  let ⟨hl⟩ ← isDefEqLevels ls₁ ls₂
  let ⟨hps₂⟩ ← guardProofOr (ps₂.size = ps₁.size) (.reject .notDefEq)
  let ⟨his₂⟩ ← guardProofOr (is₂.size = is₁.size) (.reject .notDefEq)
  let hpsD ← isDefEqArr G ps₁ ps₂ hps₂
  let hisD ← isDefEqArr G is₁ is₂ his₂
  pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
    have .ind hls₁ hps₁' his₁' hη₁ hs₁' hls₁' hps₁'' his₁'' := hd₁
    have .ind hls₂ hps₂' his₂' hη₂ hs₂' hls₂' hps₂'' his₂'' := hd₂
    cases hη₁.symm.trans hη₂
    obtain rfl := Fin.ext (hs₁'.trans hs₂'.symm)
    rw [← hl hls₁ hls₂ hls₁' hls₂'] at he₂ ⊢
    have ⟨_, _, hpsw₁, hisw₁, _⟩ := he₁.ind_inv
    have ⟨_, _, hpsw₂, hisw₂, _⟩ := he₂.ind_inv
    have hps p := (hpsw₁ p).trans (hpsD.down ⟨p.val, by omega⟩ hS (hps₁'' p) (hps₂'' p)
      (hpsw₁ p).right (hpsw₂ p).right)
    have his i := (hisw₁ i).trans (hisD.down ⟨i.val, by omega⟩ hS (his₁'' i) (his₂'' i)
      (hisw₁ i).right (hisw₂ i).right)
    exact Defeq.retype hS.ordered hS.wf ((Defeq.indDF hpsw₁ hisw₁).symm.trans (.indDF hps his)) he₁⟩

partial def isDefEqCtor (G : FCtx) (pos₁ s₁ c₁ : Nat) (ls₁ : Array FLevel) (ps₁ fds₁ recFds₁ : FCtx) (pos₂ s₂ c₂ : Nat)
    (ls₂ : Array FLevel) (ps₂ fds₂ recFds₂ : FCtx) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G (.ctor pos₁ s₁ c₁ ls₁ ps₁ fds₁ recFds₁) (.ctor pos₂ s₂ c₂ ls₂ ps₂ fds₂ recFds₂))) := do
  let ⟨rfl⟩ ← guardProofOr (pos₁ = pos₂) (.reject .notDefEq)
  let ⟨rfl⟩ ← guardProofOr (s₁ = s₂) (.reject .notDefEq)
  let ⟨rfl⟩ ← guardProofOr (c₁ = c₂) (.reject .notDefEq)
  let ⟨hl⟩ ← isDefEqLevels ls₁ ls₂
  let ⟨hps₂⟩ ← guardProofOr (ps₂.size = ps₁.size) (.reject .notDefEq)
  let ⟨hfds₂⟩ ← guardProofOr (fds₂.size = fds₁.size) (.reject .notDefEq)
  let ⟨hrecFds₂⟩ ← guardProofOr (recFds₂.size = recFds₁.size) (.reject .notDefEq)
  let hpsD ← isDefEqArr G ps₁ ps₂ hps₂
  let hfdsD ← isDefEqArr G fds₁ fds₂ hfds₂
  let hrecFdsD ← isDefEqArr G recFds₁ recFds₂ hrecFds₂
  pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
    have .ctor (η := η) (s' := s) (c' := c) hls₁ hps₁' hfds₁' hrecFds₁' hη₁ hs₁' hc₁' hls₁'
      hps₁'' hfds₁'' hrecFds₁'' := hd₁
    have .ctor hls₂ hps₂' hfds₂' hrecFds₂' hη₂ hs₂' hc₂' hls₂' hps₂'' hfds₂'' hrecFds₂'' := hd₂
    cases hη₁.symm.trans hη₂
    obtain rfl := Fin.ext (hs₁'.trans hs₂'.symm)
    obtain rfl := Fin.ext (hc₁'.trans hc₂'.symm)
    rw [← hl hls₁ hls₂ hls₁' hls₂'] at he₂ ⊢
    have hB := (hS.ordered.entryWF η).block
    have ⟨_, _, _, hpsw₁, hfdsw₁, hrecFdsw₁, hindw₁, _⟩ := he₁.ctor_inv
    have ⟨_, _, _, hpsw₂, hfdsw₂, hrecFdsw₂, _, _⟩ := he₂.ctor_inv
    have hps p := (hpsw₁ p).trans (hpsD.down ⟨p.val, by omega⟩ hS (hps₁'' p) (hps₂'' p)
      (hpsw₁ p).right (hpsw₂ p).right)
    have hfds f := (hfdsw₁ f).trans (hfdsD.down ⟨f.val, by omega⟩ hS (hfds₁'' f) (hfds₂'' f)
      (hfdsw₁ f).right (hfdsw₂ f).right)
    have hrecFds r := (hrecFdsw₁ r).trans (hrecFdsD.down ⟨r.val, by omega⟩ hS (hrecFds₁'' r)
      (hrecFds₂'' r) (hrecFdsw₁ r).right (hrecFdsw₂ r).right)
    have hctor := hB.ctors s c
    have hleft := hindw₁.ctorDF hpsw₁ hfdsw₁ hrecFdsw₁
      (fun f => (hctor.ordinaryFieldExpr_congr hB.params f hpsw₁ (fun g _ => hfdsw₁ g)))
      (fun r => (hctor.recursiveFieldExpr_congr hB.params rfl r hpsw₁ hfdsw₁).choose_spec)
    have hright := (Defeq.indDF hps fun i =>
      hctor.targetIndex_congr hB.params i hps hfds).ctorDF hps hfds hrecFds
      (fun f => (hctor.ordinaryFieldExpr_congr hB.params f hps (fun g _ => hfds g)))
      (fun r => (hctor.recursiveFieldExpr_congr hB.params rfl r hps hfds).choose_spec)
    exact Defeq.retype hS.ordered hS.wf (hleft.symm.trans hright) he₁⟩

partial def isDefEqRecr (G : FCtx) (pos₁ s₁ : Nat) (ls₁ : Array FLevel) (l₁ : FLevel) (ps₁ ms₁ mins₁ is₁ : FCtx)
    (maj₁ : FExpr) (pos₂ s₂ : Nat) (ls₂ : Array FLevel) (l₂ : FLevel)
    (ps₂ ms₂ mins₂ is₂ : FCtx) (maj₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqSpec L F ℓ G (.recr pos₁ s₁ ls₁ l₁ ps₁ ms₁ mins₁ is₁ maj₁) (.recr pos₂ s₂ ls₂ l₂ ps₂ ms₂ mins₂ is₂ maj₂))) := do
  let ⟨rfl⟩ ← guardProofOr (pos₁ = pos₂) (.reject .notDefEq)
  let ⟨rfl⟩ ← guardProofOr (s₁ = s₂) (.reject .notDefEq)
  let ⟨hl⟩ ← isDefEqLevels ls₁ ls₂
  let ⟨hlv⟩ ← isDefEqLevel ℓ l₁ l₂
  let ⟨hps₂⟩ ← guardProofOr (ps₂.size = ps₁.size) (.reject .notDefEq)
  let ⟨hms₂⟩ ← guardProofOr (ms₂.size = ms₁.size) (.reject .notDefEq)
  let ⟨hmins₂⟩ ← guardProofOr (mins₂.size = mins₁.size) (.reject .notDefEq)
  let ⟨his₂⟩ ← guardProofOr (is₂.size = is₁.size) (.reject .notDefEq)
  let hpsD ← isDefEqArr G ps₁ ps₂ hps₂
  let hmsD ← isDefEqArr G ms₁ ms₂ hms₂
  let hminsD ← isDefEqArr G mins₁ mins₂ hmins₂
  let hisD ← isDefEqArr G is₁ is₂ his₂
  let ⟨hmajD⟩ ← isDefEq G maj₁ maj₂
  pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
    have .recr (ι := ι) (η := η) hls₁ hps₁' hms₁' hmins₁' his₁' hη₁ hs₁' hls₁' hl₁ hps₁''
      hms₁'' hmins₁'' his₁'' hmaj₁ := hd₁
    have .recr hls₂ hps₂' hms₂' hmins₂' his₂' hη₂ hs₂' hls₂' hl₂ hps₂'' hms₂'' hmins₂'' his₂''
      hmaj₂ := hd₂
    cases hη₁.symm.trans hη₂
    obtain rfl := Fin.ext (hs₁'.trans hs₂'.symm)
    rw [← hl hls₁ hls₂ hls₁' hls₂', ← hlv hl₁ hl₂] at he₂ ⊢
    have hB := (hS.ordered.entryWF η).block
    have ⟨_, _, _, _, _, hallowed, hpsw₁, hmsw₁, hminsw₁, hisw₁, hmajw₁, hresw₁, _⟩ :=
      he₁.recr_inv
    have ⟨_, _, _, _, _, _, hpsw₂, hmsw₂, hminsw₂, hisw₂, hmajw₂, _, _⟩ :=
      he₂.recr_inv
    have hps p := (hpsw₁ p).trans (hpsD.down ⟨p.val, by omega⟩ hS (hps₁'' p) (hps₂'' p)
      (hpsw₁ p).right (hpsw₂ p).right)
    have hms t := (hmsw₁ t).trans (hmsD.down ⟨t.val, by omega⟩ hS (hms₁'' t) (hms₂'' t)
      (hmsw₁ t).right (hmsw₂ t).right)
    have hmins t c := (hminsw₁ t c).trans
      (hminsD.down ⟨(Fin.encodeSigma ι.nctors ⟨t, c⟩).val,
        by have := (Fin.encodeSigma ι.nctors ⟨t, c⟩).isLt; omega⟩ hS
        (hmins₁'' t c) (hmins₂'' t c) (hminsw₁ t c).right (hminsw₂ t c).right)
    have his i := (hisw₁ i).trans (hisD.down ⟨i.val, by omega⟩ hS (his₁'' i) (his₂'' i)
      (hisw₁ i).right (hisw₂ i).right)
    have hmaj := hmajw₁.trans (hmajD hS hmaj₁ hmaj₂ hmajw₁.right hmajw₂.right)
    have hleft := Defeq.recrDF hallowed hpsw₁ hmsw₁ hminsw₁ hisw₁ hmajw₁ hresw₁
    have hright := Defeq.recrDF hallowed hps hms hmins his hmaj
      (hB.motiveResult_congr hS.wf hps hms his hmaj)
    exact Defeq.retype hS.ordered hS.wf (hleft.symm.trans hright) he₁⟩

partial def isDefEqCore (G : FCtx) :
    (fe₁ fe₂ : FExpr) → CheckM L F ℓ (PLift (DefEqSpec L F ℓ G fe₁ fe₂))
  | .sort l₁, .sort l₂ => do
    let ⟨hl⟩ ← isDefEqLevel ℓ l₁ l₂
    pure ⟨fun {_ _ _ _ _ _ _ _} _ hd₁ hd₂ he₁ _ => by
      have .sort hl₁ := hd₁
      have .sort hl₂ := hd₂
      rw [hl hl₁ hl₂] at he₁ ⊢
      exact he₁⟩
  | .forallE ft₁ b₁, .forallE ft₂ b₂ => do
    let ⟨h⟩ ← isDefEqPiTele G 0 (Nat.zero_le _) (.forallE ft₁ b₁) (.forallE ft₂ b₂)
    pure ⟨h.toDefEq⟩
  | .lam ft₁ b₁, .lam ft₂ b₂ => do
    let ⟨h⟩ ← isDefEqLamTele G 0 (Nat.zero_le _) (.lam ft₁ b₁) (.lam ft₂ b₂)
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => h hS hd₁ hd₂ he₁ he₂⟩
  | .lam ft₁ b₁, fe₂ => do
    let ⟨tf, hf⟩ ← inferOnly G fe₂
    let ⟨ft₂, _, hpi⟩ ← ensureForall G tf
    let ⟨h⟩ ← isDefEq G (.lam ft₁ b₁) (.lam ft₂ (.app fe₂ (.bvar 0)))
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ =>
      have ⟨_, htf, hfty⟩ := hf hS hd₂ he₂
      have ⟨t₂, _, ht₂, _, hconv⟩ := hpi hS htf hfty.regular
      have hfty' := hconv.conv hfty
      have ⟨_, hty⟩ := hfty'.regular
      have hinv := hty.forallE_inv
      have ⟨_, ht₂'⟩ := hinv.1
      have ⟨_, ht₂''⟩ := hinv.2
      have heta := Defeq.eta ht₂' ht₂'' (by simpa [Expr.wk] using ht₂'.wk t₂)
        (by simpa [Expr.wk] using hfty'.wk t₂) hfty'
      have hd₃ : FExpr.Denotes L ⟨_, _⟩ 0 (.lam ft₂ (.app fe₂ (.bvar 0))) _ :=
        .lam ht₂ (.app hd₂.wkOpen (.bvar rfl (Nat.lt_succ_self 0)))
      have hlam := h hS hd₁ hd₃ he₁ heta.left
      hlam.trans (Defeq.retype hS.ordered hS.wf heta hlam.right)⟩
  | fe₁, .lam ft₂ b₂ => do
    let ⟨h⟩ ← isDefEqCore G (.lam ft₂ b₂) fe₁
    pure ⟨h.symm⟩
  | .const pos₁ ls₁, .const pos₂ ls₂ => isDefEqApp G (.const pos₁ ls₁) (.const pos₂ ls₂)
  | .fvar i, .fvar j => do
    let ⟨rfl⟩ ← guardProofOr (i = j) (.reject .notDefEq)
    pure ⟨DefEqSpec.refl _⟩
  | .app f a, .app g b => do
    unless (FExpr.app f a).appArity == (FExpr.app g b).appArity do throw (.reject .notDefEq)
    isDefEqSpine G (.app f a) (.app g b)
  | .ind pos₁ s₁ ls₁ ps₁ is₁, .ind pos₂ s₂ ls₂ ps₂ is₂ =>
    isDefEqInd G pos₁ s₁ ls₁ ps₁ is₁ pos₂ s₂ ls₂ ps₂ is₂
  | .ctor pos₁ s₁ c₁ ls₁ ps₁ fds₁ recFds₁, .ctor pos₂ s₂ c₂ ls₂ ps₂ fds₂ recFds₂ =>
    isDefEqCtor G pos₁ s₁ c₁ ls₁ ps₁ fds₁ recFds₁ pos₂ s₂ c₂ ls₂ ps₂ fds₂ recFds₂
  | .recr pos₁ s₁ ls₁ l₁ ps₁ ms₁ mins₁ is₁ maj₁, .recr pos₂ s₂ ls₂ l₂ ps₂ ms₂ mins₂ is₂ maj₂ =>
    isDefEqRecr G pos₁ s₁ ls₁ l₁ ps₁ ms₁ mins₁ is₁ maj₁ pos₂ s₂ ls₂ l₂ ps₂ ms₂ mins₂ is₂ maj₂
  | .quot pos₁ l₁ α₁ r₁, .quot pos₂ l₂ α₂ r₂ => do
    let ⟨rfl⟩ ← guardProofOr (pos₁ = pos₂) (.reject .notDefEq)
    let ⟨hl⟩ ← isDefEqLevel ℓ l₁ l₂
    let ⟨hα⟩ ← isDefEq G α₁ α₂
    let ⟨hr⟩ ← isDefEq G r₁ r₂
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
      have .quot hη₁ hl₁ hα₁ hr₁ := hd₁
      have .quot hη₂ hl₂ hα₂ hr₂ := hd₂
      cases hη₁.symm.trans hη₂
      rw [← hl hl₁ hl₂] at he₂ ⊢
      have ⟨hαt₁, hrt₁⟩ := he₁.quot_formation_inv
      have ⟨hαt₂, hrt₂⟩ := he₂.quot_formation_inv
      exact Defeq.retype hS.ordered hS.wf
        (.quotDF (hα hS hα₁ hα₂ hαt₁ hαt₂) (hr hS hr₁ hr₂ hrt₁ hrt₂)) he₁⟩
  | .quotMk pos₁ l₁ α₁ r₁ a₁, .quotMk pos₂ l₂ α₂ r₂ a₂ => do
    let ⟨rfl⟩ ← guardProofOr (pos₁ = pos₂) (.reject .notDefEq)
    let ⟨hl⟩ ← isDefEqLevel ℓ l₁ l₂
    let ⟨hα⟩ ← isDefEq G α₁ α₂
    let ⟨hr⟩ ← isDefEq G r₁ r₂
    let ⟨ha⟩ ← isDefEq G a₁ a₂
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
      have .quotMk (η := η) hη₁ hl₁ hα₁ hr₁ ha₁ := hd₁
      have .quotMk hη₂ hl₂ hα₂ hr₂ ha₂ := hd₂
      cases hη₁.symm.trans hη₂
      rw [← hl hl₁ hl₂] at he₂ ⊢
      have ⟨_, _, _, hαw₁, hrw₁, haw₁, _⟩ := he₁.quotMk_prem
      have ⟨_, _, _, hαw₂, hrw₂, haw₂, _⟩ := he₂.quotMk_prem
      have hleft := Defeq.quotMkDF (η := η) hαw₁ hrw₁ haw₁
      have hright := Defeq.quotMkDF (η := η)
        (hαw₁.trans (hα hS hα₁ hα₂ hαw₁.right hαw₂.right))
        (hrw₁.trans (hr hS hr₁ hr₂ hrw₁.right hrw₂.right))
        (haw₁.trans (ha hS ha₁ ha₂ haw₁.right haw₂.right))
      exact Defeq.retype hS.ordered hS.wf (hleft.symm.trans hright) he₁⟩
  | .quotLift pos₁ l₁ l₂ α₁ r₁ β₁ f₁ h₁ a₁, .quotLift pos₂ l₁' l₂' α₂ r₂ β₂ f₂ h₂ a₂ => do
    let ⟨rfl⟩ ← guardProofOr (pos₁ = pos₂) (.reject .notDefEq)
    let ⟨hlv₁⟩ ← isDefEqLevel ℓ l₁ l₁'
    let ⟨hlv₂⟩ ← isDefEqLevel ℓ l₂ l₂'
    let ⟨hα⟩ ← isDefEq G α₁ α₂
    let ⟨hr⟩ ← isDefEq G r₁ r₂
    let ⟨hβ⟩ ← isDefEq G β₁ β₂
    let ⟨hf⟩ ← isDefEq G f₁ f₂
    let ⟨hh⟩ ← isDefEq G h₁ h₂
    let ⟨ha⟩ ← isDefEq G a₁ a₂
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
      have .quotLift (η := η) hη₁ hl₁ hl₂ hα₁ hr₁ hβ₁ hf₁ hh₁ ha₁ := hd₁
      have .quotLift hη₂ hl₁' hl₂' hα₂ hr₂ hβ₂ hf₂ hh₂ ha₂ := hd₂
      cases hη₁.symm.trans hη₂
      rw [← hlv₁ hl₁ hl₁', ← hlv₂ hl₂ hl₂'] at he₂ ⊢
      have ⟨_, _, _, _, _, _, hαw₁, hrw₁, hβw₁, hfw₁, hhw₁, haw₁, _⟩ :=
        he₁.quotLift_prem
      have ⟨_, _, _, _, _, _, hαw₂, hrw₂, hβw₂, hfw₂, hhw₂, haw₂, _⟩ :=
        he₂.quotLift_prem
      have hleft := Defeq.quotLiftDF (η := η) hαw₁ hrw₁ hβw₁ hfw₁ hhw₁ haw₁
      have hright := Defeq.quotLiftDF (η := η)
        (hαw₁.trans (hα hS hα₁ hα₂ hαw₁.right hαw₂.right))
        (hrw₁.trans (hr hS hr₁ hr₂ hrw₁.right hrw₂.right))
        (hβw₁.trans (hβ hS hβ₁ hβ₂ hβw₁.right hβw₂.right))
        (hfw₁.trans (hf hS hf₁ hf₂ hfw₁.right hfw₂.right))
        (hhw₁.trans (hh hS hh₁ hh₂ hhw₁.right hhw₂.right))
        (haw₁.trans (ha hS ha₁ ha₂ haw₁.right haw₂.right))
      exact Defeq.retype hS.ordered hS.wf (hleft.symm.trans hright) he₁⟩
  | .quotInd pos₁ l₁ α₁ r₁ β₁ f₁ a₁, .quotInd pos₂ l₂ α₂ r₂ β₂ f₂ a₂ => do
    let ⟨rfl⟩ ← guardProofOr (pos₁ = pos₂) (.reject .notDefEq)
    let ⟨hl⟩ ← isDefEqLevel ℓ l₁ l₂
    let ⟨hα⟩ ← isDefEq G α₁ α₂
    let ⟨hr⟩ ← isDefEq G r₁ r₂
    let ⟨hβ⟩ ← isDefEq G β₁ β₂
    let ⟨hf⟩ ← isDefEq G f₁ f₂
    let ⟨ha⟩ ← isDefEq G a₁ a₂
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => by
      have .quotInd (η := η) hη₁ hl₁ hα₁ hr₁ hβ₁ hf₁ ha₁ := hd₁
      have .quotInd hη₂ hl₂ hα₂ hr₂ hβ₂ hf₂ ha₂ := hd₂
      cases hη₁.symm.trans hη₂
      rw [← hl hl₁ hl₂] at he₂ ⊢
      have ⟨_, _, _, _, _, hαw₁, hrw₁, hβw₁, hfw₁, haw₁, hresw₁, _⟩ :=
        he₁.quotInd_prem
      have ⟨_, _, _, _, _, hαw₂, hrw₂, hβw₂, hfw₂, haw₂, _, _⟩ :=
        he₂.quotInd_prem
      have hleft := Defeq.quotIndDF (η := η) hαw₁ hrw₁ hβw₁ hfw₁ haw₁ hresw₁
      have hβ' := hβw₁.trans (hβ hS hβ₁ hβ₂ hβw₁.right hβw₂.right)
      have ha' := haw₁.trans (ha hS ha₁ ha₂ haw₁.right haw₂.right)
      have ⟨_, hmotive⟩ := hβ'.regular
      have ⟨⟨_, hquot⟩, ⟨_, hprop⟩⟩ := hmotive.forallE_inv
      have hright := Defeq.quotIndDF (η := η)
        (hαw₁.trans (hα hS hα₁ hα₂ hαw₁.right hαw₂.right))
        (hrw₁.trans (hr hS hr₁ hr₂ hrw₁.right hrw₂.right))
        hβ'
        (hfw₁.trans (hf hS hf₁ hf₂ hfw₁.right hfw₂.right))
        ha'
        (.appDF hquot hprop hβ' ha' (hprop.inst_congr ha'))
      exact Defeq.retype hS.ordered hS.wf (hleft.symm.trans hright) he₁⟩
  | .strLit str, .app (.const pos ls) a => do
    let ⟨rfl⟩ ← guardProofOr (pos = L.stringOfList) (.reject .notDefEq)
    let ⟨h⟩ ← isDefEqCore G (FExpr.strLitExpand L str) (.app (.const L.stringOfList ls) a)
    pure ⟨fun {_ _ _ _ _ _ _ _} hS hd₁ hd₂ he₁ he₂ => h hS hd₁.ofStrLit hd₂ he₁ he₂⟩
  | .app (.const pos ls) a, .strLit str => do
    let ⟨h⟩ ← isDefEqCore G (.strLit str) (.app (.const pos ls) a)
    pure ⟨h.symm⟩
  | .strLit _, _ | _, .strLit _ => throw (.reject .notDefEq)
  | .natLit num, fe₂ => do
    let ⟨fe₃, hr⟩ := litToCtor L F G.size (.natLit num)
    if fe₃ = .natLit num then throw (.reject .notDefEq)
    let ⟨h⟩ ← isDefEqCore G fe₃ fe₂
    pure ⟨h.ofRedSpec (RedSpec.ofRed hr) (RedSpec.refl _)⟩
  | fe₁, .natLit num => do
    let ⟨h⟩ ← isDefEqCore G (.natLit num) fe₁
    pure ⟨h.symm⟩
  | _, _ => throw (.reject .notDefEq)

end

def isDefEqAt (G : FCtx) (ft fe₁ fe₂ : FExpr) :
    CheckM L F ℓ (PLift (DefEqAtSpec L F ℓ G ft fe₁ fe₂)) := do
  let some ⟨hnt⟩ := ft.noProj | throw .internal
  let some ⟨hn₁⟩ := fe₁.noProj | throw .internal
  let some ⟨hn₂⟩ := fe₂.noProj | throw .internal
  let ⟨h₁⟩ ← checkTyped L F ℓ hints accel G fe₁ ft
  let ⟨h₂⟩ ← checkTyped L F ℓ hints accel G fe₂ ft
  let ⟨h⟩ ← isDefEq L F ℓ hints accel G fe₁ fe₂
  pure ⟨fun {_ _ _ _ _ _ _} hS hdt hd₁ hd₂ => by
    have ⟨_, _, hd₁', hdt₁, hty₁⟩ := h₁ hS hd₁ hdt
    have ⟨_, _, hd₂', hdt₂, hty₂⟩ := h₂ hS hd₂ hdt
    obtain rfl := hd₁.unique hd₁' hn₁
    obtain rfl := hd₂.unique hd₂' hn₂
    obtain rfl := hdt.unique hdt₁ hnt
    obtain rfl := hdt.unique hdt₂ hnt
    exact h hS hd₁ hd₂ hty₁ hty₂⟩

end

end Metalean.FastChecker
