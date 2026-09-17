/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public meta import Lean.Elab.Do.Basic

public meta section

namespace Metalean.Meta

open Lean Elab Term Do

syntax (name := termRflSubst) "rfl_subst% " ident " @ " ident " then " term : term
syntax (name := doRflSubst) "do_rfl_subst% " (ident " @ " ident)+ " then " doSeq : doElem

def rflDoSeq (items : Array Syntax) : TSyntax ``Parser.Term.doSeq :=
  ⟨mkNode ``Parser.Term.doSeqIndent #[mkNullNode items]⟩

def rflDoSeqItem (elem : Syntax) : Syntax :=
  mkNode ``Parser.Term.doSeqItem #[elem, mkNullNode]

def rflSubstPlan (h token : Ident) : TermElabM (FVarId × Term) := do
  let hExpr ← elabTerm h none
  if let .fvar id := hExpr then
    Lean.Meta.withLCtx ((← getLCtx).setUserName id `rfl) (← Lean.Meta.getLocalInstances) do
      addTermInfo' token hExpr
  let ty ← Lean.Meta.whnfR (← instantiateMVars (← Lean.Meta.inferType hExpr))
  let (lhs, rhs, pat) ← match ty.eq?, ty.heq? with
    | some (_, lhs, rhs), _ => pure (lhs, rhs, ← `(rfl))
    | none, some (α, lhs, β, rhs) =>
      unless ← Lean.Meta.isDefEq α β do
        throwErrorAt token m!"`rfl` cannot substitute{indentExpr ty}\n\
          because the two sides have different types"
      pure (lhs, rhs, ← `(HEq.rfl))
    | none, none => throwErrorAt token m!"`rfl` expects an equation, got{indentExpr ty}"
  let substitutable (x other : Expr) : MetaM (Option FVarId) := do
    let .fvar id := x | return none
    if (← id.getDecl).isLet || other.containsFVar id then return none
    return some id
  if let some x ← substitutable rhs lhs then return (x, pat)
  if let some x ← substitutable lhs rhs then return (x, pat)
  throwErrorAt token m!"`rfl` needs one side of{indentExpr ty}\nto be a local variable \
    not occurring in the other side"

def withRflSubstName {m : Type → Type} {α : Type}
    [MonadLCtx m] [MonadLiftT CoreM m] [MonadLiftT MetaM m] [MonadControlT MetaM m] [Monad m]
    (x : FVarId) (k : Ident → m α) : m α := do
  let name ← mkFreshUserName `x
  Lean.Meta.withLCtx ((← getLCtx).setUserName x name) (← Lean.Meta.getLocalInstances)
    (k (mkIdent name))

@[term_elab termRflSubst] def elabTermRflSubst : TermElab := fun stx expectedType? => do
  let `(rfl_subst% $h:ident @ $token:ident then $t) := stx | throwUnsupportedSyntax
  let (x, pat) ← rflSubstPlan h token
  withRflSubstName x fun x => do
    elabTerm (← `(match $x:ident, $h:ident with | _, $pat:term => $t)) expectedType?

@[doElem_elab doRflSubst] def elabDoRflSubst : DoElab := fun stx dec => do
  let `(doElem| do_rfl_subst% $[$hs:ident @ $tokens:ident]* then $rest) := stx
    | throwUnsupportedSyntax
  let (some h, some token) := (hs[0]?, tokens[0]?) | throwUnsupportedSyntax
  let (x, pat) ← rflSubstPlan h token
  let hs := hs.extract 1
  let tokens := tokens.extract 1
  let rest ← if hs.isEmpty then pure rest
    else pure (rflDoSeq #[rflDoSeqItem (← `(doElem| do_rfl_subst% $[$hs @ $tokens]* then $rest))])
  withRflSubstName x fun x => do
    elabDoElem (← `(doElem|
      match (dependent := true) $x:ident, $h:ident with
      | _, $pat:term => $rest)) dec

@[doElem_control_info doRflSubst] def controlInfoDoRflSubst : ControlInfoHandler := fun stx => do
  let `(doElem| do_rfl_subst% $[$_:ident @ $_:ident]* then $rest) := stx
    | throwUnsupportedSyntax
  inferControlInfoElem (← `(doElem| do $rest))

macro_rules (kind := termDepIfThenElse)
  | `(if $token:ident : $c then $t else $e) => do
    unless token.getId == `rfl do Macro.throwUnsupported
    `(if h : $c then rfl_subst% h @ $token then $t else $e)

macro_rules (kind := Lean.Parser.Term.doIf)
  | `(doElem| if $token:ident : $c then $t $[else $e]?) => do
    unless token.getId == `rfl do Macro.throwUnsupported
    `(doElem| if h : $c then do_rfl_subst% h @ $token then $t $[else $e]?)
  | `(doElem| if $token:ident : $_ then $_ $[else if $_ then $_]* $[else $_]?) => do
    unless token.getId == `rfl do Macro.throwUnsupported
    Macro.throwError "`if rfl` does not support `else if`"

partial def replaceRfl : Syntax → MacroM (Syntax × Array (Ident × Ident))
  | stx@(.ident ..) => do
    if stx.getId != `rfl then return (stx, #[])
    let h := mkIdentFrom stx (← withFreshMacroScope (MonadQuotation.addMacroScope `h))
    return (h, #[(h, ⟨stx⟩)])
  | .node info kind args => do
    let mut hs := #[]
    let mut args' := #[]
    for a in args do
      let (a, as) ← replaceRfl a
      args' := args'.push a
      hs := hs ++ as
    return (.node info kind args', hs)
  | stx => return (stx, #[])

partial def rewriteLetRflItems (items : Array Syntax) : MacroM (Array Syntax × Bool) := do
  for h : i in [0:items.size] do
    let `(doElem| let $pat:term ← $c:term) := items[i][0] | continue
    let (pat, pairs) ← replaceRfl pat
    if pairs.isEmpty then continue
    let rest := items.extract (i + 1) items.size
    if rest.isEmpty then
      Macro.throwErrorAt items[i]
        "a `let` pattern containing `rfl` must be followed by the rest of the block"
    let (rest, _) ← rewriteLetRflItems rest
    let hs := pairs.map (·.1)
    let tokens := pairs.map (·.2)
    let bind ← `(doElem| let $(⟨pat⟩):term ← $c:term)
    let subst ← `(doElem| do_rfl_subst% $[$hs @ $tokens]* then $(rflDoSeq rest))
    return ((items.extract 0 i).push (rflDoSeqItem bind) |>.push (rflDoSeqItem subst), true)
  return (items, false)

partial def rewriteLetRfl : Syntax → MacroM (Syntax × Bool)
  | .node info kind args => do
    let mut changed := false
    let mut args' := #[]
    for a in args do
      let (a, c) ← rewriteLetRfl a
      args' := args'.push a
      changed := changed || c
    let index? :=
      if kind == ``Parser.Term.doSeqIndent then some 0
      else if kind == ``Parser.Term.doSeqBracketed then some 1
      else none
    let some index := index? | return (.node info kind args', changed)
    let (items, c) ← rewriteLetRflItems args'[index]!.getArgs
    return (.node info kind (args'.set! index (mkNullNode items)), changed || c)
  | stx => return (stx, false)

macro_rules (kind := Lean.Parser.Term.do)
  | stx => do
    let (stx, changed) ← rewriteLetRfl stx
    unless changed do Macro.throwUnsupported
    return stx

end Metalean.Meta
