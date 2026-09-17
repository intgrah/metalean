/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public meta import Lean.Elab.Tactic.ElabTerm

public meta section

namespace Metalean.Meta

open Lean Elab.Tactic Meta

/-- Structural induction with the actual constructor available as a local definition in each branch -/
syntax (name := inductionCases) "induction_cases " ident
  (" generalizing " ident+)? " with " ident " => " tacticSeq : tactic

elab_rules : tactic
| `(tactic| induction_cases $h:ident $[generalizing $vars:ident*]?
    with $ctor:ident => $body:tacticSeq) => withMainContext do
  let major ← getFVarId h
  let type ← whnf (← major.getType)
  let info ← getConstInfoInduct type.getAppFn.constName!
  let recInfo ← getConstInfoRec (mkRecName info.name)
  unless recInfo.numMotives == 1 do
    throwError "induction_cases requires a single-motive structural recursor"
  let alts ← recInfo.rules.toArray.mapM fun rule => do
    let alt := mkIdent (.mkSimple rule.ctor.getString!)
    let ref ← Elab.Term.exprToSyntax (mkConst rule.ctor type.getAppFn.constLevels!)
    `(Parser.Tactic.inductionAlt| | $alt:ident =>
      let $ctor:ident := $ref
      ($body:tacticSeq))
  let recursor := mkIdent recInfo.name
  evalTactic (← `(tactic| induction $h:ident using $recursor:ident
    $[generalizing $vars:ident*]? with $alts:inductionAlt*))

end Metalean.Meta
