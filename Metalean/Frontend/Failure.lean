/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

@[expose] public section

namespace Metalean.Frontend

open Lean (Name)

inductive Reject where
  | parse
  | unboundVariable
  | unknownName (name : Name)
  | unknownLevelParam
  | duplicateLevelParam
  | duplicateName
  | arity
  | shape
  | positivity
  | eqShape
  | nonPropTheorem
  | notSort
  | notForall
  | notDefEq
  | recursorLevel
  | fieldLevel
  | propProjection
  | natSize
deriving DecidableEq, Inhabited, Repr

inductive Decline where
  | unreducedOccurrence
  | nested
  | «unsafe»
  | literal
  | unchecked
deriving DecidableEq, Inhabited, Repr

inductive Failure where
  | reject (r : Reject)
  | decline (d : Decline)
  | internal
deriving DecidableEq, Inhabited, Repr

def Failure.exitCode : Failure → UInt32
  | .reject .parse => 3
  | .reject _ => 1
  | .decline _ => 2
  | .internal => 3

end Metalean.Frontend
