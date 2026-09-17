/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Choice

@[expose] public section

namespace Metalean

abbrev classicalSigs : Sigs := .snoc Propext.sigs (.const .axiom 1)

/-- All the axioms and their dependencies -/
def classicalEnv : Env classicalSigs := .snoc Propext.env (.axiom Choice.type)

end Metalean
