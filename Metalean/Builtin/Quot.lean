/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Builtin.Eq

/-! # The quotient entry of the builtin environment -/

@[expose] public section

namespace Metalean.Quot

abbrev sigs : Sigs := .snoc Eq.sigs .quot

def env : Env sigs := .snoc Eq.env (.quot Eq.head)

end Metalean.Quot
