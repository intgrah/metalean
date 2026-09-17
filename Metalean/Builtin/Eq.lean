/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/
module

public import Metalean.Syntax.Env
public import Metalean.Syntax.Eq

@[expose] public section

namespace Metalean.Eq

abbrev sigs : Sigs := .snoc .nil (.inductive sig)

def env : Env sigs := .snoc .nil (.inductive block)

abbrev head : Head sigs (.inductive sig) := .here

end Metalean.Eq
