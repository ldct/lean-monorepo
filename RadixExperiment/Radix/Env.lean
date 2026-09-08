/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.AST
import Std.Data.HashMap

/-! # Radix Variable Environment

A thin wrapper around `HashMap String Value` for variable environments.
Each `Frame` contains one `Env`. Variable scoping is handled by the
frame stack in `PState`, not by nested environments -- there is no
lexical scoping or closure capture.
-/

namespace Radix
open Std

abbrev Env := HashMap String Value

namespace Env

def empty : Env := {}

def get? (env : Env) (x : String) : Option Value :=
  HashMap.get? env x

def set (env : Env) (x : String) (v : Value) : Env :=
  HashMap.insert env x v

def remove (env : Env) (x : String) : Env :=
  HashMap.erase env x

end Env
end Radix
