/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Radix.Env
import Radix.Heap

/-! # Radix Program State

The runtime state combines a call stack (list of `Frame`s), a heap, and a
function table. The call stack grows on function calls (`pushFrame`) and
shrinks on return (`popFrame`). Variable lookup and mutation always operate
on the topmost frame -- there is no variable capture across frames.
-/

namespace Radix
open Std

/-- A single stack frame: a local variable environment and an optional return
variable name (currently unused but reserved for future call-with-result). -/
structure Frame where
  env : Env := Env.empty
  retVar : Option String := none
  deriving Inhabited

/-- The complete program state. `frames` is a stack (head = current frame).
`funs` is immutable after initialization -- the `BigStep.funs_preserved`
theorem in `Radix.Opt.Inline` proves this invariant. -/
structure PState where
  frames : List Frame := [{}]
  heap : Heap := {}
  funs : HashMap String FunDecl := {}
  deriving Inhabited

namespace PState

def currentFrame (σ : PState) : Option Frame :=
  σ.frames.head?

def updateCurrentFrame (σ : PState) (f : Frame → Frame) : Option PState :=
  match σ.frames with
  | [] => none
  | fr :: rest => some { σ with frames := f fr :: rest }

def getVar (σ : PState) (x : String) : Option Value := do
  let fr ← σ.currentFrame
  fr.env.get? x

def setVar (σ : PState) (x : String) (v : Value) : Option PState :=
  σ.updateCurrentFrame fun fr => { fr with env := fr.env.set x v }

def pushFrame (σ : PState) (fr : Frame) : PState :=
  { σ with frames := fr :: σ.frames }

def popFrame (σ : PState) : Option (Frame × PState) :=
  match σ.frames with
  | [] => none
  | fr :: rest => some (fr, { σ with frames := rest })

def lookupFun (σ : PState) (name : String) : Option FunDecl :=
  σ.funs.get? name

/-- Build the initial state from a program: empty frame, empty heap,
function table populated from the program's declarations. -/
def initFromProgram (p : Program) : PState :=
  let funs := p.funs.foldl (init := ({}:HashMap String FunDecl)) fun m fd => m.insert fd.name fd
  { frames := [{}], heap := {}, funs }

end PState
end Radix
