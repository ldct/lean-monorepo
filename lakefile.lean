import Lake
open Lake DSL

package «LeanGT» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require Regex from git
  "https://github.com/bergmannjg/regex" @ "main"

@[default_target]
lean_lib «LeanGT» where
  -- add any library configuration options here
