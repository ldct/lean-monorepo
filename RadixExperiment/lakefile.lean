import Lake
open System Lake DSL

require «verso-slides» from git
  "https://github.com/leanprover/verso-slides.git"@"main"

package «radix-slides» where
  version := v!"0.1.0"

lean_lib Radix
lean_lib Slides

@[default_target] lean_exe «radix-slides» where root := `Main
