import Lake
open System Lake DSL

require «verso-slides» from git
  "https://github.com/leanprover/verso-slides.git"@"main"

package «radix-slides» where
  version := v!"0.1.0"

input_file radixPrelude where
  path := "runtime/radix_io.hpp"

input_file abc177cReference where
  path := "benchmarks/abc177c/reference.cpp"

input_file abc177cOptimized where
  path := "benchmarks/abc177c/optimized.cpp"

lean_lib Radix where
  needs := #[radixPrelude, abc177cReference, abc177cOptimized]
lean_lib Slides

@[default_target] lean_exe «radix-slides» where root := `Main
