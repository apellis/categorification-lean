import Lake
open Lake DSL

package Categorification where
  moreLeanArgs := #["-DwarningAsError=true"]

require StringDiagrams from git
  "https://github.com/apellis/string-diagrams-lean.git" @
  "34f2d952b3e5bdecea71bf7ba7c0610274660bd9"

require LieLean from git
  "https://github.com/apellis/lie-lean.git" @
  "ba57f07e0b3ca8d701c31d872e6919ab15b29f46"

require DG from git
  "https://github.com/apellis/dg-lean.git" @
  "79a32b105fa512f105b7362c8245635ab876eab2"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.34.1"

@[default_target]
lean_lib Categorification where
  globs := #[.andSubmodules `Categorification]
