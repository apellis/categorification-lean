import Lake
open Lake DSL

package Categorification where
  moreLeanArgs := #["-DwarningAsError=true"]

require StringDiagrams from git
  "https://github.com/apellis/string-diagrams-lean.git" @
  "4540cd4a47cf0c4d8ef7597cdc8a5fa95c84a11f"

require LieLean from git
  "https://github.com/apellis/lie-lean.git" @
  "84222f8a9861e73db9778092c6a9d51ff39315cb"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.34.1"

@[default_target]
lean_lib Categorification where
  globs := #[.andSubmodules `Categorification]
