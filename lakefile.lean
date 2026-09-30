import Lake
open Lake DSL

package Categorification where
  moreLeanArgs := #["-DwarningAsError=true"]

require StringDiagrams from git
  "https://github.com/apellis/string-diagrams-lean.git" @
  "fb96f497c0dd0a24ed941d3a2c25b4cbfe63d884"

require LieLean from git
  "https://github.com/apellis/lie-lean.git" @
  "da624c7644e753c303259ace2f4f5f0ffba1c970"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.34.1"

@[default_target]
lean_lib Categorification where
  globs := #[.andSubmodules `Categorification]
