import Lake
open Lake DSL

package Categorification where
  moreLeanArgs := #["-DwarningAsError=true"]

require StringDiagrams from git
  "https://github.com/apellis/string-diagrams-lean.git" @
  "e4495caf7733af3318a26058266dca1272379af3"

require LieLean from git
  "https://github.com/apellis/lie-lean.git" @
  "29042522f511a969b7f6dbc81d3c8a8bebfef818"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.34.1"

@[default_target]
lean_lib Categorification where
  globs := #[.andSubmodules `Categorification]
