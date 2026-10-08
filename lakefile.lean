import Lake
open Lake DSL

package Categorification where
  moreLeanArgs := #["-DwarningAsError=true"]

require StringDiagrams from git
  "https://github.com/apellis/string-diagrams-lean.git" @
  "6f066162223bcc1762b2eebc1983dfa8e0f90630"

require LieLean from git
  "https://github.com/apellis/lie-lean.git" @
  "aa683687d4e22463e006ecd3fb0b4b9e6d704866"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.34.1"

@[default_target]
lean_lib Categorification where
  globs := #[.andSubmodules `Categorification]
