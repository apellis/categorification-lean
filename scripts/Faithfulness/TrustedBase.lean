import Categorification.Spec.Webster.Thm438
import Categorification.Spec.Webster.Prop55
import Categorification.Spec.Webster.Cor521

/-!
# Trusted base of the Webster specification files

For each statement of `Categorification/Spec/Webster/*.lean`, list the constants of this project
and of its sibling libraries (`StringDiagrams`, `LieLean`) on which the *statement* depends:
the constants occurring in its type, closed under the types and bodies of definitions and the
constructor types of inductive types. Proofs of theorems are not followed. Mathlib and core
constants are trusted and not listed.

Every listed constant is part of what a reader must check against the source; the definition
cards in `docs/Faithfulness/cards/` cover the mathematically meaningful ones. The script fails if
a spec statement is missing or if a statement depends on `sorryAx`.
-/

open Lean Elab Command

namespace Faithfulness

/-- Module-name prefixes of the libraries whose definitions belong to the trusted base. -/
def projectRoots : List Name := [`Categorification, `StringDiagrams, `LieLean]

/-- Whether `c` is declared in a module of this project or of a sibling library. -/
def isProjectConst (env : Environment) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | some idx => projectRoots.any (·.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

/-- The constants occurring in the declaration of `c` that a statement depending on `c` depends
on: the type, the body of a definition, the constructors of an inductive type. -/
def stepConstants (info : ConstantInfo) : Array Name :=
  match info with
  | .defnInfo d => d.type.getUsedConstants ++ d.value.getUsedConstants
  | .opaqueInfo d => d.type.getUsedConstants ++ d.value.getUsedConstants
  | .inductInfo d => d.type.getUsedConstants ++ d.ctors.toArray
  | .ctorInfo d => d.type.getUsedConstants
  | .recInfo d => d.type.getUsedConstants
  | .quotInfo d => d.type.getUsedConstants
  | .axiomInfo d => d.type.getUsedConstants
  | .thmInfo d => d.type.getUsedConstants

/-- The project constants reachable from the type of `root`. Theorems are listed when they
occur (as proof terms inside definitions) but their proofs are not followed. -/
def trustedBase (env : Environment) (root : Name) : Except String (Array Name) := do
  let some info := env.find? root | throw s!"missing spec statement {root}"
  let mut todo : Array Name := info.type.getUsedConstants
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if c == ``sorryAx then throw s!"{root} depends on sorryAx"
    unless isProjectConst env c do continue
    let some ci := env.find? c | continue
    match ci with
    | .thmInfo _ => continue
    | _ =>
      unless c.isInternal do out := out.push c
      todo := todo ++ stepConstants ci
  return out.qsort (·.toString < ·.toString)

/-- The spec statements, by result. -/
def specStatements : List (String × List Name) :=
  [("Webster v2 Theorem 4.38",
      [`Categorification.Spec.Webster.Thm438.existence,
       `Categorification.Spec.Webster.Thm438.uniqueness]),
   ("Webster v2 Proposition 5.5, dimension count",
      [`Categorification.Spec.Webster.Prop55.dimension_count]),
   ("Webster v2 Corollary 5.21",
      [`Categorification.Spec.Webster.Cor521.standard_filtration_of_kernel])]

end Faithfulness

open Faithfulness in
run_cmd do
  let env ← getEnv
  for (label, roots) in specStatements do
    let mut seen : NameSet := {}
    let mut names : Array Name := #[]
    for root in roots do
      match trustedBase env root with
      | .error e => throwError m!"{e}"
      | .ok found =>
        for n in found do
          unless seen.contains n do
            seen := seen.insert n
            names := names.push n
    names := names.qsort (·.toString < ·.toString)
    IO.println s!"== {label}: {names.size} project constants"
    for n in names do
      IO.println s!"  {n}"
  logInfo m!"Trusted bases listed for {specStatements.length} results."
