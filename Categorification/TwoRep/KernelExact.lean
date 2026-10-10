/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Basic

/-!
# The tactic `kernel_exact`

`kernel_exact e` closes the main goal with the term `e` without asking the elaborator to unify the
type of `e` with the goal: the kernel checks the declaration when it is added, as for every proof.

This is useful when the type of `e` and the goal agree only up to the normalization of universe
levels, e.g. a lemma proved for arbitrary bicategories and instantiated at a bicategory whose
universe levels are expressions such as `max u v`, against a statement written out by hand (whose
universe levels the elaborator normalizes). On large terms the elaborator's unifier may then unfold
both sides completely before comparing levels, while the kernel decides the equality directly.
-/

namespace Categorification

open Lean Elab Tactic Meta

/-- `kernel_exact e` closes the main goal with `e`, leaving the comparison of the type of `e`
with the goal to the kernel. -/
elab "kernel_exact " e:term : tactic => withMainContext do
  let g ← getMainGoal
  let e ← elabTerm e none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasExprMVar then
    throwError "kernel_exact: the term has unassigned metavariables"
  g.assign e
  replaceMainGoal []

end Categorification
