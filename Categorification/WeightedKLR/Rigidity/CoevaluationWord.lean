/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LieLean.RepresentationTheory.Crystal.KashiwaraSaito
import Mathlib.Data.Finsupp.Multiset

/-!
# The word of the extremal projective

Webster, arXiv:1309.3796v2, Definition 7.1. Read the simple reflections in the
order they are applied to the initial weight. At each step record the current
coroot pairing as a block of the corresponding simple root label. For a path
with nonnegative pairings, the multiplicities are the simple-root coordinates
of the difference between the initial and final weights.
-/

namespace Categorification.Stendhal

variable {I X : Type*} [AddCommGroup X] (D : CartanDatum I X)

/-- The black-strand word for a sequence of simple reflections. The pairings
along a nonnegative reflection path are used as natural multiplicities. -/
def coevaluationWord (weight : X) : List I → List I
  | [] => []
  | i :: w => List.replicate (D.coroot i weight).toNat i ++ coevaluationWord (D.reflection i weight) w

/-- Each coroot pairing is nonnegative at the step where it is read. -/
def NonnegativeReflectionPath (weight : X) : List I → Prop
  | [] => True
  | i :: w => 0 ≤ D.coroot i weight ∧ NonnegativeReflectionPath (D.reflection i weight) w

private theorem multiplicities_replicate [DecidableEq I] (i : I) (n : ℕ) :
    (↑(List.replicate n i) : Multiset I).toFinsupp = Finsupp.single i n := by
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

/-- The black multiplicities record the weight difference along the reflection path. -/
theorem rootSum_coevaluationWord [DecidableEq I] (weight : X) (w : List I)
    (h : NonnegativeReflectionPath D weight w) :
    D.rootSum (↑(coevaluationWord D weight w) : Multiset I).toFinsupp =
      weight - w.foldl (fun μ i => D.reflection i μ) weight := by
  induction w generalizing weight with
  | nil => simp [coevaluationWord]
  | cons i w ih =>
    rcases h with ⟨hi, hw⟩
    simp only [coevaluationWord, ← Multiset.coe_add, Multiset.toFinsupp_add,
      multiplicities_replicate, D.rootSum_add, D.rootSum_single, List.foldl_cons]
    rw [ih _ hw, ← Nat.cast_smul_eq_nsmul ℤ, Int.toNat_of_nonneg hi]
    have step := D.reflection_apply i weight
    rw [step]
    abel

/-- Two nonnegative reflection paths ending at the same weight have the same
black multiplicities when the simple roots are linearly independent. -/
theorem coevaluationWord_multiplicities_eq [DecidableEq I]
    (hD : LinearIndependent ℤ D.root) (weight : X) (v w : List I)
    (hv : NonnegativeReflectionPath D weight v) (hw : NonnegativeReflectionPath D weight w)
    (he : v.foldl (fun μ i => D.reflection i μ) weight =
      w.foldl (fun μ i => D.reflection i μ) weight) :
    (coevaluationWord D weight v : Multiset I) = (coevaluationWord D weight w : Multiset I) := by
  apply Multiset.toFinsupp.injective
  apply D.rootSum_injective hD
  rw [rootSum_coevaluationWord D weight v hv, rootSum_coevaluationWord D weight w hw, he]

end Categorification.Stendhal
