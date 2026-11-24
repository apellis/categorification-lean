/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CoevaluationWord
import LieLean.RepresentationTheory.Crystal.Path.Stability

/-!
# The coevaluation word for reduced Weyl expressions

Webster, arXiv:1309.3796v2, Definition 7.1. In the integral weight
lattice of a Cartan realization, reducedness and dominance provide the
nonnegative coroot pairings used by the coevaluation word.
-/

open Module

namespace Categorification.Stendhal

private theorem nonnegativeReflectionPath_append_singleton
    {I X : Type*} [AddCommGroup X] (D : CartanDatum I X) (weight : X)
    (w : List I) (i : I) :
    NonnegativeReflectionPath D weight (w ++ [i]) ↔
      NonnegativeReflectionPath D weight w ∧
        0 ≤ D.coroot i (w.foldl (fun μ j => D.reflection j μ) weight) := by
  induction w generalizing weight with
  | nil => simp [NonnegativeReflectionPath]
  | cons j w ih =>
    simp [NonnegativeReflectionPath, ih, and_assoc]

variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K]
  [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (P : Matrix.Realization A K H) (hA : A.IsGeneralizedCartan)

local notation "D" => P.cartanDatum hA
local notation "cs" => P.coxeterSystem hA

private theorem coe_foldl_reflections (w : List I) (weight : P.integralWeights) :
    ((w.foldl (fun μ i => (D).reflection i μ) weight : P.integralWeights) : Dual K H) =
      ((cs).wordProd w.reverse).1 weight := by
  induction w generalizing weight with
  | nil => simp
  | cons i w ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, (cs).wordProd_append, (cs).wordProd_singleton,
      Subgroup.coe_mul, LinearEquiv.mul_apply, P.coxeterSystem_simple, P.coe_reflection_cartanDatum]

/-- A reduced sequence of reflections starting at a dominant integral weight
has the nonnegative coroot pairings used in Webster's coevaluation word. -/
theorem nonnegativeReflectionPath_of_reduced (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Dual K H)) (w : List I)
    (hw : (cs).IsReduced w.reverse) : NonnegativeReflectionPath D weight w := by
  induction w using List.reverseRecOn with
  | nil => trivial
  | append_singleton w i ih =>
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at hw
    have hw' : (cs).IsReduced w.reverse := by
      simpa using hw.drop 1
    refine (nonnegativeReflectionPath_append_singleton D weight w i).mpr ⟨ih hw', ?_⟩
    have hnd : ¬(cs).IsLeftDescent ((cs).wordProd w.reverse) i := by
      apply (cs).not_isLeftDescent_iff.mpr
      rw [← (cs).wordProd_cons, hw.eq, hw'.eq, List.length_cons]
    have h := Matrix.Realization.apply_coroot_nonneg_of_not_isLeftDescent hweight hnd
    rw [← coe_foldl_reflections P hA w weight, ← P.coroot_cartanDatum_cast hA] at h
    exact_mod_cast h

/-- The root content in Definition 7.1 for reduced Weyl words. -/
theorem rootSum_coevaluationWord_of_reduced (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Dual K H)) (w : List I)
    (hw : (cs).IsReduced w.reverse) :
    (((D).rootSum (↑(coevaluationWord D weight w) : Multiset I).toFinsupp :
      P.integralWeights) : Dual K H) = weight - ((cs).wordProd w.reverse).1 weight := by
  rw [rootSum_coevaluationWord D weight w
    (nonnegativeReflectionPath_of_reduced P hA weight hweight w hw),
    AddSubgroup.coe_sub, coe_foldl_reflections P hA]

/-- The multiplicities in Definition 7.1 depend only on the Weyl element
represented by the reduced word. -/
theorem coevaluationWord_multiplicities_eq_of_reduced (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Dual K H)) (v w : List I)
    (hv : (cs).IsReduced v.reverse) (hw : (cs).IsReduced w.reverse)
    (he : (cs).wordProd v.reverse = (cs).wordProd w.reverse) :
    (coevaluationWord D weight v : Multiset I) = (coevaluationWord D weight w : Multiset I) := by
  have hRoots : LinearIndependent ℤ (D).root := by
    apply LinearIndependent.of_comp P.integralWeights.subtype.toIntLinearMap
    change LinearIndependent ℤ P.root
    exact P.linearIndependent_root.restrict_scalars' ℤ
  apply coevaluationWord_multiplicities_eq D hRoots weight v w
    (nonnegativeReflectionPath_of_reduced P hA weight hweight v hv)
    (nonnegativeReflectionPath_of_reduced P hA weight hweight w hw)
  apply Subtype.ext
  simp only [coe_foldl_reflections P hA, he]

end Categorification.Stendhal
