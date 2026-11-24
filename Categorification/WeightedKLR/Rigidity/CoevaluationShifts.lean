/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CoevaluationWord

/-!
# Degrees of the coevaluation word

Webster, arXiv:1309.3796v2, Definition 7.4. The two shift numbers can be
read from the length and the sum of simple-root symmetrizers in the
coevaluation word, when the respective functional changes sign at its endpoint.
-/

namespace Categorification.Stendhal

variable {I X : Type*} [AddCommGroup X] (D : CartanDatum I X)

/-- Evaluating the difference between the two endpoints on an additive
weight functional gives the sum of the evaluations of the black roots. -/
theorem sum_coevaluationWord_apply_root (f : X →+ ℤ)
    (weight : X) (w : List I) (h : NonnegativeReflectionPath D weight w) :
    ((coevaluationWord D weight w).map (fun i => f (D.root i))).sum =
      f weight - f (w.foldl (fun μ i => D.reflection i μ) weight) := by
  induction w generalizing weight with
  | nil => simp [coevaluationWord]
  | cons i w ih =>
    rcases h with ⟨hi, hw⟩
    rw [coevaluationWord, List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
      ih (D.reflection i weight) hw, List.foldl_cons]
    rw [← Nat.cast_smul_eq_nsmul ℤ, Int.toNat_of_nonneg hi, D.reflection_apply, map_sub, map_zsmul]
    abel

/-- If the final reflection sends the functional to its negative at the
initial weight, the weighted black content is twice the initial evaluation.
This is the shift calculation in Webster, arXiv:1309.3796v2, Definition 7.4. -/
theorem sum_coevaluationWord_apply_root_of_final_neg (f : X →+ ℤ)
    (weight : X) (w : List I) (h : NonnegativeReflectionPath D weight w)
    (hfinal : f (w.foldl (fun μ i => D.reflection i μ) weight) = -f weight) :
    ((coevaluationWord D weight w).map (fun i => f (D.root i))).sum = 2 * f weight := by
  rw [sum_coevaluationWord_apply_root D f weight w h, hfinal]
  omega

private theorem sum_map_eq_two_mul_sum {I : Type*} (f g : I → ℤ)
    (hf : ∀ i, f i = 2 * g i) (word : List I) :
    (word.map f).sum = 2 * (word.map g).sum := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    simp only [List.map_cons, List.sum_cons, hf, ih]
    omega

/-- If twice the inner-product functional evaluates to twice the root
symmetrizer on each simple root, the sum of the symmetrizers over the black
word equals the internal shift in Webster, arXiv:1309.3796v2, Definition 7.4. -/
theorem coevaluationWord_sum_symmetrizers_eq_twice_pairing
    (twicePairing : X →+ ℤ) (symmetrizer : I → ℤ)
    (hroot : ∀ i, twicePairing (D.root i) = 2 * symmetrizer i)
    (weight : X) (w : List I) (h : NonnegativeReflectionPath D weight w)
    (hfinal : twicePairing (w.foldl (fun μ i => D.reflection i μ) weight) = -twicePairing weight) :
    ((coevaluationWord D weight w).map symmetrizer).sum = twicePairing weight := by
  have he := sum_coevaluationWord_apply_root_of_final_neg D twicePairing weight w h hfinal
  rw [sum_map_eq_two_mul_sum _ _ hroot] at he
  omega

/-- Applying twice the height functional, which takes each simple root to
two, identifies the number of black strands with Webster's homological
shift before the minus sign (arXiv:1309.3796v2, Definition 7.4). -/
theorem coevaluationWord_length_eq_twice_height (twiceHeight : X →+ ℤ)
    (hroot : ∀ i, twiceHeight (D.root i) = 2)
    (weight : X) (w : List I) (h : NonnegativeReflectionPath D weight w)
    (hfinal : twiceHeight (w.foldl (fun μ i => D.reflection i μ) weight) = -twiceHeight weight) :
    ((coevaluationWord D weight w).length : ℤ) = twiceHeight weight := by
  have he := coevaluationWord_sum_symmetrizers_eq_twice_pairing D twiceHeight (fun _ => 1)
    (fun i => by simpa using hroot i) weight w h hfinal
  simpa using he

end Categorification.Stendhal
