/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CoevaluationDividedPower
import Categorification.WeightedKLR.Rigidity.ReducedCoevaluationWord

/-!
# The coevaluation word of the dual weight

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Proposition 7.8: the standard module `M_λ = S^{κ₀}_{i_{λ*}}` is built from the divided word of
`λ* = -w₀λ` for a reduced expression of `w₀`. For the divided coevaluation word `d` of `λ` along
`w`, the divided word of `-wλ` along the reversed expression is `d̄ = d.reverse`
(`coevaluationDividedWord_reverse`), and `-w₀λ` is dominant when every simple reflection is a
left descent of `w₀` (`isDominantIntegral_neg_foldl`).
-/

open Module

namespace Categorification.Stendhal

section Datum

variable {I X : Type*} [AddCommGroup X] (D : CartanDatum I X)

theorem foldl_reflection_neg (w : List I) (x : X) :
    w.foldl (fun μ j => D.reflection j μ) (-x) = -(w.foldl (fun μ j => D.reflection j μ) x) := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => simp only [List.foldl_cons, map_neg, ih]

theorem foldl_reverse_foldl_reflection (w : List I) (x : X) :
    w.reverse.foldl (fun μ j => D.reflection j μ) (w.foldl (fun μ j => D.reflection j μ) x) =
      x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      CartanDatum.reflection_reflection]

/-- **The divided word of the dual weight.** Along the reversed expression, the divided
coevaluation word of `-wλ` is the reversed divided coevaluation word of `λ`: the `m`-th block of
the former pairs `α_{w_{k+1-m}}^∨` with `-s_{w_{k+2-m}} ⋯ s_{w_k} wλ = -s_{w_{k+1-m}} ⋯ s_{w_1} λ`.
-/
theorem coevaluationDividedWord_reverse (weight : X) (w : List I) :
    coevaluationDividedWord D (-(w.foldl (fun μ j => D.reflection j μ) weight)) w.reverse =
      (coevaluationDividedWord D weight w).reverse := by
  induction w generalizing weight with
  | nil => rfl
  | cons i w ih =>
    rw [List.reverse_cons, coevaluationDividedWord_snoc, List.foldl_cons, ih,
      coevaluationDividedWord, List.reverse_cons, foldl_reflection_neg,
      foldl_reverse_foldl_reflection, map_neg, CartanDatum.coroot_reflection, neg_neg]

end Datum

section Realization

variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K]
  [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (P : Matrix.Realization A K H) (hA : A.IsGeneralizedCartan)

local notation "D" => P.cartanDatum hA
local notation "cs" => P.coxeterSystem hA

theorem coe_foldl_reflection_cartanDatum (w : List I) (weight : P.integralWeights) :
    ((w.foldl (fun μ i => (D).reflection i μ) weight : P.integralWeights) : Dual K H) =
      ((cs).wordProd w.reverse).1 weight := by
  induction w generalizing weight with
  | nil => simp
  | cons i w ih =>
    rw [List.foldl_cons, ih, List.reverse_cons, (cs).wordProd_append, (cs).wordProd_singleton,
      Subgroup.coe_mul, LinearEquiv.mul_apply, P.coxeterSystem_simple, P.coe_reflection_cartanDatum]

variable {P hA} in
/-- At a left descent `i` of `g`, a dominant integral weight moved by `g` pairs nonpositively
with `αᵢ^∨`. -/
theorem apply_coroot_nonpos_of_isLeftDescent {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)
    {g : P.weylGroup hA} {i : I} (hg : (cs).IsLeftDescent g i) : g.1 Λ (P.coroot i) ≤ 0 := by
  have hnd : ¬(cs).IsLeftDescent ((cs).simple i * g) i :=
    ((cs).isLeftDescent_iff_not_isLeftDescent_mul).mp hg
  have h := Matrix.Realization.apply_coroot_nonneg_of_not_isLeftDescent hΛ hnd
  have hg' : g = (cs).simple i * ((cs).simple i * g) := ((cs).simple_mul_simple_cancel_left i).symm
  rw [hg', Subgroup.coe_mul, LinearEquiv.mul_apply, P.coxeterSystem_simple, P.reflection_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, P.root_coroot_self hA, smul_eq_mul]
  linarith

/-- **The dual weight is dominant**: if every simple reflection is a left descent of the Weyl
element `w₀` of `w`, then `-w₀λ` is dominant integral for dominant integral `λ`. -/
theorem isDominantIntegral_neg_foldl (weight : P.integralWeights) (w : List I)
    (hweight : P.IsDominantIntegral (weight : Dual K H))
    (hlong : ∀ i, (cs).IsLeftDescent ((cs).wordProd w.reverse) i) :
    P.IsDominantIntegral
      ((-(w.foldl (fun μ j => (D).reflection j μ) weight) : P.integralWeights) : Dual K H) := by
  intro i
  have h := apply_coroot_nonpos_of_isLeftDescent hweight (hlong i)
  rw [← coe_foldl_reflection_cartanDatum P hA, ← P.coroot_cartanDatum_cast hA] at h
  refine ⟨(-((D).coroot i (w.foldl (fun μ j => (D).reflection j μ) weight))).toNat, ?_⟩
  rw [← P.coroot_cartanDatum_cast hA, map_neg]
  have h0 : (0 : ℤ) ≤ -((D).coroot i (w.foldl (fun μ j => (D).reflection j μ) weight)) := by
    have : ((D).coroot i (w.foldl (fun μ j => (D).reflection j μ) weight) : K) ≤ 0 := h
    have : (D).coroot i (w.foldl (fun μ j => (D).reflection j μ) weight) ≤ 0 := by
      exact_mod_cast this
    omega
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]

end Realization

end Categorification.Stendhal
