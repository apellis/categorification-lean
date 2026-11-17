/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleRedEulerForm
import Categorification.WeightedKLR.RedStrands.SingleRedGrading
import Categorification.Algebra.Graded.HomFormEquiv

/-!
# The Euler form of Webster's one-red tensor product algebra

Insertion of the red strand identifies the cyclotomic and Stendhal graded
projective categories. Transport along this equivalence gives Webster's
Corollary 3.22 on all virtual projectives of the one-red algebra.
-/

noncomputable section
namespace Categorification.Stendhal.SingleRed

open KLR KLR.CycKLR KLR.KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot LieLean
open LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
open scoped RatFunc
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [Finite I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hP : IsRouquierQ C Q) (Λ : Fin 1 → I →₀ ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (highest : X)
    (hΛ : ∀ i, (Λ 0 i : ℤ) = RD.pair (RD.iY i) highest) (hR : (projectiveRootDatum RD).IsXRegular)
    (β : Multiset I)
local notation "G" => hP.gradingDatum
local notation "d" => di C
local notation "hd" => (fun i => Eq.symm (two_mul_di C i))
local notation "src" => CycKLR.grade G (Λ 0) β
local notation "dst" => tensorProductGrade (stendhalGradingDatum Λ G d hd) β
local notation "σ" => cyclotomicEquiv Q Λ β
local notation "e" => cyclotomicK0Equiv Λ G d hd β
local notation "wt" => dominantWeight (Λ 0) RD highest hΛ
local notation "η" => projectiveIntegralEquiv hP (Λ 0) RD highest hΛ hR
local notation "ι" => DirectSum.lof (LaurentPolynomial ℤ) _ (fun ν => K0 (CycKLR.grade G (Λ 0) ν))

omit [Finite I] in
include hP in
private theorem finite_cyclotomic : Module.Finite k (CycKLR k Q
    (fun i => (Polynomial.X : Polynomial k) ^ Λ 0 i) β) :=
  module_finite (ν := β) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hP.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun j => Polynomial.monic_X_pow (Λ 0 j))

omit [Finite I] in
include hP in
/-- Every one-red tensor product algebra is finite dimensional, by the
cyclotomic algebra isomorphism and Kang–Kashiwara, Corollary 4.4. -/
theorem finite_singleRed : Module.Finite k (TensorProductAlgebra k Q Λ β) := by
  let := finite_cyclotomic hP Λ β
  exact FiniteDimensional.of_surjective (σ).toLinearEquiv.toLinearMap (σ).surjective

omit [Finite I] in
/-- The one-red grading of a cyclotomic quotient has finite-dimensional
homogeneous pieces and is bounded below. -/
theorem hasGdim_singleRed : HasGdim dst := by
  let := finite_singleRed hP Λ β
  exact HasGdim.of_finiteDimensional _

private local instance : HasGdim dst := hasGdim_singleRed hP Λ β

/-- Webster, Corollary 3.22 and the one-red specialization of Theorem 4.38:
the normalized Shapovalov pairing of the integral images of two projective
classes equals the graded Hom Laurent series, with the right-module order. -/
theorem homForm_eq_shapovalov (x y : K0 dst) :
    lsCast (K0.homForm dst x y) = algebraMap (RatFunc ℚ) (LaurentSeries ℚ)
      (SingleBlack.websterForm wt hR (η (ι β ((e).symm y))).val (η (ι β ((e).symm x))).val) := by
  let := finite_cyclotomic hP Λ β
  let := HasGdim.of_finiteDimensional src
  have h := K0.homForm_map (𝒜 := src) (ℬ := dst) σ
    (fun _ _ hz => cyclotomicEquiv_symm_mem_grade Λ G d hd β hz) ((e).symm x) ((e).symm y)
  change K0.homForm dst (e ((e).symm x)) (e ((e).symm y)) = _ at h
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
  rw [h]
  exact CycKLR.homForm_eq_websterForm hP (Λ 0) RD highest hΛ hR β _ _

end Categorification.Stendhal.SingleRed
