/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SingleRedHomForm
import Categorification.Algebra.Graded.HomFormPolynomial

/-!
# The integral Laurent polynomial of the single-red Euler pairing

Webster, arXiv:1309.3796v2, Corollary 3.22 and Theorem 4.20. For
each pair of virtual projectives there is a unique integral Laurent
polynomial whose coefficients are their Euler series and whose value
at the indeterminate is the normalized one-factor Shapovalov pairing.
-/

noncomputable section
namespace Categorification

open KLR KLR.CycKLR KLR.KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot LieLean
open LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "series" => algebraMap L (LaurentSeries ℚ)

private theorem expand_integralLaurentEval (p : LP) :
    series (integralLaurentEval p) = lsCast (toLaurentSeries p) := by
  rw [lsCast_toLaurentSeries, vToLS, RingHom.comp_apply, barQ_qToV]
  congr 1
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single n m =>
    have hT : (AddMonoidAlgebra.single n m : LP) = m • LaurentPolynomial.T n := by
      rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.smul_eq_C_mul]
    rw [hT, map_zsmul, map_zsmul, map_zsmul, LaurentPolynomial.invert_T,
      integralLaurentEval_T, qToV_T, Units.val_zpow_eq_zpow_val, vQ_val, neg_neg]

private theorem existsUnique_common_polynomial {k A : Type*} [Field k] [Ring A] [Algebra k A]
    [Module.Finite k A] (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] [HasGdim 𝒜]
    (x y : K0 𝒜) (r : L) (h : lsCast (K0.homForm 𝒜 x y) = series r) :
    ∃! p : LP, toLaurentSeries p = K0.homForm 𝒜 x y ∧ integralLaurentEval p = r := by
  obtain ⟨p, hp⟩ := K0.exists_homForm_polynomial 𝒜 x y
  refine ⟨p, ⟨hp, (algebraMap L (LaurentSeries ℚ)).injective ?_⟩,
    fun q hq => toLaurentSeries_injective (hq.1.trans hp.symm)⟩
  rw [expand_integralLaurentEval, hp, h]

namespace Stendhal.SingleRed

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
variable {I k : Type*} [DecidableEq I] [Finite I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hP : IsRouquierQ C Q) (Λ : Fin 1 → I →₀ ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (highest : X)
    (hΛ : ∀ i, (Λ 0 i : ℤ) = RD.pair (RD.iY i) highest) (hR : (projectiveRootDatum RD).IsXRegular)
    (β : Multiset I)
local notation "G" => hP.gradingDatum
local notation "dst" => tensorProductGrade (stendhalGradingDatum Λ G (di C)
  (fun i => Eq.symm (two_mul_di C i))) β
local notation "e" => cyclotomicK0Equiv Λ G (di C) (fun i => Eq.symm (two_mul_di C i)) β
local notation "wt" => dominantWeight (Λ 0) RD highest hΛ
local notation "η" => projectiveIntegralEquiv hP (Λ 0) RD highest hΛ hR
local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (CycKLR.grade G (Λ 0) ν))

private local instance : HasGdim dst := hasGdim_singleRed hP Λ β

/-- The common integral Laurent polynomial of Webster's Corollary 3.22,
for arbitrary virtual projectives of the one-red block. -/
theorem existsUnique_eulerPolynomial (x y : K0 dst) :
    ∃! p : LP, toLaurentSeries p = K0.homForm dst x y ∧ integralLaurentEval p =
      SingleBlack.websterForm wt hR (η (ι β ((e).symm y))).val (η (ι β ((e).symm x))).val := by
  let := finite_singleRed hP Λ β
  exact existsUnique_common_polynomial dst x y _
    (homForm_eq_shapovalov hP Λ RD highest hΛ hR β x y)

/-- For actual projectives the common polynomial is the homogeneous Hom
dimension polynomial itself. -/
theorem homGdimPoly_eq_shapovalov (P Q' : GProj dst) :
    integralLaurentEval (gdimPoly (homGrade (TensorProductAlgebra k Q Λ β) P.grading Q'.grading)) =
      SingleBlack.websterForm wt hR (η (ι β ((e).symm (K0.of Q')))).val
        (η (ι β ((e).symm (K0.of P)))).val := by
  let := finite_singleRed hP Λ β
  obtain ⟨p, ⟨hp, hp'⟩, _⟩ := existsUnique_eulerPolynomial hP Λ RD highest hΛ hR β (K0.of P) (K0.of Q')
  rw [K0.homForm_of] at hp
  rw [← toLaurentSeries_injective (hp.trans (GProj.toLaurentSeries_homGdimPoly dst P Q').symm)]
  exact hp'

end Stendhal.SingleRed
end Categorification
