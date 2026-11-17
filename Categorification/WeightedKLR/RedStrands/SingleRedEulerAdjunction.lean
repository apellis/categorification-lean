/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGradedFrobenius
import Categorification.KLR.CyclotomicIntegralLattice
import Categorification.WeightedKLR.RedStrands.SingleBlackShapovalov

/-!
# Adjoint induction under the integral highest-weight isomorphism

For a single red strand, raw cyclotomic restriction corresponds to the
inverse adjoint of the lowering generator for Webster's form (3.24).
Graded Frobenius reciprocity therefore gives the identical recursion for the
Euler and Shapovalov forms on every edge of the weight decomposition.
See Webster, arXiv:1309.3796v2, Corollary 3.22 and Kang–Kashiwara,
arXiv:1102.4677v4, §6.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot
open KLGamma LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open Categorification.Stendhal.SingleBlack
open scoped TensorProduct
attribute [local instance] KLGamma.qToVAlgebra

local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable {k I : Type*} [Field k] [Finite I] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y) (highest : X)
    (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)

local notation "G" => hP.gradingDatum
local notation "R" => projectiveRootDatum RD
local notation "wt" => dominantWeight Λ RD highest hΛ
local notation "η" => projectiveIntegralEquiv hP Λ RD highest hΛ hR
local notation "eQ" => projectiveHighestWeightEquiv Λ RD highest hΛ hP hR
local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (grade G Λ ν))
local notation "B" => websterForm wt hR

/-- A homogeneous cyclotomic projective class lands in the weight space with
the same content under the integral comparison. -/
theorem projectiveIntegralEquiv_lof_mem_weightSpace (β : Multiset I) (x : K0 (grade G Λ β)) :
    (η (ι β x)).val ∈ weightSpace R v _ (RD.pair.flip (highest - (β.map RD.iX).sum)) := by
  intro y
  rw [projectiveIntegralEquiv_val]
  change K R v y • eQ ((1 : L) ⊗ₜ[LP] ι β x) =
    v ^ (RD.pair y (highest - (β.map RD.iX).sum)) • eQ ((1 : L) ⊗ₜ[LP] ι β x)
  rw [← projectiveHighestWeightEquiv_action Λ RD highest hΛ hP hR (K R v y),
    projectiveRepresentationX_K]
  change eQ ((1 : L) ⊗ₜ[LP] toral G Λ RD highest (-y) (ι β x)) = _
  rw [toral_lof, TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul L]
  change eQ (qToV (LaurentPolynomial.T _) • _) = _
  rw [map_smul, parameter_eval_T]
  congr 1
  simp [projectiveParameter]

private theorem projectiveIntegralEquiv_T (n : ℤ) (x : projectiveK0 G Λ) :
    (η ((LaurentPolynomial.T n : LP) • x)).val = v ^ (-n) • (η x).val := by
  rw [projectiveIntegralEquiv_val, projectiveIntegralEquiv_val, TensorProduct.tmul_smul,
    ← IsScalarTower.algebraMap_smul L]
  change eQ (qToV (LaurentPolynomial.T n) • _) = _
  rw [map_smul, parameter_eval_T]
  simp [projectiveParameter]
  rfl

variable (i : I) (β : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "res" => resK0 G Λ i β hP.klrSymm hP.polyInY_leading

/-- Under reciprocal grading shifts the *unshifted* restriction corresponds
to `ρ(Fᵢ) = qᵢ K̃ᵢ⁻¹ Eᵢ`, the inverse adjoint of `Fᵢ` in (3.24). -/
theorem projectiveIntegralEquiv_resK0 (x : K0 (grade G Λ (Si + β))) :
    (η (ι β (res x))).val = rho R v (F R v i) • (η (ι (Si + β) x)).val := by
  have he := projectiveIntegralEquiv_raise hP Λ RD highest hΛ hR i (ι (Si + β) x)
  rw [raise_lof, raiseK0, LinearMap.smul_apply, map_smul, projectiveIntegralEquiv_T] at he
  have hw := projectiveIntegralEquiv_lof_mem_weightSpace hP Λ RD highest hΛ hR β (res x)
  rw [rho_F, rhoF, smul_assoc, mul_smul, ← he, smul_comm (K R v (-ktilde R i)),
    K_neg_ktilde_smul_of_mem_weightSpace hw i, smul_smul, smul_smul]
  suffices h : v ^ C.toLusztig.d i * (v ^ (-raiseShift Λ i β C) *
      (v ^ C.toLusztig.d i) ^ (-(RD.pair (RD.iY i) (highest - (β.map RD.iX).sum)))) = 1 by
    rw [mul_assoc]
    change _ = (v ^ C.toLusztig.d i * (v ^ (-raiseShift Λ i β C) *
      (v ^ C.toLusztig.d i) ^ (-(RD.pair (RD.iY i) (highest - (β.map RD.iX).sum))))) • _
    rw [h, one_smul]
  have hd : ((C.toLusztig.d i : ℕ) : ℤ) = di C i := Int.toNat_of_nonneg (di_pos C i).le
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ RatFunc.X_ne_zero,
    ← zpow_add₀ RatFunc.X_ne_zero, hd, pair_sub_content Λ i β RD highest (hΛ i)]
  simp only [raiseShift]
  convert zpow_zero v using 2
  ring

/-- The one-factor Shapovalov form has the same induction–restriction
recursion as graded Hom, at every cyclotomic weight. -/
theorem websterForm_ind_res (x : K0 (grade G Λ β)) (y : K0 (grade G Λ (Si + β))) :
    B (η (ι (Si + β) y)).val (η (ι (Si + β) (indK0 G Λ i β x))).val =
      B (η (ι β (res y))).val (η (ι β x)).val := by
  rw [← lower_lof, projectiveIntegralEquiv_lower, projectiveIntegralEquiv_resK0,
    websterForm_adjoint, rho_rho, barHom_F]

end Categorification.KLR.CycKLR
