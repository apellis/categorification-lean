/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorFormAdjunction
import Categorification.WeightedKLR.RedStrands.FirstWeightFormCounterexample
import Categorification.WeightedKLR.RedStrands.FundamentalPrefixCorners

/-!
# The corrected form in the fundamental first lowering weight

For Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36, the two projectives in
the first lowering weight of the type A₁ fundamental tensor square give a
test of the repair to the tensor form preceding Proposition 4.33.
-/

noncomputable section

namespace Categorification.Stendhal.TensorPairing

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open KLR FirstWeight Categorification.Graded TensorProduct
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "𝕂" => RatFunc ℚ
local notation "q" => (RatFunc.X : 𝕂)
local instance : NeZero q := ⟨RatFunc.X_ne_zero⟩
local notation "L" => IrreducibleModule sl2RootDatum q (Subtype.val fundamental)
local notation "v₀" => IrreducibleModule.hwv sl2RootDatum q (Subtype.val fundamental)
local notation "F₁" => F sl2RootDatum q ()
local notation "v₁" => F₁ • v₀
local notation "A" => v₁ ⊗ₜ[𝕂] v₀
local notation "B" => v₀ ⊗ₜ[𝕂] v₁
local notation "θ" => websterTheta sl2XRegular fundamental fundamental
local notation "φ" => factorwise sl2XRegular fundamental fundamental
local notation "Ψ" => correctedForm sl2XRegular fundamental fundamental
local notation "ψ" => SingleBlack.websterForm fundamental sl2XRegular
local notation "act₂" => TensorModule.actPair sl2RootDatum q L L

/-- The first prefix vector lowers the first fundamental factor. -/
theorem binaryEquiv_pVector_first :
    binaryEquiv (pVector twoFundamental () 0) = A := by
  have hs : Finset.Iic (0 : Fin 2) = {0} := by decide
  rw [pVector_eq_sum, hs, Finset.sum_singleton, tensor_laurent_smul]
  have hc : prefixCoefficient twoFundamental () (0 : Fin 2) 0 = 1 := by
    rw [prefixCoefficient, Fin.prod_univ_two]
    change LaurentPolynomial.T 0 * LaurentPolynomial.T 0 = _
    simp
  rw [hc, map_one, one_smul, loweredPure]
  erw [binaryEquiv, LinearEquiv.trans_apply, tensorSplitLast_tprod,
    LinearEquiv.rTensor_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

private theorem K_highest (m : ℤ) : K sl2RootDatum q m • v₀ = q ^ m • v₀ :=
  IrreducibleModule.hwv_mem_weightSpace m

private theorem loweredPair_eq : loweredPair = q⁻¹ • A + B := by
  simp only [loweredPair, highestPair, TensorModule.act, AlgHom.comp_apply, comul_F,
    map_add, LinearMap.add_apply, TensorModule.act_tmul, one_smul, sl2RootDatum_ktilde,
    K_highest, zpow_neg_one, tmul_smul]

private theorem theta_loweredPair : θ loweredPair = q • A + B := by
  rw [loweredPair, websterTheta_act, highestPair, websterTheta_append_highest]
  simp only [barComul_F, map_add, LinearMap.add_apply, TensorModule.act_tmul,
    sl2RootDatum_ktilde, K_highest, zpow_one, one_smul, tmul_smul]

private theorem simple_norm : ψ v₁ v₁ = 1 := by
  rw [SingleBlack.websterForm_lowered]
  change (q ^ 1) ^ ((1 : ℤ) - 1) * qIntZ (q ^ 1) 1 = 1
  rw [pow_one, sub_self, zpow_zero, one_mul,
    qIntZ_one (sub_inv_ne_zero_of_pow_ne_one RatFunc.X_ne_zero hvn_ratFunc)]

private theorem lower_highest : ψ v₁ v₀ = 0 := by
  rw [SingleBlack.websterForm_adjoint, rho_F, rhoF, barHom_smul, map_mul, barHom_K, barHom_E,
    smul_assoc, mul_smul, IrreducibleModule.E_smul_hwv, smul_zero, smul_zero]
  simp [SingleBlack.websterForm]

private theorem theta_first :
    θ (binaryEquiv (pVector twoFundamental () 0)) = A := by
  rw [binaryEquiv_pVector_first, websterTheta_append_highest]

private theorem theta_last :
    θ (binaryEquiv (pVector twoFundamental () 1)) = q • A + B := by
  rw [binaryEquiv_pVector_last, theta_loweredPair]

private theorem scaled_pair (c d : 𝕂) (u v x y : L) :
    φ (c • (u ⊗ₜ[𝕂] v)) (d • (x ⊗ₜ[𝕂] y)) =
      RatFunc.bar c * d * ψ u x * ψ v y := by
  calc
    _ = φ ((c • u) ⊗ₜ[𝕂] v) ((d • x) ⊗ₜ[𝕂] y) := by
      simp only [smul_tmul']
    _ = _ := by
      rw [factorwise_tmul, SingleBlack.websterForm_smul_left, SingleBlack.websterForm_smul_right]
      ring

private theorem factorwise_firstWeight (c d e f : 𝕂) :
    φ (c • A + d • B) (e • A + f • B) = RatFunc.bar c * e + RatFunc.bar d * f := by
  have hleft (x y z : L ⊗[𝕂] L) : φ (x + y) z = φ x z + φ y z := by
    simp [factorwise]
  have hright (x y z : L ⊗[𝕂] L) : φ x (y + z) = φ x y + φ x z := by
    simp [factorwise]
  simp only [hleft, hright, scaled_pair, SingleBlack.websterForm_hwv, simple_norm,
    lower_highest, mul_one, mul_zero, zero_mul, add_zero, zero_add]

private theorem firstWeight_coords (a : Fin 2) :
    binaryEquiv (pVector twoFundamental () a) =
      (if a = 0 then 1 else q⁻¹) • A + (if a = 0 then (0 : 𝕂) else 1) • B := by
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl
  · simp [binaryEquiv_pVector_first]
  · simp [binaryEquiv_pVector_last, loweredPair_eq]

private theorem theta_firstWeight_coords (a : Fin 2) :
    θ (binaryEquiv (pVector twoFundamental () a)) =
      (if a = 0 then 1 else q) • A + (if a = 0 then (0 : 𝕂) else 1) • B := by
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl
  · rw [theta_first]
    simp
  · rw [theta_last]
    simp

private theorem pair_eval (a b : Fin 2) :
    Ψ (binaryEquiv (pVector twoFundamental () a)) (binaryEquiv (pVector twoFundamental () b)) =
      if a = b then if a = 0 then 1 else 1 + q ^ 2 else q := by
  rw [correctedForm, theta_firstWeight_coords, firstWeight_coords, factorwise_firstWeight]
  have ha : a = 0 ∨ a = 1 := by omega
  have hb : b = 0 ∨ b = 1 := by omega
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [RatFunc.bar_X, pow_two, add_comm]

local notation "T" => TensorProductAlgebra ℚ FundamentalCorner.Q fundamentalLabels
  (Singleton.singleton () : Multiset Unit)
private abbrev prefixProj (r : Fin 2) :=
  sequenceProj fundamentalGrading (boundaryAt () 2 r).1 (boundaryAt () 2 r).2.1

/-- The first-lowering case of Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36
for two type A₁ fundamental red labels, repaired by using the quasi-R
intertwiner in the second argument. The entries in increasing prefix order are
(1,q,q,1+q²). -/
theorem fundamental_prefix_homGdimPoly_eq_correctedForm (a b : Fin 2) :
    integralLaurentEval (gdimPoly (homGrade T (prefixProj a).grading (prefixProj b).grading)) =
      Ψ (binaryEquiv (pVector twoFundamental () a)) (binaryEquiv (pVector twoFundamental () b)) := by
  have h := FundamentalCorner.boundaryAt_homGdimPoly a b
  change gdimPoly (homGrade T (prefixProj a).grading (prefixProj b).grading) = _ at h
  rw [h, pair_eval]
  split_ifs <;> simp [integralLaurentEval_T]

end Categorification.Stendhal.TensorPairing
