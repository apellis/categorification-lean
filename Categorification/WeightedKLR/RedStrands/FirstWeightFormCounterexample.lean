/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorShapovalov
import Categorification.WeightedKLR.RedStrands.TensorAction
import Categorification.WeightedKLR.RedStrands.FirstWeightLattice

/-!
# The diagonal entry at the terminal loading of two fundamental red strands

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36, with the two-factor form
printed above Proposition 4.33. For two type A₁ fundamental weights and
one terminal black strand, the degree `-2` Hom coefficient is zero.
The coefficient of the printed norm at that degree is one.
-/

noncomputable section

namespace Categorification.Stendhal.TensorPairing

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open KLR FirstWeight Categorification.Graded TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
open scoped TensorProduct

local notation "𝕂" => RatFunc ℚ
local notation "q" => (RatFunc.X : 𝕂)
local instance : NeZero q := ⟨RatFunc.X_ne_zero⟩
local notation "L" => IrreducibleModule sl2RootDatum q (Subtype.val fundamental)
local notation "v₀" => IrreducibleModule.hwv sl2RootDatum q (Subtype.val fundamental)
local notation "F₁" => F sl2RootDatum q ()
local notation "Φ" => printedForm sl2XRegular fundamental fundamental

/-- The two fundamental red labels of type A₁. -/
abbrev twoFundamental : Fin 2 → Dom sl2RootDatum := fun _ => fundamental

/-- The binary realization of the ordered pair of tensor factors. -/
def binaryEquiv : TensorSpace twoFundamental ≃ₗ[𝕂] L ⊗[𝕂] L :=
  (tensorSplitLast twoFundamental).trans ((PiTensorProduct.subsingletonEquiv (0 : Fin 1)).rTensor L)

private theorem binaryEquiv_tprod (z : Fin 2 → L) :
    binaryEquiv (PiTensorProduct.tprod 𝕂 z) = z 0 ⊗ₜ[𝕂] z 1 := by
  erw [binaryEquiv, LinearEquiv.trans_apply, tensorSplitLast_tprod,
    LinearEquiv.rTensor_tmul, PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

/-- The repository's prefix-lowering vector for the terminal black strand
identifies with the vector `F(h ⊗ h)` in the binary tensor product. -/
theorem binaryEquiv_pVector_last : binaryEquiv (pVector twoFundamental () 1) = loweredPair := by
  have hset : Finset.Iic (1 : Fin 2) = Finset.univ := by decide
  rw [pVector_eq_sum, hset, Fin.sum_univ_two, tensor_laurent_smul, tensor_laurent_smul,
    map_add, map_smul, map_smul]
  have h₀ : binaryEquiv (loweredPure twoFundamental () 0) = (F₁ • v₀) ⊗ₜ[𝕂] v₀ := by
    erw [loweredPure, binaryEquiv_tprod]
    rfl
  have h₁ : binaryEquiv (loweredPure twoFundamental () 1) = v₀ ⊗ₜ[𝕂] (F₁ • v₀) := by
    erw [loweredPure, binaryEquiv_tprod]
    rfl
  have hc : prefixCoefficient twoFundamental () (1 : Fin 2) 0 = LaurentPolynomial.T (-1) := by
    rw [prefixCoefficient, Fin.prod_univ_two]
    change LaurentPolynomial.T 0 * LaurentPolynomial.T (-1) = _
    simp
  have hc' : prefixCoefficient twoFundamental () (1 : Fin 2) 1 = 1 := by
    rw [prefixCoefficient, Fin.prod_univ_two]
    change LaurentPolynomial.T 0 * LaurentPolynomial.T 0 = _
    simp
  rw [h₀, h₁, hc, hc', integralLaurentEval_T, map_one, one_smul]
  simp only [loweredPair, highestPair, TensorModule.act, AlgHom.comp_apply, comul_F, map_add,
    LinearMap.add_apply, TensorModule.act_tmul, one_smul, sl2RootDatum_ktilde]
  have hk : K sl2RootDatum q (-1) • v₀ = q ^ (-1 : ℤ) • v₀ :=
    IrreducibleModule.hwv_mem_weightSpace _
  rw [hk, tmul_smul (q ^ (-1 : ℤ))]

/-- The integral root multiplicity of each red strand is one. -/
def fundamentalLabels : Fin 2 → Unit →₀ ℕ := fun _ => Finsupp.single () 1

/-- Webster's standard type A₁ grading, with black dots in degree two. -/
def fundamentalGrading :=
  stendhalGradingDatum fundamentalLabels (KLR.klGradingDatum ℚ (⊥ : SimpleGraph Unit)) (fun _ => 1) (fun _ => rfl)

local notation "rrb" => boundaryAt () 2 1
local notation "P" => sequenceProj fundamentalGrading (rrb).1 (rrb).2.1
local notation "T" => TensorProductAlgebra ℚ (KLR.klQ (k := ℚ) (⊥ : SimpleGraph Unit)) fundamentalLabels
  (Singleton.singleton () : Multiset Unit)

private theorem dots_positive (a : Unit ⊕ Fin 2) : 0 < fundamentalGrading.degX a := by
  cases a <;> exact (by decide : (0 : ℤ) < 2)

/-- Counterexample to the printed identification in Webster, arXiv:1309.3796v2,
Lemma 4.36. The characteristic-zero example uses the terminal projective itself
and the prefix-lowering vector of the same loading. -/
theorem terminal_homGdimPoly_ne_printedForm :
    integralLaurentEval (gdimPoly (homGrade T (P).grading (P).grading)) ≠
      Φ (binaryEquiv (pVector twoFundamental () 1)) (binaryEquiv (pVector twoFundamental () 1)) := by
  rw [binaryEquiv_pVector_last, printedForm_loweredPair]
  intro he
  have h := integralLaurentEval_injective (show
      integralLaurentEval (gdimPoly (homGrade T (P).grading (P).grading)) =
        integralLaurentEval (1 + LaurentPolynomial.T (-2)) by
    rwa [map_add, map_one, integralLaurentEval_T])
  have hc := congrArg (fun z : LaurentPolynomial ℤ => z.coeff (-2)) h
  rw [FirstWeight.coeff_endPoly_sequenceProj_eq_zero_of_neg fundamentalGrading dots_positive
    (rrb).1 (rrb).2.1 (by decide)] at hc
  change (0 : ℤ) = ((1 : LaurentPolynomial ℤ) + LaurentPolynomial.T (-2)).coeff (-2) at hc
  rw [← LaurentPolynomial.T_zero] at hc
  simp only [AddMonoidAlgebra.coeff_add, LaurentPolynomial.T, AddMonoidAlgebra.coeff_single] at hc
  norm_num at hc

end Categorification.Stendhal.TensorPairing
