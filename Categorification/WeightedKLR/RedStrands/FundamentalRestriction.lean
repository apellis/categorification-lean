/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorFormFundamental
import Categorification.WeightedKLR.RedStrands.VacuumRestrictionClass

/-!
# Restriction at the fundamental first lowering weight

For Webster, arXiv:1309.3796v2, §4.6 following Theorem 4.31 and §4.7,
Theorem 4.38, the raising action from the first lowering weight to the
highest weight of the type A₁ fundamental tensor square is realized by
restriction with the vacuum grading shift.
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
local notation "E₁" => E sl2RootDatum q ()
local notation "𝒞" => QuantumGroup.CartanDatum.ofGraph (⊥ : SimpleGraph Unit)
local notation "T" => TensorProductAlgebra ℚ FundamentalCorner.Q fundamentalLabels
  (Singleton.singleton () : Multiset Unit)
local notation "ι" => LaurentPolynomial.invert (R := ℤ)

private theorem q_spec : IsRouquierQ 𝒞 FundamentalCorner.Q where
  symm _ _ h := (h (Subsingleton.elim _ _)).elim
  homogeneous _ _ h := (h (Subsingleton.elim _ _)).elim
  unit_coeff _ _ h := (h (Subsingleton.elim _ _)).elim

private abbrev prefixProj (r : Fin 2) :=
  sequenceProj fundamentalGrading (boundaryAt () 2 r).1 (boundaryAt () 2 r).2.1

/-- The right-black restriction of a fundamental prefix projective to the vacuum. -/
def fundamentalPrefixRestriction (r : Fin 2) :=
  blackResVacuumProj (i := ()) fundamentalGrading 𝒞 q_spec (prefixProj r)

private theorem E_firstPrefix :
    TensorModule.act sl2RootDatum q L L E₁ (binaryEquiv (pVector twoFundamental () 0)) =
      highestPair := by
  rw [binaryEquiv_pVector_first]
  simp only [TensorModule.act, AlgHom.comp_apply, comul_E, map_add, LinearMap.add_apply,
    TensorModule.act_tmul, one_smul, E_first, IrreducibleModule.E_smul_hwv, tmul_zero, add_zero,
    highestPair]

private theorem E_prefix (a : Fin 2) :
    TensorModule.act sl2RootDatum q L L E₁ (binaryEquiv (pVector twoFundamental () a)) =
      (if a = 0 then 1 else q⁻¹ + q) • highestPair := by
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl
  · simpa using E_firstPrefix
  · simpa [binaryEquiv_pVector_last] using E_loweredPair

private abbrev terminalWord := (boundaryAt () 2 1).1

private theorem appendBlack_one_eq_terminal :
    appendBlack FundamentalCorner.Q fundamentalLabels () 0 1 =
      TensorProductAlgebra.mk FundamentalCorner.Q fundamentalLabels {()}
        (StendhalAlgebra.e terminalWord (boundaryAt () 2 1).2.1) := by
  rw [← vacuumSeq_mk_e FundamentalCorner.Q fundamentalLabels, appendBlack_mk_e]
  have h : appendBlackLoading () (0 : Multiset Unit) (vacuumSeq (ℓ := 2)) =
      terminalWord := by
    apply Subtype.ext
    funext j
    revert j
    decide +kernel
  apply congrArg (TensorProductAlgebra.mk FundamentalCorner.Q fundamentalLabels {()})
  apply KLR.Corner.ext
  exact congrArg StendhalAlgebraAllOrders.e h

private theorem restriction_poly (a : Fin 2) :
    tensorProductVacuumK0Equiv fundamentalGrading (K0.of (fundamentalPrefixRestriction a)) =
      if a = 0 then LaurentPolynomial.T 1 else 1 + LaurentPolynomial.T 2 := by
  refine (tensorProductVacuumK0Equiv_blackResVacuumProj_eq_homGdimPoly
    fundamentalGrading () 𝒞 q_spec (prefixProj a)).trans ?_
  have h (x y : T)
      (hxy : x = y) (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
      (hx₀ : x ∈ tensorProductGrade fundamentalGrading {()} 0)
      (hy₀ : y ∈ tensorProductGrade fundamentalGrading {()} 0) :
      gdimPoly (homGrade T (GProj.ofIdempotent x hx hx₀).grading (prefixProj a).grading) =
        gdimPoly (homGrade T (GProj.ofIdempotent y hy hy₀).grading (prefixProj a).grading) := by
    cases hxy
    rfl
  have hIdem : IsIdempotentElem (appendBlack FundamentalCorner.Q fundamentalLabels () 0 1 : T) := by
    exact IsIdempotentElem.map (show IsIdempotentElem (1 : TensorProductAlgebra ℚ FundamentalCorner.Q
      fundamentalLabels (0 : Multiset Unit)) from IsIdempotentElem.one)
      (appendBlack FundamentalCorner.Q fundamentalLabels () 0)
  refine (h _ _ appendBlack_one_eq_terminal hIdem
    (isIdempotentElem_mk_e terminalWord (boundaryAt () 2 1).2.1)
    (appendBlack_mem_grade FundamentalCorner.Q fundamentalLabels () 0 fundamentalGrading SetLike.GradedOne.one_mem)
    (mk_e_mem_tensorProductGrade fundamentalGrading {()} terminalWord (boundaryAt () 2 1).2.1)).trans ?_
  have hpoly := FundamentalCorner.boundaryAt_homGdimPoly 1 a
  change gdimPoly (homGrade T (prefixProj 1).grading (prefixProj a).grading) = _ at hpoly
  change gdimPoly (homGrade T (prefixProj 1).grading (prefixProj a).grading) = _
  have ha : a = 0 ∨ a = 1 := by omega
  rcases ha with rfl | rfl <;> simpa using hpoly

private theorem shift_eval (a : Fin 2)
    (h : tensorProductVacuumK0Equiv fundamentalGrading (K0.of (fundamentalPrefixRestriction a)) =
      if a = 0 then LaurentPolynomial.T 1 else 1 + LaurentPolynomial.T 2) :
    integralLaurentEval (ι (tensorProductVacuumK0Equiv fundamentalGrading
      (K0.of ((fundamentalPrefixRestriction a).shift (-1))))) = if a = 0 then 1 else q⁻¹ + q := by
  rw [← K0.T_smul_of, map_smul, smul_eq_mul, h]
  split_ifs
  · rw [← LaurentPolynomial.T_add]
    simp
  · rw [mul_add, mul_one, ← LaurentPolynomial.T_add]
    simp [integralLaurentEval_T, add_comm]

/-- In the first lowering weight of two fundamental type A₁ factors,
the right-black restriction shifted by `1 - 2` induces Webster's raising
operator on the two prefix classes after inverting the grading parameter
(arXiv:1309.3796v2, Definition 3.15, §4.6 following Theorem 4.31, and
§4.7, Theorem 4.38). -/
theorem fundamental_restriction_eq_E (a : Fin 2) :
    integralLaurentEval (ι (tensorProductVacuumK0Equiv fundamentalGrading
      (K0.of ((fundamentalPrefixRestriction a).shift (-1))))) • highestPair =
      TensorModule.act sl2RootDatum q L L E₁ (binaryEquiv (pVector twoFundamental () a)) := by
  rw [shift_eval a (restriction_poly a), E_prefix]

end Categorification.Stendhal.TensorPairing
