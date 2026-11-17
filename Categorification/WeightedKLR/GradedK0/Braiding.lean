/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.TwistedMultiplication
import Categorification.WeightedKLR.Cartan
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-!
# The weight braiding on the weighted Grothendieck algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, p. 11, preceding Theorem 2.19. The flip on each pair of homogeneous
summands is multiplied by the Laurent monomial for the crossing degree.
These monomials are units even over integral Laurent scalars. The twisted
tensor-square multiplication crosses the middle two factors by this map.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded LaurentPolynomial
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  (G : GradingDatum Γ)

local notation "L" => LaurentPolynomial ℤ
local notation "ι" => DirectSum.lof L _ G.K0fam

private def weightTwist (p : (I →₀ ℕ) × (I →₀ ℕ)) :
    G.K0fam p.1 ⊗[L] G.K0fam p.2 ≃ₗ[L] G.K0fam p.1 ⊗[L] G.K0fam p.2 :=
  (isUnit_T (R := ℤ) (G.crossingDegree p.1 p.2)).unit • LinearEquiv.refl L _

/-- The invertible weight-dependent switch in Webster's §2.4, p. 11. -/
def weightBraiding : G.K0W ⊗[L] G.K0W ≃ₗ[L] G.K0W ⊗[L] G.K0W :=
  let d := TensorProduct.directSum L L G.K0fam G.K0fam
  d ≪≫ₗ DirectSum.congrLinearEquiv (G.weightTwist) ≪≫ₗ d.symm ≪≫ₗ TensorProduct.comm L _ _

/-- Formula for the braiding on homogeneous pure tensors. -/
theorem weightBraiding_tmul (a b : I →₀ ℕ) (x : G.K0fam a) (y : G.K0fam b) :
    G.weightBraiding (ι a x ⊗ₜ ι b y) =
      (T (G.crossingDegree a b) : L) • (ι b y ⊗ₜ ι a x) := by
  simp only [weightBraiding, LinearEquiv.trans_apply, TensorProduct.directSum_lof_tmul_lof,
    DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof, LinearEquiv.coe_coe,
    weightTwist, LinearEquiv.smul_apply, IsUnit.unit_spec, LinearEquiv.refl_apply,
    map_smul, TensorProduct.directSum_symm_lof_tmul, TensorProduct.comm_tmul]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The scalar hexagon for crossing a block past a tensor product. -/
theorem braidingFactor_add_right (a b c : I →₀ ℕ) :
    (T (G.crossingDegree a (b + c)) : L) = T (G.crossingDegree a b) * T (G.crossingDegree a c) := by
  rw [G.crossingDegree_add_right, T_add]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The scalar hexagon for crossing a tensor product past a block. -/
theorem braidingFactor_add_left (a b c : I →₀ ℕ) :
    (T (G.crossingDegree (a + b) c) : L) = T (G.crossingDegree a c) * T (G.crossingDegree b c) := by
  rw [G.crossingDegree_add_left, T_add]

/-- The tensor-square product uses the explicit braiding on the two middle
factors (Webster, §2.4, p. 11 and Theorem 2.19). -/
theorem twMul_eq_map_weightBraiding (x y z w : G.K0W) :
    G.twMul (x ⊗ₜ y) (z ⊗ₜ w) =
      TensorProduct.map (LinearMap.mulLeft L x) (LinearMap.mulRight L w)
        (G.weightBraiding (y ⊗ₜ z)) := by
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' =>
    simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, LinearMap.add_apply,
      hy, hy']
  | of a y =>
    induction z using DirectSum.induction_on with
    | zero => simp
    | add z z' hz hz' =>
      simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add, hz, hz']
    | of b z =>
      have h := G.weightBraiding_tmul a b y z
      simp only [DirectSum.lof_eq_of] at h
      rw [G.twMul_tmul, h, map_smul, TensorProduct.map_tmul]
      rfl

end Categorification.WeightedKLR.GradingDatum

namespace Categorification.WeightedKLR.WeightedGraph.Standing

open Categorification.QuantumGroup

variable {I 𝕜 k : Type*} [DecidableEq I] [CommRing k] {Γ : WeightedGraph I 𝕜 k}

/-- In the standing grading the crossing monomial is indexed by the negative
symmetric Cartan pairing. The Laurent variable here denotes a grading shift
(the inverse of the quantum-group parameter). -/
theorem crossingDegree_eq_neg_wdot (hS : Γ.Standing) (hne : ∀ e, Γ.head e ≠ Γ.tail e)
    (hl : ∀ i, Γ.loop i = none) (a b : I →₀ ℕ) :
    hS.gradingDatum.crossingDegree a b = -wdot hS.cartanDatum.dot a.toMultiset b.toMultiset := by
  have single (i : I) (v : Multiset I) :
      wdot hS.gradingDatum.pairDeg {i} v = -wdot hS.cartanDatum.dot {i} v := by
    induction v using Multiset.induction_on with
    | empty => simp
    | cons j v ih =>
      rw [wdot_cons_right, wdot_cons_right, wdot_singleton, wdot_singleton, ih,
        hS.pairDeg_eq_neg_cartanDatum_dot hne hl, neg_add]
  unfold GradingDatum.crossingDegree
  induction a.toMultiset using Multiset.induction_on with
  | empty => simp
  | cons i u ih => rw [wdot_cons_left, wdot_cons_left, single, ih, neg_add]

end Categorification.WeightedKLR.WeightedGraph.Standing
