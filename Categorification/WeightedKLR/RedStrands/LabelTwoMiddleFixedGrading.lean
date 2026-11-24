/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleGradedAugmentation
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleTensorDifferentials

/-!
# The grading of the actual fixed label-two middle quotient

In the middle loading's fixed subspace of the diagrammatic dot-sum
quotient, the scalar and epsilon coordinates have degrees zero and two.
This supplies the internal grading for the two separated-factor
coordinates in Webster, arXiv:1309.3796v2, §8.2.
-/

noncomputable section

set_option maxRecDepth 2048

namespace Categorification.Stendhal.LabelTwo

open KLR Categorification.Graded Categorification.Webster.LabelTwo DirectSum
open scoped DualNumber

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable (k : Type) [Field k]

local notation "ν" => (({()} : Multiset Unit) + {()})
local notation "A" => TensorProductAlgebra k (parameter k) weights ν
local notation "S" => Standard k
local notation "g" => leftStandardUnit (parameter k) weights loading loading_ordered
local notation "E" => seqIdem (parameter k) weights loading loading_ordered
local notation "ℳ" => middleStandardGrade k (labelTwoGradingDatum k)
local notation "𝒬" => middleDotSumQuotientGrade k
local notation "Q" => StandardDotSumQuotient k
local notation "W" => fixSub k Q E

private theorem middleToFixed_one_value : (middleToFixed k (1 : Middle k)).val = g := by
  change (middleEndomorphismEquiv k ((middlePolynomialEquiv k).symm (1 : Middle k))) g = g
  rw [map_one (middlePolynomialEquiv k).symm]
  exact DFunLike.congr_fun (map_one (middleEndomorphismEquiv k)) g

private theorem middleToFixed_y₁_value : (middleToFixed k (y₁ : Middle k)).val = dotEnd k 0 g := by
  have h : (middlePolynomialEquiv k).symm (y₁ : Middle k) = squareQuotientVariable k 0 :=
    (middlePolynomialEquiv k).symm_apply_eq.mpr (middlePolynomialEquiv_variable_zero k).symm
  change (middleEndomorphismEquiv k ((middlePolynomialEquiv k).symm (y₁ : Middle k))) g = _
  rw [h]
  exact DFunLike.congr_fun (middleDotQuotientAction_X k 0) g

private theorem fixedQuotientMap_eq_of_specialize (a : Middle k) (b : DualNumber k)
    (hb : specialize a = b) :
    fixedQuotientMap k (middleToFixed k a) = (middleCutDotSumEquiv k).symm b := by
  let e := middleCutDotSumEquiv k
  have left : e (fixedQuotientMap k (middleToFixed k a)) = b :=
    (middleCutDotSumEquiv_specialize k a).trans hb
  have right : e (e.symm b) = b := e.apply_symm_apply b
  exact e.injective (left.trans right.symm)

private theorem fixedQuotientMap_mem_grade (z : fixSub k S E) (d : ℤ)
    (hz : z.val ∈ ℳ d) : (fixedQuotientMap k z).val ∈ 𝒬 d := by
  change (LinearMap.range (diagramPlus k)).mkQ z.val ∈ 𝒬 d
  exact preservesGrading_mkQ ℳ (LinearMap.range (diagramPlus k)) hz

/-- The scalar coordinate at the actual fixed middle quotient is in internal degree zero. -/
theorem middleCutDotSum_scalar_mem_grade :
    ((middleCutDotSumEquiv k).symm (1 : DualNumber k)).val ∈ 𝒬 0 := by
  have hvalue : specialize (1 : Middle k) = (1 : DualNumber k) := map_one specialize
  have h := fixedQuotientMap_eq_of_specialize k 1 1 hvalue
  have hz : (middleToFixed k (1 : Middle k)).val ∈ ℳ 0 := by
    rw [middleToFixed_one_value]
    exact middleStandardGenerator_mem_grade k
  exact h ▸ fixedQuotientMap_mem_grade k _ 0 hz

/-- The epsilon coordinate at the actual fixed middle quotient is in internal degree two. -/
theorem middleCutDotSum_epsilon_mem_grade :
    ((middleCutDotSumEquiv k).symm ε).val ∈ 𝒬 2 := by
  have h := fixedQuotientMap_eq_of_specialize k y₁ ε specialize_y₁
  have hz : (middleToFixed k (y₁ : Middle k)).val ∈ ℳ 2 := by
    rw [middleToFixed_y₁_value]
    have hdot : dotEnd k 0 g ∈ ℳ ((0 : ℤ) + 2) :=
      dotEnd_degree_two k 0 (middleStandardGenerator_mem_grade k)
    exact (zero_add (2 : ℤ)) ▸ hdot
  exact h ▸ fixedQuotientMap_mem_grade k _ 2 hz

private theorem dualNumber_split (x : DualNumber k) :
    x = x.fst • (1 : DualNumber k) + x.snd • ε := by
  apply TrivSqZeroExt.ext
  · change x.fst = x.fst * 1 + x.snd * 0
    rw [mul_one, mul_zero, add_zero]
  · change x.snd = x.fst * 0 + x.snd * 1
    rw [mul_zero, mul_one, zero_add]

private theorem inverseBasis_ne_zero {V : Type*} [AddCommGroup V] [Module k V]
    {U : Submodule k V} (e : U ≃ₗ[k] DualNumber k) {b : DualNumber k} (hb : b ≠ 0) :
    (e.symm b).val ≠ 0 := by
  intro h
  apply hb
  calc
    b = e (e.symm b) := (e.apply_symm_apply b).symm
    _ = e 0 := congrArg e (Subtype.ext h)
    _ = 0 := map_zero e

private theorem fixedDualNumber_mem_grade_iff {V : Type*} [AddCommGroup V] [Module k V]
    {U : Submodule k V} {D : ℤ → Submodule k V} [Decomposition D]
    (e : U ≃ₗ[k] DualNumber k) (h₀ : (e.symm 1).val ∈ D 0) (h₂ : (e.symm ε).val ∈ D 2)
    (z : U) (d : ℤ) :
    z.val ∈ D d ↔ (d ≠ 0 → (e z).fst = 0) ∧ (d ≠ 2 → (e z).snd = 0) := by
  let b₀ := (e.symm (1 : DualNumber k)).val
  let b₂ := (e.symm ε).val
  let c₀ := (e z).fst
  let c₂ := (e z).snd
  have hsplit : z.val = c₀ • b₀ + c₂ • b₂ := by
    have h := congrArg e.symm (dualNumber_split k (e z))
    rw [LinearEquiv.symm_apply_apply, map_add, map_smul, map_smul] at h
    exact congrArg Subtype.val h
  have hb₀ : c₀ • b₀ ∈ D 0 := (D 0).smul_mem _ h₀
  have hb₂ : c₂ • b₂ ∈ D 2 := (D 2).smul_mem _ h₂
  constructor
  · intro hz
    constructor
    · intro h
      have hp := congrArg (fun x : V => (decompose D x 0).val) hsplit
      rw [decompose_of_mem_ne D hz h, decompose_add, DirectSum.add_apply,
        Submodule.coe_add, decompose_of_mem_same D hb₀,
        decompose_of_mem_ne D hb₂ (by decide)] at hp
      have hz₀ : 0 = c₀ • b₀ := by simpa using hp
      exact (smul_eq_zero.mp hz₀.symm).resolve_right (inverseBasis_ne_zero k e one_ne_zero)
    · intro h
      have hp := congrArg (fun x : V => (decompose D x 2).val) hsplit
      rw [decompose_of_mem_ne D hz h, decompose_add, DirectSum.add_apply,
        Submodule.coe_add, decompose_of_mem_ne D hb₀ (by decide),
        decompose_of_mem_same D hb₂] at hp
      have hz₂ : 0 = c₂ • b₂ := by simpa using hp
      have hε : (ε : DualNumber k) ≠ 0 := fun he =>
        one_ne_zero (congrArg TrivSqZeroExt.snd he)
      exact (smul_eq_zero.mp hz₂.symm).resolve_right (inverseBasis_ne_zero k e hε)
  · rintro ⟨hd₀, hd₂⟩
    rw [hsplit]
    apply (D d).add_mem
    · by_cases hd : d = 0
      · exact hd.symm ▸ hb₀
      · rw [show c₀ = 0 from hd₀ hd, zero_smul]
        exact zero_mem _
    · by_cases hd : d = 2
      · exact hd.symm ▸ hb₂
      · rw [show c₂ = 0 from hd₂ hd, zero_smul]
        exact zero_mem _

/-- Every homogeneous actual middle quotient vector has only the coordinates
allowed by its internal degree. -/
theorem middleCutDotSum_mem_grade_iff (z : W) (d : ℤ) :
    z.val ∈ 𝒬 d ↔ (d ≠ 0 → (middleCutDotSumEquiv k z).fst = 0) ∧
      (d ≠ 2 → (middleCutDotSumEquiv k z).snd = 0) := by
  let : Decomposition 𝒬 := (middleDotSumQuotientGFin k).decomposition
  exact fixedDualNumber_mem_grade_iff (D := 𝒬) k (middleCutDotSumEquiv k)
    (middleCutDotSum_scalar_mem_grade k) (middleCutDotSum_epsilon_mem_grade k) z d

end Categorification.Stendhal.LabelTwo
