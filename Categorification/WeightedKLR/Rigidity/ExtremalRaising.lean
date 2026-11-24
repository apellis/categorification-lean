/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LieLean.Algebra.QuantumGroup.HighestWeightMaps
import Categorification.WeightedKLR.Rigidity.ExtremalWeightRank

/-!
# Missing raising weights at a positive Weyl step

For the saturation argument in Webster, arXiv:1309.3796v2, Proposition 7.2,
a Weyl translate of the highest weight has no weight one outgoing simple root
above it. This transfers the lower-cone obstruction to the quantum irreducible.
-/

noncomputable section
open Module
namespace Categorification.Stendhal
open Matrix.Realization.KacMoodyAlgebra
variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K]
  [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (P : Matrix.Realization A K H) (hA : A.IsGeneralizedCartan)

/-- Conjugating the raising root back to the dominant chamber gives a nonzero
positive root above the highest weight. -/
theorem classical_weightSpace_raise_extremal_eq_bot (highest : Dual K H) (hdom : P.IsDominantIntegral highest)
    (g : P.weylGroup hA) (i : I) (hi : ¬(P.coxeterSystem hA).IsLeftDescent g i) :
    weightSpace P (IrreducibleModule P highest) (g.val highest + P.root i) = ⊥ := by
  have hnd : ¬(P.coxeterSystem hA).IsRightDescent g⁻¹ i :=
    fun h => hi ((P.coxeterSystem hA).isRightDescent_inv_iff.mp h)
  obtain ⟨a, ha, he⟩ := (P.not_isRightDescent_coxeterSystem_iff hA).mp hnd
  have hI := (IrreducibleModule.isIntegrable_iff P hA).mpr hdom
  rw [← weightSpace_weylGroup_eq_bot_iff hA hI (g⁻¹).property]
  rw [map_add, he]
  change weightSpace P (IrreducibleModule P highest) (g.val.symm (g.val highest) + P.rootOf a) = ⊥
  rw [LinearEquiv.symm_apply_apply]
  by_contra hn
  obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨b, hb, hab⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P highest _
    (LieSubmodule.Quotient.surjective_mk' _) hx hn
  have h : P.rootOf a = -P.rootOf b := by linear_combination (norm := abel) hab
  have hz := P.eq_zero_of_mem_closure_of_neg_mem
    ((P.mem_closure_range_root_iff).mpr ⟨a, ha, rfl⟩)
    ((P.mem_closure_range_root_iff).mpr ⟨b, hb, by rw [h, neg_neg]⟩)
  rw [← he, LinearEquiv.map_eq_zero_iff] at hz
  exact P.linearIndependent_root.ne_zero i hz

section Quantum
open LieLean
variable {Y : Type*} [AddCommGroup Y] {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
  (P' : Matrix.Realization Δ.cartanMatrix K H) [FiniteDimensional K H] (hR : R.IsXRegular)
local notation "v" => (RatFunc.X : RatFunc ℚ)
local notation "hCartan" => Δ.isGeneralizedCartan_cartanMatrix
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

include hR in
/-- In an actual extremal weight, a positive Weyl step annihilates the whole source
weight space under the raising generator. -/
theorem quantum_weightSpace_raise_extremal_eq_bot (L : Y →+ ℤ) (highest : Dual K H)
    (hdom : P'.IsDominantIntegral highest)
    (hmatch : ∀ i, highest (P'.coroot i) = (L (R.coroot i) : K))
    (g : P'.weylGroup hCartan) (β : I →₀ ℕ)
    (hβ : highest - P'.rootOf (fun j => (β j : ℤ)) = g.val highest)
    (i : I) (hi : ¬(P'.coxeterSystem hCartan).IsLeftDescent g i) :
    LieLean.QuantumGroup.weightSpace R v (LieLean.QuantumGroup.IrreducibleModule R v L)
      (L - R.rootSum β + R.root i) = ⊥ := by
  have hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1 :=
    fun _ hn => LusztigF.pow_ne_one_of_transcendental LusztigF.transcendental_ratFunc_X hn
  by_cases he : ∃ ν, L - R.rootSum β + R.root i = L - R.rootSum ν
  · obtain ⟨ν, he⟩ := he
    have hsum : R.rootSum β = R.rootSum (ν + Finsupp.single i 1) := by
      rw [R.rootSum_add, R.rootSum_single, one_smul]
      linear_combination (norm := abel) -he
    have hb : β = ν + Finsupp.single i 1 := by
      by_contra hne
      obtain ⟨y, hy⟩ := R.exists_rootSum_ne hR hne
      exact hy (by rw [hsum])
    have hc : P'.rootOf (fun j => (β j : ℤ)) =
        P'.rootOf (fun j => (ν j : ℤ)) + P'.root i := by
      rw [hb, ← P'.rootOf_single i, ← map_add]
      congr 1
      funext j
      by_cases h : i = j
      · subst j; simp
      · simp [Ne.symm h]
    have hξ : highest - P'.rootOf (fun j => (ν j : ℤ)) = g.val highest + P'.root i := by
      rw [← hβ, hc]
      abel
    have hnonneg (j : I) : 0 ≤ L (R.coroot j) := by
      obtain ⟨n, hn⟩ := hdom j
      have e := (hmatch j).symm.trans hn
      exact_mod_cast (e.ge.trans' (Nat.cast_nonneg n))
    let := LieLean.QuantumGroup.IrreducibleModule.finiteDimensional_weightSpace
      (Λ := L) hR hv (L - R.rootSum ν)
    rw [he, ← Submodule.finrank_eq_zero,
      LieLean.QuantumGroup.IrreducibleModule.finrank_weightSpace_eq_ratFunc hR hnonneg P' hmatch]
    change finrank K (weightSpace P' (IrreducibleModule P' highest)
      (highest - P'.rootOf (fun j => (ν j : ℤ)))) = 0
    rw [hξ, classical_weightSpace_raise_extremal_eq_bot P' hCartan highest hdom g i hi, finrank_bot]
  · push Not at he
    have hle := LieLean.QuantumGroup.weightSpace_quotient_le_map hv
      LieLean.QuantumGroup.VermaModule.iSup_weightSpace_eq_top
      (LieLean.QuantumGroup.VermaModule.maxSubmodule R v L) (L - R.rootSum β + R.root i)
    rw [LieLean.QuantumGroup.VermaModule.weightSpace_eq_bot hv he, Submodule.map_bot] at hle
    exact le_bot_iff.mp hle

end Quantum

end Categorification.Stendhal
