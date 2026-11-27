/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.ExtremalRaising
import Categorification.WeightedKLR.Rigidity.ExtremalBlockRank
import Categorification.WeightedKLR.Rigidity.RigidityExtRankOne

/-!
# Missing lowering weights below an extremal weight

Input for Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3. If the simple reflection `s_i` is a left
descent of `g` in the Weyl group, then `g λ - α_i` is not a weight of the irreducible module of
highest weight `λ`. For the content of a reduced coevaluation word of `g`, the cyclotomic block
with one more black strand of colour `i` therefore has Grothendieck rank zero and vanishes.
For a reduced expression of the longest element this holds for every colour.
-/

noncomputable section
open Module
namespace Categorification.Stendhal
open Matrix.Realization.KacMoodyAlgebra
variable {I K H : Type*} [Fintype I] [DecidableEq I] [Field K]
  [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K] [AddCommGroup H] [Module K H]
  {A : Matrix I I ℤ} (P : Matrix.Realization A K H) (hA : A.IsGeneralizedCartan)

/-- Conjugating the lowering root back to the dominant chamber gives a nonzero positive root
above the highest weight. -/
theorem classical_weightSpace_lower_extremal_eq_bot (highest : Dual K H)
    (hdom : P.IsDominantIntegral highest)
    (g : P.weylGroup hA) (i : I) (hi : (P.coxeterSystem hA).IsLeftDescent g i) :
    weightSpace P (IrreducibleModule P highest) (g.val highest - P.root i) = ⊥ := by
  have hd : (P.coxeterSystem hA).IsRightDescent g⁻¹ i :=
    (P.coxeterSystem hA).isRightDescent_inv_iff.mpr hi
  obtain ⟨a, ha, he⟩ := (P.isRightDescent_coxeterSystem_iff hA).mp hd
  have hI := (IrreducibleModule.isIntegrable_iff P hA).mpr hdom
  rw [← weightSpace_weylGroup_eq_bot_iff hA hI (g⁻¹).property]
  rw [map_sub, he]
  change weightSpace P (IrreducibleModule P highest)
    (g.val.symm (g.val highest) - -P.rootOf a) = ⊥
  rw [LinearEquiv.symm_apply_apply, sub_neg_eq_add]
  by_contra hn
  obtain ⟨x, hx, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨b, hb, hab⟩ := VermaModule.exists_eq_sub_of_mem_weightSpace P highest _
    (LieSubmodule.Quotient.surjective_mk' _) hx hn
  have h : P.rootOf a = -P.rootOf b := by linear_combination (norm := abel) hab
  have hz := P.eq_zero_of_mem_closure_of_neg_mem
    ((P.mem_closure_range_root_iff).mpr ⟨a, ha, rfl⟩)
    ((P.mem_closure_range_root_iff).mpr ⟨b, hb, by rw [h, neg_neg]⟩)
  have h0 : ((g⁻¹ : P.weylGroup hA) : Dual K H ≃ₗ[K] Dual K H) (P.root i) = 0 := by
    rw [he, hz, neg_zero]
  rw [LinearEquiv.map_eq_zero_iff] at h0
  exact P.linearIndependent_root.ne_zero i h0

section Quantum
open LieLean
variable {Y : Type*} [AddCommGroup Y] {Δ : LusztigCartanDatum I} {R : Δ.RootDatum Y}
  (P' : Matrix.Realization Δ.cartanMatrix K H) [FiniteDimensional K H] (hR : R.IsXRegular)
local notation "v" => (RatFunc.X : RatFunc ℚ)
local notation "hCartan" => Δ.isGeneralizedCartan_cartanMatrix
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

include hR in
/-- Below an extremal weight at a left descent, the lowering weight space of the quantum
irreducible vanishes. -/
theorem quantum_weightSpace_lower_extremal_eq_bot (L : Y →+ ℤ) (highest : Dual K H)
    (hdom : P'.IsDominantIntegral highest)
    (hmatch : ∀ i, highest (P'.coroot i) = (L (R.coroot i) : K))
    (g : P'.weylGroup hCartan) (β : I →₀ ℕ)
    (hβ : highest - P'.rootOf (fun j => (β j : ℤ)) = g.val highest)
    (i : I) (hi : (P'.coxeterSystem hCartan).IsLeftDescent g i) :
    LieLean.QuantumGroup.weightSpace R v (LieLean.QuantumGroup.IrreducibleModule R v L)
      (L - R.rootSum (β + Finsupp.single i 1)) = ⊥ := by
  have hv : ∀ n : ℕ, 0 < n → v ^ n ≠ 1 :=
    fun _ hn => LusztigF.pow_ne_one_of_transcendental LusztigF.transcendental_ratFunc_X hn
  have hc : P'.rootOf (fun j => (((β + Finsupp.single i 1 : I →₀ ℕ) j : ℕ) : ℤ)) =
      P'.rootOf (fun j => (β j : ℤ)) + P'.root i := by
    rw [← P'.rootOf_single i, ← map_add]
    congr 1
    funext j
    by_cases h : i = j
    · subst j; simp
    · simp [Ne.symm h]
  have hξ : highest - P'.rootOf (fun j => (((β + Finsupp.single i 1 : I →₀ ℕ) j : ℕ) : ℤ)) =
      g.val highest - P'.root i := by
    rw [← hβ, hc]
    abel
  have hnonneg (j : I) : 0 ≤ L (R.coroot j) := by
    obtain ⟨n, hn⟩ := hdom j
    have e := (hmatch j).symm.trans hn
    exact_mod_cast (e.ge.trans' (Nat.cast_nonneg n))
  let := LieLean.QuantumGroup.IrreducibleModule.finiteDimensional_weightSpace
    (Λ := L) hR hv (L - R.rootSum (β + Finsupp.single i 1))
  rw [← Submodule.finrank_eq_zero,
    LieLean.QuantumGroup.IrreducibleModule.finrank_weightSpace_eq_ratFunc hR hnonneg P' hmatch]
  change finrank K (weightSpace P' (IrreducibleModule P' highest)
    (highest - P'.rootOf (fun j => (((β + Finsupp.single i 1 : I →₀ ℕ) j : ℕ) : ℤ)))) = 0
  rw [hξ, classical_weightSpace_lower_extremal_eq_bot P' hCartan highest hdom g i hi, finrank_bot]

end Quantum

end Categorification.Stendhal

namespace Categorification.KLR.CycKLR

open Categorification.Graded QuantumGroup QuantumGroup.UDot LieLean LieLean.QuantumGroup
open Module
local notation "v" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable {I k : Type*} [Fintype I] [DecidableEq I] [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hR : (projectiveRootDatum RD).IsXRegular)

local notation "G" => hP.gradingDatum
local notation "𝒟" => projectiveRootDatum RD
local notation "λ₀" => RD.pair.flip highest

include hP hΛ hR in
/-- **The block below a coevaluation word vanishes at a left descent.** If `s_i` is a left
descent of the Weyl group element of a reduced coevaluation word `w`, the cyclotomic quotient
with one more black strand of colour `i` is zero (input for Webster, arXiv:1309.3796v3, §7.1,
Lemma 7.3). -/
theorem subsingleton_of_isLeftDescent_coevaluationWord
    {K H : Type*} [Field K] [ConditionallyCompleteLinearOrder K] [IsStrictOrderedRing K]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H]
    (P : Matrix.Realization C.toLusztig.cartanMatrix K H) (weight : P.integralWeights)
    (hweight : P.IsDominantIntegral (weight : Dual K H))
    (match_weight : ∀ i, (weight : Dual K H) (P.coroot i) = (λ₀ ((𝒟).coroot i) : K))
    (w : List I) (hw : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsReduced w.reverse)
    (i : I) (hi : (P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).IsLeftDescent
      ((P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd w.reverse) i) :
    Subsingleton (CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ j)
      ({i} + (Stendhal.coevaluationWord
        (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w : Multiset I))) := by
  let β : Multiset I := Stendhal.coevaluationWord
    (P.cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix) weight w
  let := module_finite (Q := Q) (ν := {i} + β) (fun i j hij => by
    obtain ⟨c, hc, h⟩ := hP.polyInY_leading i j hij
    rw [h]
    exact hc.map Polynomial.C) (fun i => Polynomial.monic_X_pow (R := k) (Λ i))
  let := HasGdim.of_finiteDimensional (grade G Λ ({i} + β))
  apply GProj.subsingleton_of_finrank_K0_eq_zero (𝒜 := grade G Λ ({i} + β))
  rw [finrank_projectiveBlock_eq_weightSpace hP Λ RD highest hΛ hR]
  have hδ := Stendhal.rootSum_coevaluationWord_of_reduced P
    C.toLusztig.isGeneralizedCartan_cartanMatrix weight hweight w hw
  rw [P.coe_rootSum_cartanDatum C.toLusztig.isGeneralizedCartan_cartanMatrix] at hδ
  have hβ : (weight : Dual K H) - P.rootOf (fun j => ((β.toFinsupp j : ℕ) : ℤ)) =
      ((P.coxeterSystem C.toLusztig.isGeneralizedCartan_cartanMatrix).wordProd w.reverse).1
        (weight : Dual K H) := by
    rw [hδ, sub_sub_cancel]
  have h := Stendhal.quantum_weightSpace_lower_extremal_eq_bot P hR λ₀ (weight : Dual K H)
    hweight match_weight _ β.toFinsupp hβ i hi
  rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, add_comm, h, finrank_bot]

end Categorification.KLR.CycKLR
