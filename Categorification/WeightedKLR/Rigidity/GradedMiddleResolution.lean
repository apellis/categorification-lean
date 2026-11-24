/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalMiddleResolution
import Categorification.WeightedKLR.Rigidity.GradedMiddleProjectives

/-!
# The internal degrees of the middle projective resolution

For the fundamental weights of type A₁ over ℚ, the resolution of the
middle coevaluation coefficient of Webster, arXiv:1309.3796v2, §7.1,
Lemma 7.3 and Definition 7.4 is exact in every internal degree. The two
crossings have diagram degree one, so in weight n the three projectives
are the n−2, n−1 and n homogeneous pieces of the middle, terminal and
middle loading right ideals.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open KLR StendhalAlgebraAllOrders DirectSum
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "𝒜" => tensorProductGrade grading ({()} : Multiset Unit)
local notation "p" => terminalIdem
local notation "q" => middleIdem
local notation "C" => project (ψ 1)

private theorem homogeneous_crossing_preimage {f c y : T} {j n : ℤ}
    (hf : f ∈ 𝒜 0) (hc : c ∈ 𝒜 1) (hy : y ∈ 𝒜 n) (hj : 1 + j = n)
    (x : rIdeal f) (hxy : c * x.val = y) :
    ∃ z : rIdeal f, z.val ∈ 𝒜 j ∧ c * z.val = y := by
  let z := decompose 𝒜 x.val j
  have hz : f * (z : T) = z := by
    exact (coe_decompose_mul_of_left_mem_zero 𝒜 hf).symm.trans
      (congrArg (fun a : T => (decompose 𝒜 a j : T)) x.property)
  refine ⟨⟨z.val, hz⟩, z.property, ?_⟩
  calc c * z.val = (decompose 𝒜 (c * x.val) (1 + j) : T) :=
         (coe_decompose_mul_add_of_left_mem 𝒜 hc).symm
       _ = y := by rw [hj, hxy, decompose_of_mem_same 𝒜 hy]

/-- Both mixed resolution differentials preserve the shifted internal degrees. -/
theorem middleResolution_maps_degree (n : ℤ) :
    (∀ x : rIdeal q, x.val ∈ 𝒜 (n-2) → (fundamentalResolutionMap x).val ∈ 𝒜 (n-1)) ∧
    (∀ x : rIdeal p, x.val ∈ 𝒜 (n-1) → (terminalToMiddle x).val ∈ 𝒜 n) := by
  obtain ⟨_, _, hu, hv⟩ := fundamental_loading_crossing_degrees
  constructor
  · intro x hx
    change C * q * x.val ∈ _
    simpa only [show 1 + (n-2) = n-1 by omega] using SetLike.GradedMul.mul_mem hu hx
  · intro x hx
    change C * p * x.val ∈ _
    simpa only [show 1 + (n-1) = n by omega] using SetLike.GradedMul.mul_mem hv hx

/-- Exactness of the middle resolution at the terminal projective in each internal degree. -/
theorem middleResolution_exact_terminal (n : ℤ) (x : rIdeal p) (hx : x.val ∈ 𝒜 (n-1)) :
    terminalToMiddle x = 0 ↔ ∃ y : rIdeal q, y.val ∈ 𝒜 (n-2) ∧ fundamentalResolutionMap y = x := by
  obtain ⟨hq, _, hu, _⟩ := fundamental_loading_crossing_degrees
  have ex := middleProjectiveResolution.2.2.2.1 x
  constructor
  · intro h
    obtain ⟨y, hy⟩ := ex.mp h
    obtain ⟨z, hz, he⟩ := homogeneous_crossing_preimage hq hu hx
      (show 1 + (n-2) = n-1 by omega) y (congrArg Subtype.val hy)
    exact ⟨z, hz, Subtype.ext he⟩
  · rintro ⟨y, _, hy⟩
    exact ex.mpr ⟨y, hy⟩

/-- Exactness at the middle projective in each internal degree, using the scalar
character that presents the simple quotient. -/
theorem middleResolution_exact_middle (n : ℤ) (x : rIdeal q) (hx : x.val ∈ 𝒜 n) :
    middleCharacter x.val = 0 ↔ ∃ y : rIdeal p, y.val ∈ 𝒜 (n-1) ∧ terminalToMiddle y = x := by
  obtain ⟨_, hp, _, hv⟩ := fundamental_loading_crossing_degrees
  have ex : middleCharacter x.val = 0 ↔ x ∈ LinearMap.range terminalToMiddle := by
    rw [terminalToMiddle_range, mem_middleCutTrace_iff]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := ex.mp h
    obtain ⟨z, hz, he⟩ := homogeneous_crossing_preimage hp hv hx
      (show 1 + (n-1) = n by omega) y (congrArg Subtype.val hy)
    exact ⟨z, hz, Subtype.ext he⟩
  · rintro ⟨y, _, hy⟩
    exact ex.mpr ⟨y, hy⟩

/-- The augmentation hits every homogeneous scalar in its degree. -/
theorem middleResolution_augmentation_surjective (n : ℤ) (z : ℚ) (hz : n = 0 ∨ z = 0) :
    ∃ x : rIdeal q, x.val ∈ 𝒜 n ∧ middleCharacter x.val = z := by
  rcases hz with rfl | rfl
  · have hq : IsIdempotentElem q :=
      IsIdempotentElem.map (by simp [IsIdempotentElem, e_mul_e]) project
    refine ⟨z • (⟨q, hq.eq⟩ : rIdeal q), (𝒜 0).smul_mem _ fundamental_loading_crossing_degrees.1, ?_⟩
    change middleCharacter (z • q) = z
    rw [map_smul, middleCharacter_middleIdem, smul_eq_mul, mul_one]
  · exact ⟨0, (𝒜 n).zero_mem, map_zero _⟩

end Categorification.Stendhal.FundamentalCorner
