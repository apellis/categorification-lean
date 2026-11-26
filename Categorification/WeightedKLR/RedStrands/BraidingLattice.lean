/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorBraiding
import Categorification.KLR.CyclotomicIntegralLattice
import LieLean.Algebra.QuantumGroup.Modified.TensorVermaIntegral

/-!
# The braiding of two factors on the integral lattice, and its limit at `v = 1`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Lemma 6.11. The dimension count in that proof uses that at `q = 1` the braiding of two
highest-weight modules becomes the flip of the tensor factors. This file proves the integral
form of that statement for two factors `V^{λ₁} ⊗ V^{λ₂}` and the integral lattice `L` spanned
over `𝒜 = ℤ[v, v⁻¹]` by the pure tensors `x ⊗ y` with `x ∈ V_ℤ(λ₁)` and `y ∈ V_ℤ(λ₂)`:

* the braiding `σ` maps `L` into the lattice of `V^{λ₂} ⊗ V^{λ₁}`
  (`braidingEquiv_mem_laurentSpan`);
* `σ z - flip z ∈ (v - 1) L` for every `z ∈ L` (`braidingEquiv_sub_tensorFlip_mem`).

The proof follows the structure of Webster's argument. The lattice `L` is spanned by divided
lowering words applied to the vectors `x ⊗ v_{λ₂}` (`tmul_mem_laurentSpan_braidGenerator`), as
in the proof of Theorem 4.38. On those vectors `σ (x ⊗ v_{λ₂}) = v^{-(ν, λ₂)} v_{λ₂} ⊗ x`, a unit
multiple of the flip that is `≡ 1` at `v = 1`. The braiding commutes with the divided powers
`Fᵢ^{(n)}`, and so does the flip modulo `(v - 1) L`: the coproduct of `Fᵢ^{(n)}` has monomial
coefficients that agree with those of the opposite coproduct at `v = 1`
(`dividedF_tensorFlip_sub_mem`).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop KLR.CycKLR LusztigF
open scoped TensorProduct

local notation "𝕍" => (RatFunc.X : RatFunc ℚ)
local notation "𝕂" => RatFunc ℚ
local notation "LP" => LaurentPolynomial ℤ
local instance braidingLatticeInst1 : NeZero 𝕍 := ⟨RatFunc.X_ne_zero⟩

/-! ### Scalars -/

/-- `v^c - 1` is divisible by `v - 1` in `ℤ[v, v⁻¹]`. -/
theorem exists_zpow_sub_one (c : ℤ) :
    ∃ p : LP, (𝕍 ^ c - 1 : 𝕂) = (𝕍 - 1) * integralLaurentEval p := by
  have hnat : ∀ n : ℕ, (𝕍 ^ (n : ℤ) - 1 : 𝕂) =
      (𝕍 - 1) * integralLaurentEval (∑ i ∈ Finset.range n, LaurentPolynomial.T (i : ℤ)) := by
    intro n
    rw [map_sum]
    simp only [integralLaurentEval_T, zpow_natCast]
    rw [mul_comm, geom_sum_mul]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · exact ⟨_, hnat n⟩
  · refine ⟨-LaurentPolynomial.T (-(n : ℤ)) *
      ∑ i ∈ Finset.range n, LaurentPolynomial.T (i : ℤ), ?_⟩
    rw [map_mul, map_neg, integralLaurentEval_T,
      show ∀ a b : 𝕂, (𝕍 - 1) * (-a * b) = -a * ((𝕍 - 1) * b) from fun a b => by ring, ← hnat n,
      neg_mul, mul_sub, ← zpow_add₀ RatFunc.X_ne_zero, neg_add_cancel, zpow_zero, mul_one]
    ring

section LaurentSpan

variable {V : Type*} [AddCommGroup V] [Module 𝕂 V]

/-- The `𝒜`-span of `(v - 1) S`, that is `(v - 1)` times the `𝒜`-span of `S`. -/
abbrev vOneSpan (S : Set V) : Submodule ℤ V :=
  laurentSpan ((fun s => (𝕍 - 1) • s) '' S)

theorem sub_one_smul_mem_vOneSpan {S : Set V} {z : V} (hz : z ∈ laurentSpan S) :
    (𝕍 - 1) • z ∈ vOneSpan S := by
  have h := map_mem_laurentSpan (T := (fun s => (𝕍 - 1) • s) '' S)
    (DistribSMul.toLinearMap 𝕂 V (𝕍 - 1 : 𝕂))
    (fun s hs => mem_laurentSpan_of_mem (Set.mem_image_of_mem (fun s => (𝕍 - 1) • s) hs)) hz
  exact h

/-- `(v^a - v^b) z ∈ (v - 1) L` for `z ∈ L`. -/
theorem zpow_sub_zpow_smul_mem_vOneSpan {S : Set V} (a b : ℤ) {z : V}
    (hz : z ∈ laurentSpan S) : ((𝕍 ^ a - 𝕍 ^ b : 𝕂)) • z ∈ vOneSpan S := by
  obtain ⟨p, hp⟩ := exists_zpow_sub_one (a - b)
  have he : (𝕍 ^ a - 𝕍 ^ b : 𝕂) = 𝕍 ^ b * integralLaurentEval p * (𝕍 - 1) := by
    rw [mul_assoc, mul_comm (integralLaurentEval p), ← hp, mul_sub, ← zpow_add₀ RatFunc.X_ne_zero,
      add_sub_cancel, mul_one]
  rw [he, mul_smul, mul_smul]
  exact zpow_smul_mem_laurentSpan b (laurent_smul_mem_laurentSpan ⟨p, rfl⟩
    (sub_one_smul_mem_vOneSpan hz))

end LaurentSpan

variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} {R : D.RootDatum Y}

private abbrev Fac (w : Dom R) := IrreducibleModule R 𝕍 w.1
local notation "divF" => fun (i : I) (n : ℕ) => qDivPow (𝕍 ^ D.d i) n (F R 𝕍 i)

/-! ### Lattices of two factors -/

section Lattice

variable (w₁ w₂ : Dom R)

/-- The pure tensors `x ⊗ y` of weight vectors `x ∈ V_ℤ(λ₁)`, `y ∈ V_ℤ(λ₂)`. -/
def pureIntegralTensor : Set (TensorModule 𝕂 (Fac w₁) (Fac w₂)) :=
  {z | ∃ (x : Fac w₁) (y : Fac w₂) (μ₁ μ₂ : Y →+ ℤ), x ∈ hwIntegral w₁ ∧
    x ∈ weightSpace R 𝕍 (Fac w₁) μ₁ ∧ y ∈ hwIntegral w₂ ∧ y ∈ weightSpace R 𝕍 (Fac w₂) μ₂ ∧
      z = TensorModule.mk _ _ (x ⊗ₜ[𝕂] y)}

/-- The flip `x ⊗ y ↦ y ⊗ x` of the two tensor factors. -/
def tensorFlip : TensorModule 𝕂 (Fac w₁) (Fac w₂) ≃ₗ[𝕂] TensorModule 𝕂 (Fac w₂) (Fac w₁) :=
  ((TensorModule.mk _ _).symm.trans (TensorProduct.comm 𝕂 _ _)).trans (TensorModule.mk _ _)

omit [Finite I] in
theorem tensorFlip_mk (x : Fac w₁) (y : Fac w₂) :
    tensorFlip w₁ w₂ (TensorModule.mk _ _ (x ⊗ₜ[𝕂] y)) = TensorModule.mk _ _ (y ⊗ₜ[𝕂] x) :=
  rfl

theorem tensorFlip_mem_pureIntegralTensor {z : TensorModule 𝕂 (Fac w₁) (Fac w₂)}
    (hz : z ∈ pureIntegralTensor w₁ w₂) : tensorFlip w₁ w₂ z ∈ pureIntegralTensor w₂ w₁ := by
  obtain ⟨x, y, μ₁, μ₂, hx, hxμ, hy, hyμ, rfl⟩ := hz
  exact ⟨y, x, μ₂, μ₁, hy, hyμ, hx, hxμ, rfl⟩

theorem tensorFlip_mem_laurentSpan {z : TensorModule 𝕂 (Fac w₁) (Fac w₂)}
    (hz : z ∈ laurentSpan (pureIntegralTensor w₁ w₂)) :
    tensorFlip w₁ w₂ z ∈ laurentSpan (pureIntegralTensor w₂ w₁) :=
  map_mem_laurentSpan (tensorFlip w₁ w₂).toLinearMap
    (fun _ hs => mem_laurentSpan_of_mem (tensorFlip_mem_pureIntegralTensor w₁ w₂ hs)) hz

/-- A divided power `Fᵢ^{(n)}` keeps a pure tensor of integral weight vectors in the lattice. -/
theorem dividedF_smul_mem_laurentSpan (i : I) (n : ℕ) {z : TensorModule 𝕂 (Fac w₁) (Fac w₂)}
    (hz : z ∈ laurentSpan (pureIntegralTensor w₁ w₂)) :
    divF i n • z ∈ laurentSpan (pureIntegralTensor w₁ w₂) := by
  refine map_mem_laurentSpan (DistribSMul.toLinearMap 𝕂 _ (divF i n)) ?_ hz
  rintro _ ⟨x, y, μ₁, μ₂, hx, hxμ, hy, hyμ, rfl⟩
  rw [DistribSMul.toLinearMap_apply, TensorModule.qDivPow_F_smul_tmul ratFunc_X_not_root i _ hyμ]
  refine Submodule.sum_mem _ fun p _ ↦
    laurent_smul_mem_laurentSpan (Modified.isLaurent_vd_zpow _ _) ?_
  exact mem_laurentSpan_of_mem ⟨_, _, _, _, dF_smul_mem_hwIntegral w₁ i p.1 hx,
    qDivPow_F_smul_mem_weightSpace hxμ i p.1, dF_smul_mem_hwIntegral w₂ i p.2 hy,
    qDivPow_F_smul_mem_weightSpace hyμ i p.2, rfl⟩

/-- A divided power `Fᵢ^{(n)}` keeps `(v - 1) L` inside `(v - 1) L`. -/
theorem dividedF_smul_mem_vOneSpan (i : I) (n : ℕ) {z : TensorModule 𝕂 (Fac w₁) (Fac w₂)}
    (hz : z ∈ vOneSpan (pureIntegralTensor w₁ w₂)) :
    divF i n • z ∈ vOneSpan (pureIntegralTensor w₁ w₂) := by
  refine map_mem_laurentSpan (DistribSMul.toLinearMap 𝕂 _ (divF i n)) ?_ hz
  rintro _ ⟨s, hs, rfl⟩
  rw [DistribSMul.toLinearMap_apply, smul_comm]
  exact sub_one_smul_mem_vOneSpan
    (dividedF_smul_mem_laurentSpan w₁ w₂ i n (mem_laurentSpan_of_mem hs))

omit [Finite I] in
private theorem zpow_vd (d : ℕ) (a : ℤ) : ((𝕍 ^ d) ^ a : 𝕂) = 𝕍 ^ ((d : ℤ) * a) := by
  rw [← zpow_natCast, ← zpow_mul]

/-- **The flip commutes with `Fᵢ^{(n)}` modulo `(v - 1) L`**: the coproduct of `Fᵢ^{(n)}` and
its opposite have monomial coefficients that agree at `v = 1`. -/
theorem dividedF_tensorFlip_sub_mem (i : I) (n : ℕ) {z : TensorModule 𝕂 (Fac w₁) (Fac w₂)}
    (hz : z ∈ laurentSpan (pureIntegralTensor w₁ w₂)) :
    divF i n • tensorFlip w₁ w₂ z - tensorFlip w₁ w₂ (divF i n • z) ∈
      vOneSpan (pureIntegralTensor w₂ w₁) := by
  refine map_mem_laurentSpan
    ((DistribSMul.toLinearMap 𝕂 _ (divF i n)) ∘ₗ (tensorFlip w₁ w₂).toLinearMap -
      (tensorFlip w₁ w₂).toLinearMap ∘ₗ (DistribSMul.toLinearMap 𝕂 _ (divF i n))) ?_ hz
  rintro _ ⟨x, y, μ₁, μ₂, hx, hxμ, hy, hyμ, rfl⟩
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, DistribSMul.toLinearMap_apply,
    LinearEquiv.coe_coe, tensorFlip_mk]
  rw [TensorModule.qDivPow_F_smul_tmul ratFunc_X_not_root i _ hxμ,
    TensorModule.qDivPow_F_smul_tmul ratFunc_X_not_root i _ hyμ, map_sum,
    ← Finset.Nat.sum_antidiagonal_swap, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun p _ ↦ ?_
  simp only [Prod.fst_swap, Prod.snd_swap, map_smul, tensorFlip_mk, ← sub_smul, zpow_vd]
  exact zpow_sub_zpow_smul_mem_vOneSpan _ _ (mem_laurentSpan_of_mem ⟨_, _, _, _,
    dF_smul_mem_hwIntegral w₂ i p.2 hy, qDivPow_F_smul_mem_weightSpace hyμ i p.2,
    dF_smul_mem_hwIntegral w₁ i p.1 hx, qDivPow_F_smul_mem_weightSpace hxμ i p.1, rfl⟩)

end Lattice

/-! ### Generation by divided words on `x ⊗ v_{λ₂}` -/

section Generation

variable (w₁ w₂ : Dom R)

/-- Successive divided lowering powers `⋯ Fᵢ₂^{(n₂)} Fᵢ₁^{(n₁)}`, as an element of `U`. -/
def dividedFWord (d : List (I × ℕ)) : LieLean.QuantumGroup R 𝕍 :=
  d.foldl (fun u a => divF a.1 a.2 * u) 1

omit [Finite I] in
theorem dividedFWord_snoc (d : List (I × ℕ)) (i : I) (n : ℕ) :
    dividedFWord (R := R) (d ++ [(i, n)]) = divF i n * dividedFWord d := by
  simp [dividedFWord, List.foldl_append]

omit [Finite I] in
theorem dividedFWord_nil : dividedFWord (R := R) [] = 1 := rfl

omit [Finite I] in
/-- A divided lowering word applied to the highest weight vector has a depth. -/
theorem dividedLoweringWord_mem_depthSpace (w : Dom R) (d : List (I × ℕ)) :
    ∃ ν, dividedLoweringWord w d ∈ depthSpace R (Fac w) w.1 ν := by
  induction d using List.reverseRecOn with
  | nil =>
    refine ⟨0, ?_⟩
    change IrreducibleModule.hwv R 𝕍 w.1 ∈ weightSpace R 𝕍 (Fac w) (w.1 - R.rootSum 0)
    rw [R.rootSum_zero, sub_zero]
    exact IrreducibleModule.hwv_mem_weightSpace
  | append_singleton d a ih =>
    obtain ⟨ν, hν⟩ := ih
    obtain ⟨i, n⟩ := a
    refine ⟨ν + Finsupp.single i n, ?_⟩
    rw [show dividedLoweringWord w (d ++ [(i, n)]) = divF i n • dividedLoweringWord w d by
      simp [dividedLoweringWord, List.foldl_append]]
    have h := qDivPow_F_smul_mem_weightSpace hν i n
    rwa [show w.1 - R.rootSum ν - n • R.root i = w.1 - R.rootSum (ν + Finsupp.single i n) by
      rw [R.rootSum_add, R.rootSum_single]; abel] at h

theorem dividedWord_mem_hwIntegral (w : Dom R) (d : List (I × ℕ)) :
    dividedLoweringWord w d ∈ hwIntegral w := by
  rw [← span_dividedLoweringWord]
  exact Submodule.subset_span (Set.mem_range_self d)

/-- The divided lowering words applied to the vectors `x ⊗ v_{λ₂}`, `x` a divided lowering
word of `V^{λ₁}`. -/
def braidGenerator : Set (TensorModule 𝕂 (Fac w₁) (Fac w₂)) :=
  {z | ∃ d d' : List (I × ℕ), z = dividedFWord (R := R) d • TensorModule.mk _ _
    (dividedLoweringWord w₁ d' ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕍 w₂.1)}

omit [Finite I] in
theorem dividedF_smul_mem_laurentSpan_braidGenerator (i : I) (n : ℕ)
    {z : TensorModule 𝕂 (Fac w₁) (Fac w₂)} (hz : z ∈ laurentSpan (braidGenerator w₁ w₂)) :
    divF i n • z ∈ laurentSpan (braidGenerator w₁ w₂) := by
  refine map_mem_laurentSpan (DistribSMul.toLinearMap 𝕂 _ (divF i n)) ?_ hz
  rintro _ ⟨d, d', rfl⟩
  rw [DistribSMul.toLinearMap_apply, ← mul_smul, ← dividedFWord_snoc]
  exact mem_laurentSpan_of_mem ⟨_, d', rfl⟩

private theorem tmul_hwv_mem_laurentSpan {x : Fac w₁} (hx : x ∈ hwIntegral w₁) :
    TensorModule.mk _ _ (x ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕍 w₂.1) ∈
      laurentSpan (braidGenerator w₁ w₂) := by
  rw [← span_dividedLoweringWord] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d', rfl⟩ := hx
    exact mem_laurentSpan_of_mem ⟨[], d', by rw [dividedFWord_nil, one_smul]⟩
  | zero => rw [TensorProduct.zero_tmul, map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.add_tmul, map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [hw_laurent_smul_eq, ← TensorProduct.smul_tmul', map_smul]
    exact laurent_smul_mem_laurentSpan ⟨c, rfl⟩ ha

private theorem tmul_word_mem_laurentSpan (d : List (I × ℕ)) :
    ∀ x ∈ hwIntegral w₁, TensorModule.mk _ _ (x ⊗ₜ[𝕂] dividedLoweringWord w₂ d) ∈
      laurentSpan (braidGenerator w₁ w₂) := by
  induction d using List.reverseRecOn with
  | nil => exact fun x hx => tmul_hwv_mem_laurentSpan w₁ w₂ hx
  | append_singleton d a ih =>
    obtain ⟨i, n⟩ := a
    let y := dividedLoweringWord w₂ d
    obtain ⟨ν, hν⟩ := dividedLoweringWord_mem_depthSpace w₂ d
    rw [show dividedLoweringWord w₂ (d ++ [(i, n)]) = divF i n • y by
      simp [y, dividedLoweringWord, List.foldl_append]]
    induction n using Nat.strong_induction_on with
    | h n hn =>
      intro x hx
      have hall := dividedF_smul_mem_laurentSpan_braidGenerator w₁ w₂ i n (ih x hx)
      have h0 : ((0, n) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal n :=
        Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add n)
      rw [TensorModule.qDivPow_F_smul_tmul ratFunc_X_not_root i _ hν,
        ← Finset.add_sum_erase _ _ h0] at hall
      simp only [Nat.cast_zero, zero_mul, sub_self, zpow_zero, one_smul, qDivPow_zero'] at hall
      refine (add_mem_cancel_right (Submodule.sum_mem _ fun p hp => ?_)).1 hall
      obtain ⟨hp0, hp⟩ := Finset.mem_erase.1 hp
      have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      have hlt : p.2 < n := by
        rcases p with ⟨a, b⟩
        by_contra! hb
        exact hp0 (Prod.ext (by simp only at hsum ⊢; omega) (by simp only at hsum ⊢; omega))
      exact laurent_smul_mem_laurentSpan (Modified.isLaurent_vd_zpow _ _)
        (hn p.2 hlt _ (dF_smul_mem_hwIntegral w₁ i p.1 hx))

/-- **Integral generation** (as in Webster, arXiv:1309.3796v2, proof of Theorem 4.38): every
`x ⊗ y` with `x ∈ V_ℤ(λ₁)` and `y ∈ V_ℤ(λ₂)` lies in the `𝒜`-span of the divided lowering words
applied to the vectors `x' ⊗ v_{λ₂}`. -/
theorem tmul_mem_laurentSpan_braidGenerator {x : Fac w₁} (hx : x ∈ hwIntegral w₁) {y : Fac w₂}
    (hy : y ∈ hwIntegral w₂) :
    TensorModule.mk _ _ (x ⊗ₜ[𝕂] y) ∈ laurentSpan (braidGenerator w₁ w₂) := by
  rw [← span_dividedLoweringWord] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, rfl⟩ := hy
    exact tmul_word_mem_laurentSpan w₁ w₂ d x hx
  | zero => rw [TensorProduct.tmul_zero, map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [TensorProduct.tmul_add, map_add]; exact add_mem ha hb
  | smul c a _ ha =>
    rw [hw_laurent_smul_eq, TensorProduct.tmul_smul, map_smul]
    exact laurent_smul_mem_laurentSpan ⟨c, rfl⟩ ha

theorem laurentSpan_pure_le_braidGenerator :
    laurentSpan (pureIntegralTensor w₁ w₂) ≤ laurentSpan (braidGenerator w₁ w₂) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, _, ⟨x, y, _, _, hx, _, hy, _, rfl⟩, rfl⟩
  exact zpow_smul_mem_laurentSpan k (tmul_mem_laurentSpan_braidGenerator w₁ w₂ hx hy)

end Generation

/-! ### The braiding on the lattice -/

section Braiding

variable (hR : R.IsXRegular) (w₁ w₂ : Dom R)

local notation "σ" => IrreducibleModule.braidingEquiv hR (Subtype.val w₁) (Subtype.val w₂)

private theorem braidGenerator_spec (d d' : List (I × ℕ)) :
    let z := dividedFWord (R := R) d • TensorModule.mk _ _
      (dividedLoweringWord w₁ d' ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕍 w₂.1)
    z ∈ laurentSpan (pureIntegralTensor w₁ w₂) ∧
      σ z ∈ laurentSpan (pureIntegralTensor w₂ w₁) ∧
      σ z - tensorFlip w₁ w₂ z ∈ vOneSpan (pureIntegralTensor w₂ w₁) := by
  intro z
  obtain ⟨ν, hν⟩ := dividedLoweringWord_mem_depthSpace w₁ d'
  have hx := dividedWord_mem_hwIntegral w₁ d'
  induction d using List.reverseRecOn with
  | nil =>
    simp only [z, dividedFWord_nil, one_smul]
    rw [IrreducibleModule.braidingEquiv_tmul_hwv hR w₁.1 w₂.1 hν, map_smul, tensorFlip_mk]
    have hp : TensorModule.mk _ _ (IrreducibleModule.hwv R 𝕍 w₂.1 ⊗ₜ[𝕂]
        dividedLoweringWord w₁ d') ∈ laurentSpan (pureIntegralTensor w₂ w₁) :=
      mem_laurentSpan_of_mem ⟨_, _, _, _, hwv_mem_hwIntegral w₂,
        IrreducibleModule.hwv_mem_weightSpace, hx, hν, rfl⟩
    refine ⟨mem_laurentSpan_of_mem ⟨_, _, _, _, hx, hν, hwv_mem_hwIntegral w₂,
      IrreducibleModule.hwv_mem_weightSpace, rfl⟩, zpow_smul_mem_laurentSpan _ hp, ?_⟩
    have h := zpow_sub_zpow_smul_mem_vOneSpan (-pairDepth R w₂.1 ν) 0 hp
    rwa [sub_smul, zpow_zero, one_smul] at h
  | append_singleton d a ih =>
    obtain ⟨i, n⟩ := a
    obtain ⟨h₀, h₁, h₂⟩ := ih
    simp only [z, dividedFWord_snoc, mul_smul]
    set z₀ := dividedFWord (R := R) d • TensorModule.mk _ _
      (dividedLoweringWord w₁ d' ⊗ₜ[𝕂] IrreducibleModule.hwv R 𝕍 w₂.1)
    rw [LinearEquiv.map_smul]
    refine ⟨dividedF_smul_mem_laurentSpan w₁ w₂ i n h₀,
      dividedF_smul_mem_laurentSpan w₂ w₁ i n h₁, ?_⟩
    rw [show divF i n • σ z₀ - tensorFlip w₁ w₂ (divF i n • z₀) =
        divF i n • (σ z₀ - tensorFlip w₁ w₂ z₀) +
          (divF i n • tensorFlip w₁ w₂ z₀ - tensorFlip w₁ w₂ (divF i n • z₀)) by
      rw [smul_sub]; abel]
    exact add_mem (dividedF_smul_mem_vOneSpan w₂ w₁ i n h₂)
      (dividedF_tensorFlip_sub_mem w₁ w₂ i n h₀)

/-- **The braiding preserves the integral lattice**: `σ` maps the `𝒜`-span of the `x ⊗ y`
(`x ∈ V_ℤ(λ₁)`, `y ∈ V_ℤ(λ₂)`) into the corresponding lattice of `V^{λ₂} ⊗ V^{λ₁}`. -/
theorem braidingEquiv_mem_laurentSpan {z : TensorModule 𝕂 (Fac w₁) (Fac w₂)}
    (hz : z ∈ laurentSpan (pureIntegralTensor w₁ w₂)) :
    σ z ∈ laurentSpan (pureIntegralTensor w₂ w₁) := by
  refine map_mem_laurentSpan ((σ).restrictScalars 𝕂).toLinearMap ?_
    (laurentSpan_pure_le_braidGenerator w₁ w₂ hz)
  rintro _ ⟨d, d', rfl⟩
  exact (braidGenerator_spec hR w₁ w₂ d d').2.1

/-- **At `v = 1` the braiding is the flip**: `σ z - flip z ∈ (v - 1) L` for every `z` of the
integral lattice `L` (Webster, arXiv:1309.3796v2, proof of Lemma 6.11). -/
theorem braidingEquiv_sub_tensorFlip_mem {z : TensorModule 𝕂 (Fac w₁) (Fac w₂)}
    (hz : z ∈ laurentSpan (pureIntegralTensor w₁ w₂)) :
    σ z - tensorFlip w₁ w₂ z ∈ vOneSpan (pureIntegralTensor w₂ w₁) := by
  refine map_mem_laurentSpan (((σ).restrictScalars 𝕂).toLinearMap -
    (tensorFlip w₁ w₂).toLinearMap) ?_ (laurentSpan_pure_le_braidGenerator w₁ w₂ hz)
  rintro _ ⟨d, d', rfl⟩
  exact (braidGenerator_spec hR w₁ w₂ d d').2.2

include hR in
/-- Pure tensors of integral vectors lie in the integral lattice. -/
theorem tmul_mem_laurentSpan_pure {x : Fac w₁} (hx : x ∈ hwIntegral w₁) {y : Fac w₂}
    (hy : y ∈ hwIntegral w₂) :
    TensorModule.mk _ _ (x ⊗ₜ[𝕂] y) ∈ laurentSpan (pureIntegralTensor w₁ w₂) := by
  refine map_mem_laurentSpan LinearMap.id ?_ (tmul_mem_laurentSpan_braidGenerator w₁ w₂ hx hy)
  rintro _ ⟨d, d', rfl⟩
  exact (braidGenerator_spec hR w₁ w₂ d d').1

end Braiding

end Categorification.Stendhal.FirstWeight
