/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.TotalCoproduct
import Categorification.WeightedKLR.GradedK0.TwistedMultiplication

/-!
# Mackey shifts and multiplication on the tensor square

Webster, arXiv:1209.2463v4, §2.4, Theorem 2.19. The degree shift in the
Mackey filtration is exactly the weight pairing in the braided multiplication.
-/

noncomputable section
namespace Categorification.WeightedKLR

open Categorification.QuantumGroup
variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

private theorem sum_toMultiset_map (μ : I →₀ ℕ) (s : Finset I) (hs : μ.support ⊆ s)
    (f : I → ℤ) : (μ.toMultiset.map f).sum = ∑ i ∈ s, (μ i : ℤ) * f i := by
  rw [Finset.sum_multiset_map_count]
  simp only [Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset, nsmul_eq_mul]
  apply Finset.sum_subset hs
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi, Nat.cast_zero, zero_mul]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Juxtapose.middleShift_eq_crossingDegree (G : GradingDatum Γ) (a b c d : I →₀ ℕ) :
    middleShift G a b c d = G.crossingDegree b c := by
  classical
  let s := (a + b + (c + d)).support
  have hb : b.support ⊆ s := by
    intro i hi
    simp only [s, Finsupp.mem_support_iff, Finsupp.add_apply] at *
    omega
  have hc : c.support ⊆ s := by
    intro i hi
    simp only [s, Finsupp.mem_support_iff, Finsupp.add_apply] at *
    omega
  rw [GradingDatum.crossingDegree, wdot, sum_toMultiset_map b s hb]
  unfold middleShift
  rw [← Finset.sum_coe_sort s]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_toMultiset_map c s hc, Finset.mul_sum, ← Finset.sum_coe_sort s]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_assoc _ _ _


open Categorification.Graded
open scoped TensorProduct
namespace GradingDatum

variable {K : Type*} [Field K] {Δ : WeightedGraph I 𝕜 K}
  (G : GradingDatum Δ)

local notation "L" => LaurentPolynomial ℤ

/-- Insert a tensor of homogeneous classes in the total tensor square. -/
def tensorLof (a b : I →₀ ℕ) :
    G.K0fam a ⊗[L] G.K0fam b →ₗ[L] G.K0W ⊗[L] G.K0W :=
  TensorProduct.map (DirectSum.lof L _ G.K0fam a) (DirectSum.lof L _ G.K0fam b)

theorem map_castW_rfl {ν : I →₀ ℕ} (x : G.K0fam ν) :
    K0.map (castW K Δ (rfl : ν = ν)) (fun _ _ hx => G.castW_symm_mem_klrGrade rfl hx) x = x := by
  induction x using K0.induction_on with
  | of P =>
    exact K0.map_of_semilinear (castW K Δ (rfl : ν = ν)) _ P P (AddEquiv.refl _)
      (fun _ _ => rfl) (fun _ _ h => h) (fun _ _ h => h)
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | neg x hx => rw [map_neg, hx]

theorem lof_indK0TensorCast {a c ν : I →₀ ℕ} (h : a + c = ν)
    (x : G.K0fam a) (y : G.K0fam c) :
    DirectSum.of G.K0fam ν (G.indK0TensorCast a c ν h (x ⊗ₜ y)) =
      DirectSum.of G.K0fam a x * DirectSum.of G.K0fam c y := by
  subst ν
  rw [indK0TensorCast_tmul, map_castW_rfl, K0W_of_mul_of]

theorem twMul_tensorLof {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (D : ShuffleLayout ν' ν'' ν₁ ν₂)
    (x : G.K0fam D.a ⊗[L] G.K0fam D.b) (y : G.K0fam D.c ⊗[L] G.K0fam D.d) :
    G.twMul (G.tensorLof D.a D.b x) (G.tensorLof D.c D.d y) =
      (LaurentPolynomial.T (Juxtapose.middleShift G D.a D.b D.c D.d) : L) •
        G.tensorLof ν₁ ν₂ (D.twistedMulK0Graded G (x ⊗ₜ y)) := by
  induction x using TensorProduct.inductionOn with
  | add u v hu hv => simp [TensorProduct.add_tmul, hu, hv, smul_add]
  | tmul xa xb =>
    induction y using TensorProduct.inductionOn with
    | add u v hu hv => simp [TensorProduct.tmul_add, hu, hv, smul_add]
    | tmul yc yd =>
      simp only [tensorLof, TensorProduct.map_tmul, ShuffleLayout.twistedMulK0Graded_tmul,
        DirectSum.lof_eq_of, lof_indK0TensorCast, twMul_tmul,
        Juxtapose.middleShift_eq_crossingDegree]

end GradingDatum
end Categorification.WeightedKLR
