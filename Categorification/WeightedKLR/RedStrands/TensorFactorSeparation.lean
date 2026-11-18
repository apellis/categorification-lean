/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorShuffleCriterion
import Categorification.WeightedKLR.RedStrands.TensorLatticeCoordinates
import LieLean.Algebra.QuantumGroup.CrystalBasis.Global.TensorLattice
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# Separation by tensor products of simple-top coordinates

In Webster, arXiv:1309.3796v2, §4.7, proof of Theorem 4.38, tests on the
earlier and the last factor give tests on their tensor product. The integral
highest-weight lattice spans the entire rational module by Lusztig 14.4.12.
Consequently the product tests separate all tensor vectors, including the
bar images of every integral weight space.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight
open KLR QuantumGroup LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped TensorProduct
local notation "L" => RatFunc ℚ
local notation "v" => (RatFunc.X : L)
local notation "LP" => LaurentPolynomial ℤ
private local instance separationNeZero : NeZero v := ⟨RatFunc.X_ne_zero⟩

section Rational
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
    {D : LusztigCartanDatum I} {R : D.RootDatum Y} (hR : R.IsXRegular)
    (wt : Dom R)

private theorem hwBasis_integral (b : canonicalBasisHW D wt) : canonicalBasisHWBasis wt hR b ∈ hwIntegral wt := by
  rw [canonicalBasisHWBasis_apply]
  exact ⟨b,negIntegral_of_mem_canonicalBasis (canonicalBasisHW_subset D wt b.2),rfl⟩

include hR in
/-- Rational spanning of the integral highest-weight lattice, from the
canonical basis in Lusztig 14.4.12. -/
theorem rationalSpan_hwIntegral : Submodule.span L (↑(hwIntegral wt) : Set (IrreducibleModule R v wt.1)) = ⊤ := by
  apply top_unique
  rw [← (canonicalBasisHWBasis wt hR).span_eq]
  exact Submodule.span_mono (Set.range_subset_iff.mpr (hwBasis_integral hR wt))

include hR in
/-- The integral tensor lattice spans the full rational ordered tensor product. -/
theorem rationalSpan_integralTensor {n : ℕ} (weights : Fin n → Dom R) :
    Submodule.span L (↑(integralTensor weights) : Set (TensorSpace weights)) = ⊤ := by
  let b := fun j => canonicalBasisHWBasis (weights j) hR
  apply top_unique
  rw [← (Basis.piTensorProduct b).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  rw [Basis.piTensorProduct_apply]
  exact Submodule.subset_span ⟨_,fun i => hwBasis_integral hR (weights i) (j i),rfl⟩

end Rational

private theorem span_eq_top_of_image {F T : Type*} [Field F] [AddCommGroup T] [Module F T]
    (f : T ≃ₗ[F] T) (s : Set T) (V : Submodule F T) (hs : Submodule.span F s = ⊤)
    (h : ∀ x ∈ s, f x ∈ V) : V = ⊤ := by
  have hm : (Submodule.span F s).map f.toLinearMap ≤ V := by
    rw [Submodule.map_span]
    exact Submodule.span_le.mpr (Set.image_subset_iff.mpr h)
  rw [hs, Submodule.map_top, f.range] at hm
  exact top_unique hm

open scoped Classical in
private theorem product_tests_injective {F X Y A B : Type*} [Field F] [AddCommGroup X] [Module F X]
    [AddCommGroup Y] [Module F Y] (p : A → X) (q : B → Y) (f : A → X →ₗ[F] F) (g : B → Y →ₗ[F] F)
    (hp : Submodule.span F (Set.range p) = ⊤) (hq : Submodule.span F (Set.range q) = ⊤)
    (hf : ∀ a i, f a (p i) = if a = i then 1 else 0)
    (hg : ∀ b i, g b (q i) = if b = i then 1 else 0) :
    Function.Injective (fun z : X ⊗[F] Y => fun j : A × B => factorTensorTest f g j.1 j.2 z) := by
  let t (j : A × B) := p j.1 ⊗ₜ[F] q j.2
  have ht : Submodule.span F (Set.range t) = ⊤ := by
    have h := Submodule.map₂_span_span F (TensorProduct.mk F X Y) (Set.range p) (Set.range q)
    rw [hp, hq, TensorProduct.map₂_mk_top_top_eq_top, Set.image2_range] at h
    exact h.symm
  intro x y he
  have hx : x ∈ Submodule.span F (Set.range t) := ht ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span F (Set.range t) := ht ▸ Submodule.mem_top
  have eq := factorTensorTest_separates p q f g (Function.Embedding.refl _) hf hg (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) he
  exact congrArg Subtype.val eq

variable {I Y : Type*} [DecidableEq I] [Finite I] [AddCommGroup Y] {n : ℕ}
    (C : CartanDatum I) {R : C.toLusztig.RootDatum Y} (wt : Fin (n+1) → Dom R) (hR : R.IsXRegular)
local notation "wt₀" => fun j : Fin n => wt (Fin.castSucc j)
local notation "λ₁" => wt (Fin.last n)
local notation "V₀" => TensorSpace wt₀
local notation "V₁" => IrreducibleModule R v λ₁.1

open scoped Classical in
/-- Product coordinates on the rational factors separate each integral block
after applying the inverse quasi-R equivalence. The earlier basis vectors are
in bar convention; the final ones lie in the ordinary highest-weight lattice. -/
theorem barWeightCoordinates_injective_of_factorTests (β : Multiset I) {A B : Type*}
    (p : A → V₀) (q : B → V₁) (f : A → V₀ →ₗ[L] L) (g : B → V₁ →ₗ[L] L)
    (hp : ∀ x : integralTensor wt₀, (tensorCoproductEquiv hR wt₀).symm (x : V₀) ∈ Submodule.span L (Set.range p))
    (hq : Submodule.span LP (Set.range q) = hwIntegral λ₁)
    (hf : ∀ a i, f a (p i) = if a = i then 1 else 0)
    (hg : ∀ b i, g b (q i) = if b = i then 1 else 0) :
    Function.Injective (barWeightCoordinates C wt hR β
      (fun j : A × B => (factorTensorTest f g j.1 j.2).comp (tensorSplitLast wt).toLinearMap)) := by
  have hP := span_eq_top_of_image (tensorCoproductEquiv hR wt₀).symm _ _ (rationalSpan_integralTensor hR wt₀)
    (fun x hx => hp ⟨x,hx⟩)
  have hQ : Submodule.span L (Set.range q) = ⊤ := by
    apply top_unique
    rw [← rationalSpan_hwIntegral hR λ₁]
    apply Submodule.span_le.mpr
    intro x hx
    change x ∈ hwIntegral λ₁ at hx
    rw [← hq] at hx
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [hw_laurent_smul_eq]; exact Submodule.smul_mem _ _ ha
  intro x y h
  apply Subtype.ext
  apply (tensorCoproductEquiv hR wt).symm.injective
  apply (tensorSplitLast wt).injective
  exact product_tests_injective p q f g hP hQ hf hg h

end Categorification.Stendhal.FirstWeight
