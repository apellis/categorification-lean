/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Algebra
import Categorification.Algebra.Graded.KrullSchmidt
import Categorification.KLR.K0Free

/-!
# Scalar extension of the weighted graded Grothendieck group

Supporting the integral quantum-group map of Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19 (roadmap C). Graded Krull–Schmidt makes each component free over
`ℤ[q,q⁻¹]`, by the argument of Khovanov–Lauda I, arXiv:0803.4121v2, §2.5.
Their direct sum is therefore free, and scalar extension along `q ↦ v⁻¹`
is injective. The finiteness and lower-bound assumptions are the existing
`HasGdim` hypotheses on the component algebras.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}

/-- The direct sum of the weighted graded Grothendieck groups is free over
the Laurent polynomial ring. This is the graded Krull–Schmidt input to
integral descent in Webster Theorem 2.19; no loop-freeness hypothesis is needed. -/
theorem K0W_free (G : GradingDatum Γ)
    [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)] :
    Module.Free (LaurentPolynomial ℤ) G.K0W := by
  have : ∀ ν : I →₀ ℕ, Module.Free (LaurentPolynomial ℤ) (K0 (G.klrGrade ν)) :=
    fun _ => inferInstance
  infer_instance

attribute [local instance] KLR.KLGamma.qToVAlgebra

variable (G : GradingDatum Γ)

/-- The rational scalar extension of the weighted Grothendieck algebra along
`q ↦ v⁻¹`, used in the construction of the integral map of Webster
arXiv:1209.2463v4, Theorem 2.19. -/
def K0Q : Type _ := TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) G.K0W

instance : Ring G.K0Q :=
  inferInstanceAs (Ring (TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) G.K0W))

instance : Algebra (RatFunc ℚ) G.K0Q :=
  inferInstanceAs (Algebra (RatFunc ℚ) (TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) G.K0W))

/-- The weighted scalar extension homomorphism `x ↦ 1 ⊗ x`. -/
def toK0Q : G.K0W →+* G.K0Q :=
  (Algebra.TensorProduct.includeRight : G.K0W →ₐ[LaurentPolynomial ℤ]
    TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) G.K0W).toRingHom

/-- The scalar extension homomorphism is semilinear along `q ↦ v⁻¹`. -/
theorem toK0Q_smul (p : LaurentPolynomial ℤ) (x : G.K0W) :
    G.toK0Q (p • x) = KLR.KLGamma.qToV p • G.toK0Q x := by
  change (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] (p • x) =
    (KLR.KLGamma.qToV p • (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] x :
      TensorProduct (LaurentPolynomial ℤ) (RatFunc ℚ) G.K0W)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
    smul_eq_mul, mul_one]
  rfl

/-- The weighted scalar extension homomorphism is injective by graded
Krull–Schmidt freeness. -/
theorem toK0Q_injective [∀ ν : I →₀ ℕ, HasGdim (G.klrGrade ν)] :
    Function.Injective G.toK0Q := by
  change Function.Injective (fun x : G.K0W => (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] x)
  have := G.K0W_free
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := G.K0W)
    (Algebra.linearMap (LaurentPolynomial ℤ) (RatFunc ℚ)) KLR.KLGamma.qToV_injective
  have hfactor : (fun x : G.K0W => (1 : RatFunc ℚ) ⊗ₜ[LaurentPolynomial ℤ] x) =
      (Algebra.linearMap (LaurentPolynomial ℤ) (RatFunc ℚ)).rTensor G.K0W ∘
        (TensorProduct.lid (LaurentPolynomial ℤ) G.K0W).symm := by
    funext x
    simp
  rw [hfactor]
  exact hinj.comp (TensorProduct.lid (LaurentPolynomial ℤ) G.K0W).symm.injective

end Categorification.WeightedKLR.GradingDatum
