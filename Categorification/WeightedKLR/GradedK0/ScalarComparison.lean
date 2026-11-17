/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Induction
import Categorification.WeightedKLR.Induction.ModuleMonoidal
import Mathlib.Algebra.DirectSum.Algebra

/-!
# Scalar comparison for weighted induction

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Definition 2.17 and Theorem 2.19. The graded induction module is a
balanced tensor product over `k`, while the existing induction associators use
the tensor product over `ℤ`. Balancing over the coefficient algebra already
imposes the scalar relations of `k`, giving an explicit comparison between
these tensor models. This supports the graded associativity and unit maps.
-/

noncomputable section

namespace Categorification.InductionAlong

open MulOpposite

section ScalarComparison

universe u

variable {k N : Type*} {A B : Type u} [CommRing k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  (φ : A →ₙ+* B) (hφ : ∀ (c : k) (a : A), φ (c • a) = c • φ a)

include hφ

/-- Balancing over the coefficient algebra already imposes the scalar relations
over `k`. This identifies the two tensor models used for weighted induction. -/
def balancedIndEquiv : BalancedTensor k B A (Corner φ) N ≃ₗ[B] IndK k N φ := by
  let f : Corner φ →ₗ[k] N →ₗ[k] IndK k N φ := LinearMap.mk₂ k
    (fun z n => Ind.tmul z n)
    (fun z z' n => Ind.add_tmul z z' n)
    (fun c z n => by
      change Ind.tmul (c • z) n = algebraMap k B c • Ind.tmul z n
      have hz : c • z = algebraMap k B c • z := Subtype.ext (Algebra.smul_def c z.1)
      rw [hz, ← Ind.smul_tmul])
    (fun z n n' => Ind.tmul_add z n n')
    (fun c z n => Ind.tmul_algebraMap_smul k hφ z c n)
  let F : BalancedTensor k B A (Corner φ) N →ₗ[B] IndK k N φ :=
    BalancedTensor.liftB f (fun z a n => Ind.op_smul_tmul z a n)
      (fun b z n => (Ind.smul_tmul b z n).symm)
  let H : IndK k N φ →ₗ[B] BalancedTensor k B A (Corner φ) N :=
    Ind.lift (fun z n => BalancedTensor.tmul z n)
      (fun z z' n => BalancedTensor.add_tmul z z' n)
      (fun z n n' => BalancedTensor.tmul_add z n n')
      (fun z a n => BalancedTensor.op_smul_tmul z a n)
      (fun b z n => (BalancedTensor.smul_tmul' b z n).symm)
  refine LinearEquiv.ofLinearMap F H ?_ ?_
  · apply Ind.ext
    intro z n
    rfl
  · apply BalancedTensor.extB
    intro z n
    rfl

@[simp] theorem balancedIndEquiv_tmul (z : Corner φ) (n : N) :
    balancedIndEquiv φ hφ (BalancedTensor.tmul z n) = Ind.tmul z n := rfl

@[simp] theorem balancedIndEquiv_symm_tmul (z : Corner φ) (n : N) :
    (balancedIndEquiv φ hφ).symm (Ind.tmul z n) = BalancedTensor.tmul z n := rfl

end ScalarComparison

section MapEquiv

universe u w

variable {k : Type*} [CommRing k] {A B : Type u} [Ring A] [Ring B] [Algebra k B]
  {N N' : Type w} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
  {φ : A →ₙ+* B}

/-- Functoriality with the scalar structure of `IndK` retained in the type. -/
def IndK.mapEquiv (e : N ≃ₗ[A] N') : IndK k N φ ≃ₗ[B] IndK k N' φ :=
  Ind.mapEquiv e

@[simp] theorem IndK.mapEquiv_tmul (e : N ≃ₗ[A] N') (z : Corner φ) (n : N) :
    IndK.mapEquiv (k := k) e (Ind.tmul z n) = Ind.tmul z (e n) := rfl

end MapEquiv



end Categorification.InductionAlong

namespace Categorification.WeightedKLR

open GalleryAlgebra Juxtapose Categorification.Graded Categorification.InductionAlong
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

section Scalar

variable (ν μ : I →₀ ℕ) (N : Type*) [AddCommGroup N] [Module k N]
  [Module (TensorW k Γ ν μ) N] [IsScalarTower k (TensorW k Γ ν μ) N]

/-- The scalar comparison for the two existing models of weighted induction. -/
def gradedIndScalarEquiv : GradedInd k Γ ν μ N ≃ₗ[WeightedKLRAlgebra k Γ (ν + μ)]
    IndK k N (inductionRingHom k Γ ν μ) :=
  balancedIndEquiv (inductionRingHom k Γ ν μ) (fun c a => map_smul (inductionMap k Γ ν μ) c a)

@[simp] theorem gradedIndScalarEquiv_tmul (z : GradedIndBimod k Γ ν μ) (n : N) :
    gradedIndScalarEquiv ν μ N (BalancedTensor.tmul (k := k)
      (B := WeightedKLRAlgebra k Γ (ν + μ)) (A := TensorW k Γ ν μ) z n) =
      Ind.tmul (φ := inductionRingHom k Γ ν μ) z n :=
  balancedIndEquiv_tmul _ _ _ _

@[simp] theorem gradedIndScalarEquiv_symm_tmul (z : GradedIndBimod k Γ ν μ) (n : N) :
    (gradedIndScalarEquiv ν μ N).symm (Ind.tmul (φ := inductionRingHom k Γ ν μ) z n) =
      BalancedTensor.tmul (k := k)
      (B := WeightedKLRAlgebra k Γ (ν + μ)) (A := TensorW k Γ ν μ) z n :=
  balancedIndEquiv_symm_tmul _ _ _ _

end Scalar


end Juxtapose

end Categorification.WeightedKLR
