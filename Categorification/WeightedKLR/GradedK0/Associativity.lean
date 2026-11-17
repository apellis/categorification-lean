/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Induction
import Categorification.WeightedKLR.Induction.ModuleMonoidal
import Mathlib.Algebra.DirectSum.Algebra
import Categorification.WeightedKLR.GradedK0.ScalarComparison

/-!
# Associativity of weighted induction over the coefficient ring

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
§2.4, Definition 2.17 and Theorem 2.19. The scalar comparison transports the
module associator to the tensor model over `k` used for graded induction.
Degree preservation is established in `AssociatorGrading.lean`; the resulting
Grothendieck algebra is constructed in `Algebra.lean`.
-/

noncomputable section

namespace Categorification.WeightedKLR

open GalleryAlgebra Juxtapose Categorification.Graded Categorification.InductionAlong
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

section Assoc

universe w

variable (ν₁ ν₂ ν₃ : I →₀ ℕ) (M N P : Type w) [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν₁) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν₁) M]
  [AddCommGroup N] [Module k N] [Module (WeightedKLRAlgebra k Γ ν₂) N]
  [IsScalarTower k (WeightedKLRAlgebra k Γ ν₂) N]
  [AddCommGroup P] [Module k P] [Module (WeightedKLRAlgebra k Γ ν₃) P]
  [IsScalarTower k (WeightedKLRAlgebra k Γ ν₃) P]

/-- Changing the inner left induction to the scalar-comparison model. -/
def gradedIndAssocLeftScalar :
    GradedInd k Γ (ν₁ + ν₂) ν₃
      (ExtTensor k (GradedInd k Γ ν₁ ν₂ (ExtTensor k M N)) P) ≃ₗ[k]
    ind k Γ (ν₁ + ν₂) ν₃ (ind k Γ ν₁ ν₂ M N) P :=
  ((gradedIndScalarEquiv (ν₁ + ν₂) ν₃ _).restrictScalars k).trans
    ((IndK.mapEquiv (k := k) (φ := inductionRingHom k Γ (ν₁ + ν₂) ν₃)
      (ExtTensor.congr (k := k) (A := WeightedKLRAlgebra k Γ (ν₁ + ν₂))
        (B := WeightedKLRAlgebra k Γ ν₃)
        (gradedIndScalarEquiv ν₁ ν₂ (ExtTensor k M N))
        (LinearEquiv.refl (WeightedKLRAlgebra k Γ ν₃) P))).restrictScalars k)

/-- Changing the inner right induction to the scalar-comparison model. -/
def gradedIndAssocRightScalar :
    GradedInd k Γ ν₁ (ν₂ + ν₃)
      (ExtTensor k M (GradedInd k Γ ν₂ ν₃ (ExtTensor k N P))) ≃ₗ[k]
    ind k Γ ν₁ (ν₂ + ν₃) M (ind k Γ ν₂ ν₃ N P) :=
  ((gradedIndScalarEquiv ν₁ (ν₂ + ν₃) _).restrictScalars k).trans
    ((IndK.mapEquiv (k := k) (φ := inductionRingHom k Γ ν₁ (ν₂ + ν₃))
      (ExtTensor.congr (k := k) (A := WeightedKLRAlgebra k Γ ν₁)
        (B := WeightedKLRAlgebra k Γ (ν₂ + ν₃))
        (LinearEquiv.refl (WeightedKLRAlgebra k Γ ν₁) M)
        (gradedIndScalarEquiv ν₂ ν₃ (ExtTensor k N P)))).restrictScalars k)

/-- The associator of weighted induction in the tensor model over `k`. -/
def gradedIndAssocEquiv :
    GradedInd k Γ (ν₁ + ν₂) ν₃
      (ExtTensor k (GradedInd k Γ ν₁ ν₂ (ExtTensor k M N)) P) ≃ₗ[k]
    GradedInd k Γ ν₁ (ν₂ + ν₃)
      (ExtTensor k M (GradedInd k Γ ν₂ ν₃ (ExtTensor k N P))) :=
  (gradedIndAssocLeftScalar ν₁ ν₂ ν₃ M N P).trans
    ((indAssocEquiv k Γ ν₁ ν₂ ν₃ M N P).trans
      (gradedIndAssocRightScalar ν₁ ν₂ ν₃ M N P).symm)

end Assoc

end Juxtapose


end Categorification.WeightedKLR
