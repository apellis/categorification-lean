/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RightStandardReflection
import Categorification.WeightedKLR.RedStrands.RowStandardK0
import Categorification.WeightedKLR.RedStrands.TensorClassFunctional
import Categorification.WeightedKLR.RedStrands.GradedBraidClassMap

set_option backward.isDefEq.respectTransparency false

/-!
# The class of a right standard module at a row loading

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5,
Definition 5.1 and Proposition 5.6, for right modules. The standard module `e(s) T / U_s` at the
row loading `s` of `u_1, …, u_ℓ`, a graded right `T^λ`-module (`rightRowStandard`), is the right
twist of the left standard module by horizontal reflection (`rightStandardIso`). Hence its class
functional on projective classes, through Webster's identification `η` of Theorem 4.38 for right
projectives, is the form against `F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}`
(`classFunctional_rightRowStandard`).
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)
    (wt : Fin ℓ → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2)
  (dotDegree C hQ)
local notation "Kr" => rightTensorProjectiveGroup C hQ Λ
local notation "η'" => rightTensorModuleEquiv C hQ hR Λ wt hwt
local notation "B" => TensorPairing.orderedForm hR wt

/-- The standard module of Definition 5.1 at the row loading of `u`, as a finite-dimensional
graded right `T^λ`-module. -/
def rightRowStandard (u : Fin ℓ → List I) :
    GFin (oppositeGrade (tensorProductGrade G (blockContent u))) :=
  let := tensorProductAlgebra_finite Λ (blockContent u) hQ
  BraidedStendhalAlgebra.rightStandard (isReducedChoice_canChoice _) hQ.klrSymm
    (rowLoading ℓ u) (iteratedGrading C hQ Λ)
    ((redWord_eq_finRange_iff _).2 (isRedOrdered_rowLoading ℓ u))

variable [∀ ν : Multiset I, Module.Finite k (TensorProductAlgebra k Q Λ ν)ᵐᵒᵖ]

/-- **Proposition 5.6 for right standard modules** (Webster, arXiv:1309.3796v2, Definition 5.1
and Proposition 5.6). On every virtual right projective class `x` of black content `|u|`, the
class functional of the right standard module at the row loading of `u` is the form against
`F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_ℓ} v_{λ_ℓ}`. -/
theorem classFunctional_rightRowStandard (u : Fin ℓ → List I) (x : Kr (blockContent u)) :
    classFunctional C hQ hR Λ wt hwt (blockContent u) (rightRowStandard C hQ Λ u)
        (η' (DirectSum.lof LP _ Kr (blockContent u) x)) =
      B (wordTensor C wt u) (η' (DirectSum.lof LP _ Kr (blockContent u) x)) := by
  let := tensorProductAlgebra_finite Λ (blockContent u) hQ
  have hs := isRedOrdered_rowLoading ℓ u
  let ψ := tensorReflectionG C hQ Λ (blockContent u)
  obtain ⟨y, rfl⟩ := (K0.rightTwistEquiv ψ).surjective x
  have he : (η' (DirectSum.lof LP _ Kr (blockContent u) (K0.rightTwistEquiv ψ y)) :
      TensorSpace wt) = tensorModuleEquiv C hQ hR Λ wt hwt
        (DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ) (blockContent u) y) := by
    have hr : (tensorReflectionK0 C hQ Λ).symm
        (DirectSum.lof LP _ Kr (blockContent u) (K0.rightTwistEquiv ψ y)) =
          DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ) (blockContent u) y := by
      rw [LinearEquiv.symm_apply_eq, tensorReflectionK0_lof]
    change (tensorModuleEquiv C hQ hR Λ wt hwt ((tensorReflectionK0 C hQ Λ).symm _) :
      TensorSpace wt) = _
    rw [hr]
  have hc : projectiveHomPolynomial _ (rightRowStandard C hQ Λ u) =
      projectiveHomPolynomial _ ((leftStandardGFin G (rowLoading ℓ u) hs).rightTwist ψ) :=
    (projectiveHomPolynomial_congr _ (BraidedStendhalAlgebra.rightStandardIso
      (isReducedChoice_canChoice _) hQ.klrSymm G
      (stendhalGradingDatum_degΨ_symm C hQ Λ) hs ((redWord_eq_finRange_iff _).2 hs))).symm
  rw [classFunctional_eta, DirectSum.lof_apply, hc, projectiveHomPolynomial_rightTwist, he]
  have h56 := rowStandard_projectiveCharacter_eq C hQ hR ℓ Λ u wt hwt y
  change qToV (LaurentPolynomial.invert (projectiveHomPolynomial _ _ y)) = _ at h56
  rw [← CycKLR.integralEval_invert, LaurentPolynomial.involutive_invert] at h56
  exact h56
