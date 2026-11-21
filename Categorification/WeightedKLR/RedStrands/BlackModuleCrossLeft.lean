/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossTransport
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeft

/-!
# The commutation of `Eⱼ` and `Fᵢ` on left modules over `T^λ`, for `i ≠ j`

The relation `Eⱼ Fᵢ ≅ Fᵢ Eⱼ` (`i ≠ j`) of the categorical action (Webster, arXiv:1309.3796v3,
Theorem 4.31) on all left modules over the tensor product algebra `T^λ` at standard
Khovanov–Lauda black scalars, an input of the dimension count in the proof of Proposition 5.5
there (`clLeftBlackModuleCrossEquiv`). It is the statement on right modules
(`clBlackModuleCrossEquiv`) transported along the horizontal reflection (`FlipView`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory CategoryTheory.Idempotents QuantumGroup QuantumGroup.UDot StringDiagrams
  KLR TwoRep CyclotomicAction DoubleDiagram KL3.Diagram InductionAlong MulOpposite

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u w

section Flip

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)

/-- `appendBlackNU` with the content of the target given by an equality. -/
def appendBlackNUOfEq (j : I) {μ ν' : Multiset I} (hc : {j} + μ = ν') :
    TensorProductAlgebra k Q Λ μ →ₙ+* TensorProductAlgebra k Q Λ ν' :=
  hc ▸ appendBlackNU (Q := Q) (Λ := Λ) j μ

theorem appendBlackOpOfEq_tensorFlipRingEquiv (j : I) {μ ν' : Multiset I}
    (hc : {j} + μ = ν') (t : TensorProductAlgebra k Q Λ μ) :
    appendBlackOpOfEq Q Λ j hc (tensorFlipRingEquiv (Q := Q) (Λ := Λ) μ t) =
      tensorFlipRingEquiv (Q := Q) (Λ := Λ) ν' (appendBlackNUOfEq Q Λ j hc t) := by
  subst hc
  exact appendBlackOp_tensorFlipRingEquiv Q Λ μ j t

end Flip

section CL

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => (CL.CLScalars.kl : CL.CLScalars C k)

variable (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
  {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i j : I) (ρ : Multiset I)

local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ ({j} + ρ)) M]

local notation "FV" => FlipView (CL.qCL KL) Λ (Sj + ρ) M

/-- **`Eⱼ Fᵢ` against `Fᵢ Eⱼ` on left `T^λ`-modules**, `i ≠ j` (Webster, arXiv:1309.3796v3,
Theorem 4.31, input of the proof of Proposition 5.5): for every left `T^λ_{j+ρ}`-module `M`,
`Eⱼ Fᵢ M ≅ Fᵢ Eⱼ M` as left `T^λ_{i+ρ}`-modules. -/
def clLeftBlackModuleCrossEquiv (hji : j ≠ i) :=
  resIndCrossEquivTransport (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) ρ)
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Sj + ρ))
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + ρ))
    (tensorFlipRingEquiv (Q := CL.qCL KL) (Λ := Λ) (Si + (Sj + ρ)))
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ ρ j)
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ (Sj + ρ) i)
    (appendBlackOp_tensorFlipRingEquiv (CL.qCL KL) Λ ρ i)
    (appendBlackOpOfEq_tensorFlipRingEquiv (CL.qCL KL) Λ j (cross_content i j ρ))
    (toFlipView (CL.qCL KL) Λ (Sj + ρ) M) (toFlipView_smul (CL.qCL KL) Λ (Sj + ρ) M)
    (clBlackModuleCrossEquiv hstd hP hwf i j ρ FV hji)

end CL

end Categorification.Stendhal
