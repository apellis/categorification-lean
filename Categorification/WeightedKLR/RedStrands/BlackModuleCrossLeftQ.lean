/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossLeft
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackActionQ
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossTransportQ
import Categorification.WeightedKLR.RedStrands.BlackModuleEFLeftQ

/-!
# The commutation of `Eⱼ` and `Fᵢ` on left modules over `T^λ`, for `i ≠ j`

The relation `Eⱼ Fᵢ ≅ Fᵢ Eⱼ` (`i ≠ j`) of the categorical action (Webster, arXiv:1309.3796v3,
Theorem 4.31) on all left modules over the tensor product algebra `T^λ` at standard
Khovanov–Lauda black scalars, an input of the dimension count in the proof of Proposition 5.5
there (`clLeftBlackModuleCrossEquivQ`). It is the statement on right modules
(`clBlackModuleCrossEquivQ`) transported along the horizontal reflection (`FlipView`).

This is the version of `BlackModuleCrossLeft` in which the black strands carry the relations of
Cautis–Lauda's `U_Q(g)` (arXiv:1111.1431v3, Definition 1.1, `r = 1`; `CLQ.pres RD k sc`) instead
of the KL III relations. Each declaration carries the suffix `Q`.
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

end Flip

section CL

variable {I : Type u} {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {C : CartanDatum I}
  {k : Type u} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {hQ : IsRouquierQ C Q}

local notation "KL" => blackScalarsQ Λ C hQ

variable {P : Presentation.{u, u}
    (signature (coordinateDatum Λ C) (redWeight (cyclotomicCoverWeightDatum Λ C))) k}
  (hP : CoverRelsNegligible.{u, u, w} Λ C hQ (coverDotCentral Λ C hQ)
    (blockWeight (cyclotomicCoverWeightDatum Λ C) (cyclotomicCoverHighest (I := I) (ℓ := ℓ)) 0 :
      I ⊕ Fin ℓ → ℤ) P)
  (hwf : P.WFDom)
  (i j : I) (ρ : Multiset I)

local notation "Sj" => (Singleton.singleton j : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)

variable (M : Type u) [AddCommGroup M]
  [Module (TensorProductAlgebra k (Q) Λ ({j} + ρ)) M]

local notation "FV" => FlipView (Q) Λ (Sj + ρ) M

/-- **`Eⱼ Fᵢ` against `Fᵢ Eⱼ` on left `T^λ`-modules**, `i ≠ j` (Webster, arXiv:1309.3796v3,
Theorem 4.31, input of the proof of Proposition 5.5): for every left `T^λ_{j+ρ}`-module `M`,
`Eⱼ Fᵢ M ≅ Fᵢ Eⱼ M` as left `T^λ_{i+ρ}`-modules. -/
def clLeftBlackModuleCrossEquivQ (hji : j ≠ i) :=
  resIndCrossEquivTransport (tensorFlipRingEquiv (Q := Q) (Λ := Λ) ρ)
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Sj + ρ))
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + ρ))
    (tensorFlipRingEquiv (Q := Q) (Λ := Λ) (Si + (Sj + ρ)))
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ ρ j)
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ (Sj + ρ) i)
    (appendBlackOp_tensorFlipRingEquiv (Q) Λ ρ i)
    (appendBlackOpOfEq_tensorFlipRingEquiv (Q) Λ j (cross_content i j ρ))
    (toFlipView (Q) Λ (Sj + ρ) M) (toFlipView_smul (Q) Λ (Sj + ρ) M)
    (clBlackModuleCrossEquivQ hP hwf i j ρ FV hji)

end CL

end Categorification.Stendhal
