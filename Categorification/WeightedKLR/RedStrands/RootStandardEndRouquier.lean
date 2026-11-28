/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.RootStandardEnd
import Categorification.KLR.Rouquier.PolynomialDegree
import Categorification.QuantumGroup.UDotWords

/-!
# `End(S_α)` and full faithfulness for Rouquier parameters

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 5.26, at Webster's parameters: `Q` comes from a Cartan datum (`IsRouquierQ`). The
grading of Definition 4.4 (dots of colour `i` in degree `⟨α_i, α_i⟩`, red dots in degree `2`) has
dots of positive degree, so the results of `RootStandardEnd` hold with no further hypothesis.

## Main results

* `StendhalAlgebra.bijective_blockAction_of_isRouquierQ`,
  `StendhalAlgebra.blockActionEquivOfIsRouquierQ`: `End_{T̃^λ}(S_α) ≅ R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯`.
* `StendhalAlgebra.standardizationMap_bijective_of_isRouquierQ`: full faithfulness of the
  standardization of Definition 5.4.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR StendhalAlgebra QuantumGroup MulOpposite

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {C : CartanDatum I}
  {Q : I → I → MvPolynomial (Fin 2) k} (hR : IsRouquierQ C Q)

/-- The grading of `T̃^λ` of arXiv:1309.3796v3, Definition 4.4, for Rouquier parameters. -/
abbrev rouquierStendhalGrading {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) : GradingDatum (stendhalQ Q Λ) :=
  stendhalGradingDatum Λ hR.gradingDatum (UDot.di C)
    (fun i => (hR.gradingDatum_degX i).trans (UDot.two_mul_di C i).symm)

omit [DecidableEq I] in
theorem rouquierStendhalGrading_degX_pos {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (a : I ⊕ Fin ℓ) :
    0 < (rouquierStendhalGrading hR Λ).degX a := by
  rcases a with i | s
  · change 0 < hR.gradingDatum.degX i
    rw [hR.gradingDatum_degX, ← UDot.two_mul_di C i]
    have := UDot.di_pos C i
    omega
  · change (0 : ℤ) < 2
    norm_num

variable {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I} {b : Fin (ℓ + 1) → Multiset I}

include hR in
/-- **Proposition 5.26 of arXiv:1309.3796v3, `End(S_α)`**, at Rouquier parameters: the block
action is a bijection from `R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_ℓ}(b_ℓ)` onto `End_{T̃^λ}(S_α)`. -/
theorem bijective_blockAction_of_isRouquierQ (hb : blockPrefix b (ℓ + 1) = ν) :
    Function.Bijective (blockAction Q Λ hb) :=
  bijective_blockAction hR.klrSymm (rouquierStendhalGrading hR Λ)
    (rouquierStendhalGrading_degX_pos hR Λ) hb

/-- **Proposition 5.26 of arXiv:1309.3796v3** at Rouquier parameters: `End_{T̃^λ}(S_α) ≅
R(b_0) ⊗ R^{λ_1}(b_1) ⊗ ⋯ ⊗ R^{λ_ℓ}(b_ℓ)` through the block action. -/
def blockActionEquivOfIsRouquierQ (hb : blockPrefix b (ℓ + 1) = ν) :
    BlockAlgebra k Q Λ b ≃ₐ[k]
      Module.End (StendhalAlgebra k Q Λ ν)ᵐᵒᵖ (rootStandard (ν := ν) Q Λ (blockRoot b)) :=
  blockActionEquiv hR.klrSymm (rouquierStendhalGrading hR Λ)
    (rouquierStendhalGrading_degX_pos hR Λ) hb

theorem blockActionEquivOfIsRouquierQ_apply (hb : blockPrefix b (ℓ + 1) = ν)
    (β : BlockAlgebra k Q Λ b) :
    blockActionEquivOfIsRouquierQ hR hb β = blockAction Q Λ hb β :=
  rfl

include hR in
/-- **Proposition 5.26 of arXiv:1309.3796v3, full faithfulness of the standardization of
Definition 5.4**, at Rouquier parameters: `g ↦ g ⊗ 1` is a bijection
`Hom_B(M, M') ≅ Hom_{T̃^λ}(M ⊗_B S_α, M' ⊗_B S_α)` for right modules over the block algebra. -/
theorem standardizationMap_bijective_of_isRouquierQ (M M' : Type*) [AddCommGroup M] [Module k M]
    [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M] [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
    [AddCommGroup M'] [Module k M'] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M']
    [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M'] :
    Function.Bijective
      (fun g : M →ₗ[(BlockAlgebra k Q Λ b)ᵐᵒᵖ] M' => standardizationMap (Q := Q) (Λ := Λ) g) :=
  standardizationMap_bijective hR.klrSymm (rouquierStendhalGrading hR Λ)
    (rouquierStendhalGrading_degX_pos hR Λ) M M'

end StendhalAlgebra

end Categorification.Stendhal
