/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackMixedRelations
import Categorification.WeightedKLR.RedStrands.BlackModuleCrossTransport

/-!
# The mixed crossing between arbitrary contents

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6; the
crossing `τ_{ij}` of Rouquier's definition (arXiv:0812.5023, §4.1.2; Brundan,
arXiv:1501.00350v1, Definition 1.1), whose source and target are `Eⱼ Eᵢ` and `Eᵢ Eⱼ` at
contents related by equalities, as in `TwoRep.RouqData.cross`.

`Eᵢ` out of a content `β` given by an equality `{i} + μ = β` is restriction along
`appendBlackOpOfEq` (`blackEOfEq`). For contents `h₁ : {j} + μ = β₁`, `h₂ : {i} + β₁ = δ`,
`h₃ : {i} + μ = β₂` and `h₄ : {j} + β₂ = δ`, `blackMixedCrossOfEq` is the mixed crossing
`blackMixedCross` transported along the equalities. The restriction `Eⱼ'` of
`BlackMixedCrossing` is `Eⱼ` at the equality `mixedSwap` (`blackEAt_eq`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

theorem castOp_op {ν ν' : Multiset I} (h : ν = ν') (a : TensorProductAlgebra k Q Λ ν) :
    castOp Q Λ h (op a) = op (castTensorProductAlgebra Q Λ h a) := by
  subst h; rfl

variable (Q) in
/-- `Eᵢ` out of the content `β`, given by an equality `{i} + μ = β`: restriction along
`appendBlackOpOfEq`. -/
def blackEOfEq (i : I) {μ β : Multiset I} (h : ({i} : Multiset I) + μ = β) :
    ModuleCat.{u} (TensorProductAlgebra k Q Λ β)ᵐᵒᵖ ⥤
      ModuleCat.{u} (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ :=
  resFunctor.{u, u} (appendBlackOpOfEq Q Λ i h)

variable (Q) in
theorem blackEOfEq_rfl (i : I) (μ : Multiset I) :
    blackEOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _) = blackE Q Λ i μ :=
  rfl

variable (ν : Multiset I) (i j : I)

theorem appendBlackAtOp_eq :
    appendBlackAtOp (Q := Q) Λ ν i j = appendBlackOpOfEq Q Λ j (mixedSwap ν i j) := by
  ext a
  induction a using MulOpposite.rec' with | h a => ?_
  change op (appendBlackAt Λ j (mixedSwap ν i j) a) =
      castOp Q Λ (mixedSwap ν i j) (op (appendBlack Q Λ j ({i} + ν) a))
  rw [castOp_op, cast_appendBlack_mixed]

/-- `Eⱼ'` is `Eⱼ` at the equality `mixedSwap`. -/
theorem blackEAt_eq : blackEAt (Q := Q) Λ ν i j = blackEOfEq Q Λ j (mixedSwap ν i j) := by
  rw [blackEAt, appendBlackAtOp_eq]
  rfl

variable {Λ ν i j}

/-- **The mixed crossing between arbitrary contents** (Rouquier's `τ_{ij}`, `i ≠ j`;
cf. `TwoRep.RouqData.cross`): `Eⱼ Eᵢ ⟶ Eᵢ Eⱼ`, where `Eᵢ` runs along `h₂`, then `Eⱼ` along
`h₁`, and `Eⱼ` along `h₄`, then `Eᵢ` along `h₃`. -/
def blackMixedCrossOfEq (hsym : KLRSymm Q) (hij : i ≠ j) {μ β₁ β₂ δ : Multiset I}
    (h₁ : ({j} : Multiset I) + μ = β₁) (h₂ : ({i} : Multiset I) + β₁ = δ)
    (h₃ : ({i} : Multiset I) + μ = β₂) (h₄ : ({j} : Multiset I) + β₂ = δ) :
    blackEOfEq Q Λ i h₂ ⋙ blackEOfEq Q Λ j h₁ ⟶ blackEOfEq Q Λ j h₄ ⋙ blackEOfEq Q Λ i h₃ := by
  subst h₁ h₂ h₃
  exact blackMixedCross (ν := μ) hsym hij ≫ eqToHom (by rw [blackEAt_eq]; rfl)

theorem blackMixedCrossOfEq_rfl (hsym : KLRSymm Q) (hij : i ≠ j) :
    blackMixedCrossOfEq (Λ := Λ) hsym hij rfl rfl rfl (mixedSwap ν i j) =
      blackMixedCross hsym hij ≫ eqToHom (by rw [blackEAt_eq]; rfl) :=
  rfl

end Categorification.Stendhal
