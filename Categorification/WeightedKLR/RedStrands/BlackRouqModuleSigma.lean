/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqBlocks
import Categorification.Algebra.InductionAlongSigma

/-!
# Rouquier's rightward crossing for black induction on modules

Brundan, arXiv:1501.00350v1, (1.6), for the black induction functors on right `T^λ`-modules
(Webster, arXiv:1309.3796v3, §4.6): `blackModuleSigma`, the rightward crossing `Eᵢ Fᵢ ⟶ Fᵢ Eᵢ`
built from the unit and counit of `Fᵢ ⊣ Eᵢ` (`blackAdjOfEq`) and the same-colour crossing on
inductions (`indCrossOfEq`, the mate of the action of `-ψ`). It is definitionally the
transformation of `InductionAlong.sigma_app` for induction along `appendBlackOpOfEq`
(`blackModuleSigma_eq`), and `resCrossOfEq_self_app` is the hypothesis of that lemma: the
same-colour crossing on restrictions is `resAct₂` of minus the crossing of the two newest black
strands. Together they identify `blackModuleSigma` on each module with
`InductionAlong.sigmaLin`, the module side of `MatEnd.resIndModuleEquiv_sigmaLin`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR


attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 2000] InductionAlong.instModuleInd InductionAlong.Res.instModule

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

/-- Rouquier's rightward crossing `Eᵢ Fᵢ ⟶ Fᵢ Eᵢ` for black induction on modules of content
`{i} + μ`, as a transformation of functors (unit, crossing, counit). -/
def blackModuleSigma (hsym : KLRSymm Q) (i : I) (μ : Multiset I) :
    blackEOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _) ⋙ blackFOfEq Q Λ i rfl ⟶
      blackFOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _) ⋙ blackEOfEq Q Λ i rfl :=
  Functor.whiskerLeft (blackEOfEq Q Λ i rfl ⋙ blackFOfEq Q Λ i rfl)
      (blackAdjOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _)).unit ≫
    Functor.whiskerRight (Functor.whiskerLeft (blackEOfEq Q Λ i rfl)
      (indCrossOfEq Λ hsym i i rfl rfl rfl rfl)) (blackEOfEq Q Λ i rfl) ≫
    Functor.whiskerRight (blackAdjOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _)).counit
      (blackFOfEq Q Λ i rfl ⋙ blackEOfEq Q Λ i rfl)

/-- **The same-colour crossing on restrictions acts by minus the crossing of the two newest
black strands** (`resAct₂`), the hypothesis `hτ` of `InductionAlong.sigma_app`. With
`op_appendedCross_commute` and `op_appendedCross_fix`, `InductionAlong.sigma_app` identifies
`blackModuleSigma` on each module with `InductionAlong.sigmaLin` for `c = op appendedCross`. -/
theorem resCrossOfEq_self_app (hsym : KLRSymm Q) (i : I) (μ : Multiset I)
    (M : ModuleCat.{u} (TensorProductAlgebra k Q Λ ({i} + ({i} + μ)))ᵐᵒᵖ) :
    resAct₂ (op (appendedCross Q Λ i μ)) (op_appendedCross_fix Q Λ i μ)
        (op_appendedCross_commute Q Λ i μ) M =
      ((resCrossOfEq Λ hsym i i (rfl : ({i} : Multiset I) + μ = _) rfl rfl rfl).app M).hom := by
  rw [resCrossOfEq_self]
  rfl

/-- `blackModuleSigma` is the transformation of `InductionAlong.sigma_app` for induction along
`appendBlackOpOfEq`, with `τ = resCrossOfEq` (definitional). -/
theorem blackModuleSigma_eq (hsym : KLRSymm Q) (i : I) (μ : Multiset I) :
    blackModuleSigma Λ hsym i μ =
      Functor.whiskerLeft (resFunctor (appendBlackOpOfEq Q Λ i
          (rfl : ({i} : Multiset I) + μ = _)) ⋙ functor (appendBlackOpOfEq Q Λ i rfl))
        (adjunction.{u, u} (appendBlackOpOfEq Q Λ i
          (rfl : ({i} : Multiset I) + ({i} + μ) = _))).unit ≫
      Functor.whiskerRight (Functor.whiskerLeft (resFunctor (appendBlackOpOfEq Q Λ i rfl))
        ((conjugateEquiv ((adjunction.{u, u} (appendBlackOpOfEq Q Λ i rfl)).comp
            (adjunction.{u, u} (appendBlackOpOfEq Q Λ i rfl)))
          ((adjunction (appendBlackOpOfEq Q Λ i rfl)).comp
            (adjunction (appendBlackOpOfEq Q Λ i rfl)))).symm
          (resCrossOfEq Λ hsym i i rfl rfl rfl rfl)))
        (resFunctor (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _))) ≫
      Functor.whiskerRight (adjunction.{u, u} (appendBlackOpOfEq Q Λ i
          (rfl : ({i} : Multiset I) + μ = _))).counit
        (functor (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _)) ⋙
          resFunctor (appendBlackOpOfEq Q Λ i rfl)) :=
  rfl

/-- **Rouquier's rightward crossing for black induction is `sigmaLin`**: on each module,
`blackModuleSigma` is `z ⊗ m ↦ z · appendedCross ⊗ m` (`InductionAlong.sigmaLin` for
`c = op appendedCross`), by `InductionAlong.sigma_app`. The right side is elaborated with
`by exact` so that the instances on `Res`/`Ind` are unified against the left side. -/
theorem blackModuleSigma_app (hsym : KLRSymm Q) (i : I) (μ : Multiset I)
    (M : ModuleCat.{u} (TensorProductAlgebra k Q Λ ({i} + μ))ᵐᵒᵖ) :
    (blackModuleSigma Λ hsym i μ).app M =
      by exact ModuleCat.ofHom (sigmaLin
        (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _))
        (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _))
        (op_appendedCross_commute Q Λ i μ) M) := by
  have hτ : ∀ N : ModuleCat.{u} (TensorProductAlgebra k Q Λ ({i} + ({i} + μ)))ᵐᵒᵖ,
      (resCrossOfEq Λ hsym i i (rfl : ({i} : Multiset I) + μ = _) rfl rfl rfl).app N =
        by exact ModuleCat.ofHom (resAct₂ (op (appendedCross Q Λ i μ))
          (op_appendedCross_fix Q Λ i μ) (op_appendedCross_commute Q Λ i μ) N) := by
    intro N
    ext x
    exact (congrArg (fun f => f x) (resCrossOfEq_self_app Λ hsym i μ N)).symm
  have key := sigma_app (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _))
    (appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _))
    (op_appendedCross_commute Q Λ i μ) (op_appendedCross_fix Q Λ i μ) _ hτ M
  rw [blackModuleSigma_eq]
  exact key

end Categorification.Stendhal
