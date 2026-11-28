/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackRouqModuleSigma
import Categorification.Algebra.InductionAlongDotMate
import Categorification.TwoRep.SumInvPointwise

/-!
# The dotted caps and cups of black induction on modules

Brundan, arXiv:1501.00350v1, (1.8) and (1.9), for the black induction functors `Fᵢ ⊣ Eᵢ` on right
`T^λ`-modules (Webster, arXiv:1309.3796v3, §4.6), with the dot on `Fᵢ` the mate of the dot on
`Eᵢ` (`indDotOfEq`):

* `indDotOfEq_self_app`: the dot on `Fᵢ M` is right multiplication `z ⊗ m ↦ z x ⊗ m` by the dot
  `x = appendedDot` on the new strand;
* `blackDottedCap_app` and `blackDottedCup_app`: the dotted counit `Eᵢ x^m ε` is
  `z ⊗ m ↦ z x^m m`, and the dotted unit `η x^m Eᵢ` is `m ↦ φ(1) x^m ⊗ m`;
* `blackModuleSumInvTo`, `blackModuleSumInvFrom`: explicit inverses on each module give explicit
  inverses of `(σ, Eᵢ x^m ε)` and `(σ, η x^m Eᵢ)` in the functor category, with
  `σ = blackModuleSigma`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory MulOpposite InductionAlong KLR TwoRep

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 2000] InductionAlong.instModuleInd InductionAlong.Res.instModule

universe u

variable {I : Type u} [DecidableEq I] {k : Type u} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin ℓ → I →₀ ℕ)

/-- **The dot on black induction acts by the new dot**: `z ⊗ m ↦ z x ⊗ m`. -/
theorem indDotOfEq_self_app (i : I) (μ : Multiset I)
    (N : ModuleCat.{u} (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ) :
    (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _)).app N =
      by exact ModuleCat.ofHom (natMap (N := N)
        (φ := appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _))
        (intertwines_of_commute (op_appendedDot_commute Q Λ i μ))) :=
  conjugateEquiv_symm_resAct_app (op_appendedDot_commute Q Λ i μ) _ (fun _ => rfl) N

/-- The powers of the dot on black induction. -/
theorem powComp_indDotOfEq_self_app (i : I) (μ : Multiset I)
    (N : ModuleCat.{u} (TensorProductAlgebra k Q Λ μ)ᵐᵒᵖ) (m : ℕ) :
    (powComp (indDotOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _)) m).app N =
      by exact ModuleCat.ofHom ((natMap (N := N)
        (φ := appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _))
        (intertwines_of_commute (op_appendedDot_commute Q Λ i μ))) ^ m : Module.End _ _) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [powComp_succ, NatTrans.comp_app, ih, indDotOfEq_self_app, pow_succ']
    rfl

/-- **The dotted counit on modules**: `Eᵢ x^m ε` is `z ⊗ m ↦ z x^m m`. -/
theorem blackDottedCap_app (i : I) (μ : Multiset I) (m : ℕ)
    (M : ModuleCat.{u} (TensorProductAlgebra k Q Λ ({i} + μ))ᵐᵒᵖ) :
    (Functor.whiskerLeft (blackEOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _))
        (powComp (indDotOfEq Q Λ i rfl) m) ≫ (blackAdjOfEq Q Λ i rfl).counit).app M =
      by exact ModuleCat.ofHom (counitMap
        (φ := appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _)) M ∘ₗ
        ((natMap (intertwines_of_commute (op_appendedDot_commute Q Λ i μ))) ^ m :
          Module.End _ _)) := by
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, powComp_indDotOfEq_self_app]
  rfl

/-- **The dotted unit on modules**: `η x^m Eᵢ` is `m ↦ φ(1) x^m ⊗ m`. -/
theorem blackDottedCup_app (i : I) (μ : Multiset I) (m : ℕ)
    (M : ModuleCat.{u} (TensorProductAlgebra k Q Λ ({i} + μ))ᵐᵒᵖ) :
    ((blackAdjOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _)).unit ≫
        Functor.whiskerRight (powComp (indDotOfEq Q Λ i rfl) m) (blackEOfEq Q Λ i rfl)).app M =
      by exact ModuleCat.ofHom (Res.map
        ((natMap (intertwines_of_commute (op_appendedDot_commute Q Λ i ({i} + μ)))) ^ m :
          Module.End _ _) ∘ₗ
        unitMap (φ := appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _)) M) := by
  rw [NatTrans.comp_app, Functor.whiskerRight_app, powComp_indDotOfEq_self_app]
  rfl

/-- **Brundan (1.8) for black induction, from each module**: explicit inverses of
`(sigmaLin, z ⊗ m ↦ z x^m m)` on every module give an explicit inverse of
`(blackModuleSigma, Eᵢ x^m ε)` in the functor category. -/
def blackModuleSumInvTo (hsym : KLRSymm Q) (i : I) (μ : Multiset I) {n : ℕ}
    (S : ∀ M : ModuleCat.{u} (TensorProductAlgebra k Q Λ ({i} + μ))ᵐᵒᵖ,
      SumInvTo
        (X := ModuleCat.of _ (Ind (Res (appendBlackOpOfEq Q Λ i
          (rfl : ({i} : Multiset I) + μ = _)) M) (appendBlackOpOfEq Q Λ i rfl)))
        (Y := ModuleCat.of _ (Res (appendBlackOpOfEq Q Λ i
          (rfl : ({i} : Multiset I) + ({i} + μ) = _)) (Ind M (appendBlackOpOfEq Q Λ i rfl))))
        (Z := M)
        (ModuleCat.ofHom (sigmaLin (appendBlackOpOfEq Q Λ i rfl) (appendBlackOpOfEq Q Λ i rfl)
          (op_appendedCross_commute Q Λ i μ) M))
        (fun m => ModuleCat.ofHom (counitMap (φ := appendBlackOpOfEq Q Λ i rfl) M ∘ₗ
          ((natMap (intertwines_of_commute (op_appendedDot_commute Q Λ i μ))) ^ m :
            Module.End _ _))) n) :
    SumInvTo (blackModuleSigma Λ hsym i μ)
      (fun m => Functor.whiskerLeft (blackEOfEq Q Λ i (rfl : ({i} : Multiset I) + μ = _))
        (powComp (indDotOfEq Q Λ i rfl) m) ≫ (blackAdjOfEq Q Λ i rfl).counit) n :=
  SumInvTo.ofApp fun M => (S M).congr (blackModuleSigma_app Λ hsym i μ M).symm
    (funext fun m => (blackDottedCap_app Λ i μ m M).symm) rfl

/-- **Brundan (1.9) for black induction, from each module**: explicit inverses of
`(sigmaLin, m ↦ φ(1) x^m ⊗ m)` on every module give an explicit inverse of
`(blackModuleSigma, η x^m Eᵢ)` in the functor category. -/
def blackModuleSumInvFrom (hsym : KLRSymm Q) (i : I) (μ : Multiset I) {n : ℕ}
    (S : ∀ M : ModuleCat.{u} (TensorProductAlgebra k Q Λ ({i} + μ))ᵐᵒᵖ,
      SumInvFrom
        (X := ModuleCat.of _ (Res (appendBlackOpOfEq Q Λ i
          (rfl : ({i} : Multiset I) + ({i} + μ) = _)) (Ind M (appendBlackOpOfEq Q Λ i rfl))))
        (Y := ModuleCat.of _ (Ind (Res (appendBlackOpOfEq Q Λ i
          (rfl : ({i} : Multiset I) + μ = _)) M) (appendBlackOpOfEq Q Λ i rfl)))
        (Z := M)
        (ModuleCat.ofHom (sigmaLin (appendBlackOpOfEq Q Λ i rfl) (appendBlackOpOfEq Q Λ i rfl)
          (op_appendedCross_commute Q Λ i μ) M))
        (fun m => ModuleCat.ofHom (Res.map
          (φ := appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _))
          ((natMap (N := M)
          (φ := appendBlackOpOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _))
          (intertwines_of_commute (op_appendedDot_commute Q Λ i ({i} + μ)))) ^ m :
            Module.End _ _) ∘ₗ unitMap (φ := appendBlackOpOfEq Q Λ i rfl) M)) n) :
    SumInvFrom (blackModuleSigma Λ hsym i μ)
      (fun m => (blackAdjOfEq Q Λ i (rfl : ({i} : Multiset I) + ({i} + μ) = _)).unit ≫
        Functor.whiskerRight (powComp (indDotOfEq Q Λ i rfl) m) (blackEOfEq Q Λ i rfl)) n :=
  SumInvFrom.ofApp fun M => (S M).congr (blackModuleSigma_app Λ hsym i μ M).symm
    (funext fun m => (blackDottedCup_app Λ i μ m M).symm) rfl

end Categorification.Stendhal
