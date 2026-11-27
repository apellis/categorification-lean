/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlackResCast
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastOneBlockLinear
import Categorification.Algebra.AlgebraFamilyCastEquiv

/-!
# Transports along equal weights in the `Eᵢ`-filtration

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. Bookkeeping for the induction on the number of red strands: `Eᵢ` of an
isomorphism (`blackResCongr`); the standardizations `S N` and `S(₂Eᵢ N)` over the tensor
product algebras at the weights of the sequences of Proposition 5.5 are transports of the
standardization action (`leftStandardTEquiv`, `rightStandardTEquiv`, `lastBlackTwoTEquiv`,
`lastBlackOneTEquiv`); and `₂Eᵢ` commutes with the transport of the factor algebras along an
equality of the left weight (`rightResRightFactorCast`). All these are the identity on
elements, so they commute with every map induced by an endomorphism.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra StendhalAlgebra InductionAlong
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ}

section BlackResCongr

variable {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} (i : I) {ν : Multiset I}
  {M : Type} [AddCommGroup M] [Module k M]
  [Module (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M]
  [IsScalarTower k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M]
  {M' : Type} [AddCommGroup M'] [Module k M']
  [Module (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M']
  [IsScalarTower k (TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)) M']

/-- **`Eᵢ` of an isomorphism.** -/
def blackResCongr (e : M ≃ₗ[TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)] M') :
    BlackRes (Q := Q) (Λ := Λ) i ν M ≃ₗ[TensorProductAlgebra k Q Λ ν]
      BlackRes (Q := Q) (Λ := Λ) i ν M' :=
  { blackResMap i e.toLinearMap with
    invFun := blackResMap i e.symm.toLinearMap
    left_inv := fun m => Subtype.ext (e.symm_apply_apply m.1)
    right_inv := fun m => Subtype.ext (e.apply_symm_apply m.1) }

@[simp] theorem blackResCongr_val
    (e : M ≃ₗ[TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)] M')
    (m : BlackRes (Q := Q) (Λ := Λ) i ν M) : (blackResCongr i e m).1 = e m.1 := rfl

@[simp] theorem blackResCongr_symm_val
    (e : M ≃ₗ[TensorProductAlgebra k Q Λ (({i} : Multiset I) + ν)] M')
    (m : BlackRes (Q := Q) (Λ := Λ) i ν M') : ((blackResCongr i e).symm m).1 = e.symm m.1 := rfl

end BlackResCongr

section StandardT

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  (hQ : KLRSymm Q)

local notation "Tfam" => TensorProductAlgebra k Q Λ

section Left

variable (θ₀ β : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) β) N]

/-- **`S N` over `T(i + (θ₀ + β))` is the transport of `S N` over `T(θ + β)`** (`i ∉ β`). -/
def leftStandardTEquiv :
    LeftStandardT Q Λ i θ₀ β N hQ ≃ₗ[Tfam (({i} : Multiset I) + (θ₀ + β))]
      FamilyCast Tfam (leftBlack_weight i θ₀ β).symm
        (ParabolicStandardT Q Λ (({i} : Multiset I) + θ₀) β N hQ) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' t m := by
    change leftStandardTAction Q Λ i θ₀ β N hQ t m =
      parabolicStandardAction Q Λ _ _ N hQ ((familyRingCast Tfam
        (leftBlack_weight i θ₀ β).symm).symm t) m
    rw [familyRingCast_symm_eq_castTensorProductAlgebra]
    rfl

end Left

section Right

variable (θ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)) N]

/-- **`S N` over `T(i + (θ + β₀))` is the transport of `S N` over `T(θ + β)`** (`i ∉ θ`). -/
def rightStandardTEquiv :
    RightStandardT Q Λ i θ β₀ N hQ ≃ₗ[Tfam (({i} : Multiset I) + (θ + β₀))]
      FamilyCast Tfam (rightBlack_weight i θ β₀).symm
        (ParabolicStandardT Q Λ θ (({i} : Multiset I) + β₀) N hQ) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' t m := by
    change rightStandardTAction Q Λ i θ β₀ N hQ t m =
      parabolicStandardAction Q Λ _ _ N hQ ((familyRingCast Tfam
        (rightBlack_weight i θ β₀).symm).symm t) m
    rw [familyRingCast_symm_eq_castTensorProductAlgebra]
    rfl

end Right

section Last

variable (θ₀ β₀ : Multiset I) (N : Type) [AddCommGroup N] [Module k N]
  [Module (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) ({i} + β₀)) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ (({i} : Multiset I) + θ₀) ({i} + β₀)) N]

/-- **`S(₂Eᵢ N)` over `T(θ₀ + β)` is the transport of `S(₂Eᵢ N)` over `T(θ + β₀)`.** -/
def lastBlackTwoTEquiv :
    LastBlackTwoT Q Λ i θ₀ β₀ N hQ ≃ₗ[Tfam (θ₀ + (({i} : Multiset I) + β₀))]
      FamilyCast Tfam (lastBlackTwo_weight i θ₀ β₀).symm
        (ParabolicStandardT Q Λ (({i} : Multiset I) + θ₀) β₀ (LastResRight Q Λ i θ₀ β₀ N) hQ) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' t m := by
    change lastBlackTwoAction Q Λ i θ₀ β₀ N hQ t m =
      parabolicStandardAction Q Λ _ _ _ hQ ((familyRingCast Tfam
        (lastBlackTwo_weight i θ₀ β₀).symm).symm t) m
    rw [familyRingCast_symm_eq_castTensorProductAlgebra]
    rfl

/-- **`S(₁Eᵢ N)` over `T(θ₀ + β)`** is the standardization of `₁Eᵢ N`. -/
def lastBlackOneTEquiv :
    LastBlackOneT Q Λ i θ₀ β₀ N hQ ≃ₗ[Tfam (θ₀ + (({i} : Multiset I) + β₀))]
      ParabolicStandardT Q Λ θ₀ (({i} : Multiset I) + β₀) (LastResLeft Q Λ i θ₀ β₀ N) hQ where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Last

end StandardT

section ResFactorCast

variable (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I)
  {θ θ' : Multiset I} (β₀ : Multiset I) (hθ : θ = θ')
  (P : Type) [AddCommGroup P] [Module k P]
  [Module (parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)) P]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)) P]

/-- **`₂Eᵢ` commutes with the transport along an equality of the left weight.** -/
def rightResRightFactorCast :
    RightResRight Q Λ i θ' β₀
        (FactorCast Q Λ hθ (rfl : ({i} : Multiset I) + β₀ = {i} + β₀) P) ≃ₗ[
          parabolicFactorAlgebra Q Λ θ' β₀]
      FactorCast Q Λ hθ (rfl : β₀ = β₀) (RightResRight Q Λ i θ β₀ P) := by
  subst hθ
  exact
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

variable {P} {P' : Type} [AddCommGroup P'] [Module k P']
  [Module (parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)) P']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)) P']

/-- **Naturality of `rightResRightFactorCast`.** -/
theorem rightResRightFactorCast_map
    (g : P →ₗ[parabolicFactorAlgebra Q Λ θ (({i} : Multiset I) + β₀)] P')
    (x : RightResRight Q Λ i θ' β₀
      (FactorCast Q Λ hθ (rfl : ({i} : Multiset I) + β₀ = {i} + β₀) P)) :
    rightResRightFactorCast Q Λ i β₀ hθ P' (Res.map (factorCastMap Q Λ hθ rfl g) x) =
      factorCastMap Q Λ hθ rfl (Res.map g) (rightResRightFactorCast Q Λ i β₀ hθ P x) := by
  subst hθ
  rfl

end ResFactorCast

end Categorification.Stendhal
