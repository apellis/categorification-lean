/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55DimensionFinite
import Categorification.WeightedKLR.RedStrands.BlackInductionDimension
import Categorification.WeightedKLR.RedStrands.BlackModuleFactorCommutation
import Categorification.WeightedKLR.RedStrands.BlackModuleSecondFactorCommutation
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastBlackMissing
import Categorification.WeightedKLR.RedStrands.ParabolicStandardDimension

/-!
# Black-last pieces of standardization in the dimension count of Proposition 5.5

Webster, arXiv:1309.3796v3, proof of Proposition 5.5. The dimension count (5.14)–(5.15) splits
`S(N)`, `S(₁Fᵢ N)` and `S(₂Fᵢ N)` according to the last strand. This file computes the piece
where the last strand is black of colour `j`, for contents given by equalities
`j + θ₀ = θ'` and `j + β₀ = β'`, and the induction `Fᵢ E_j S(N)` when `j` occurs in both
blocks.

* `finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq`: `j` in both blocks,
  `dim e_j S N = dim S(₁E_j N) + dim S(₂E_j N)`.
* `finrank_fixSub_lastStrandIdem_parabolicStandardT_left_of_eq`,
  `finrank_fixSub_lastStrandIdem_parabolicStandardT_right_of_eq`: `j` in one block.
* `finrank_indK_blackRes_lastStandardT`: `dim Fᵢ E_j S N = dim Fᵢ S(₁E_j N) + dim Fᵢ S(₂E_j N)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong

open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ}

local notation "D" => parabolicFactorAlgebra Q Λ
local notation "Rs" => InductionAlong.Res

/-- The `k`-structure on the restriction of a module along a map of factor algebras. -/
@[reducible] def resFactorModuleK {θ β θ' β' : Multiset I} (φ : D θ β →ₙ+* D θ' β')
    (M : Type*) [AddCommGroup M] [Module (D θ' β') M] : Module k (Rs φ M) :=
  Res.moduleK k φ M

/-- The scalar tower `k → D θ β → Res φ M`. -/
theorem resFactor_isScalarTower {θ β θ' β' : Multiset I} (φ : D θ β →ₙ+* D θ' β')
    (M : Type*) [AddCommGroup M] [Module (D θ' β') M] :
    letI := resFactorModuleK (k := k) φ M; IsScalarTower k (D θ β) (Rs φ M) :=
  Res.isScalarTowerK k φ M

/-- Restriction of a finite-dimensional module along a `k`-linear nonunital algebra map is
finite-dimensional, for any scalar tower `k → A → Res φ M`. -/
theorem finiteDimensional_res_of_isScalarTower {A B : Type*} [Ring A] {_ : Algebra k A} [Ring B]
    {_ : Algebra k B} (f : A →ₙₐ[k] B) (M : Type*) [AddCommGroup M] [Module k M] [Module B M]
    [IsScalarTower k B M] [Module k (Rs (NonUnitalRingHomClass.toNonUnitalRingHom f) M)]
    [IsScalarTower k A (Rs (NonUnitalRingHomClass.toNonUnitalRingHom f) M)]
    [FiniteDimensional k M] :
    FiniteDimensional k (Rs (NonUnitalRingHomClass.toNonUnitalRingHom f) M) :=
  Module.Finite.of_injective
    ({ toFun := Res.val
       map_add' := Res.val_add
       map_smul' := fun c r => by
         rw [← algebraMap_smul A c r, Res.val_smul]
         change f (algebraMap k A c) • r.val = c • r.val
         rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_assoc]
         exact congrArg (c • ·) r.prop } :
      Rs (NonUnitalRingHomClass.toNonUnitalRingHom f) M →ₗ[k] M)
    fun _ _ h => Res.ext h

variable {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q) (hQ : KLRSymm Q)

section EqContents

attribute [local instance] resFactorModuleK resFactor_isScalarTower

include hR in
/-- **The black-last piece of `S N`, `j` in both blocks**, for contents given by equalities
(Webster, arXiv:1309.3796v3, proof of Proposition 5.5): for `j + θ₀ = θ'` and `j + β₀ = β'`,
the piece of `S N` whose last strand is black of colour `j` has dimension
`dim S(₁E_j N) + dim S(₂E_j N)`. -/
theorem finrank_fixSub_lastStrandIdem_parabolicStandardT_of_eq (j : I)
    {θ₀ β₀ θ' β' : Multiset I} (hθ : {j} + θ₀ = θ') (hβ : {j} + β₀ = β') (M : Type)
    [AddCommGroup M] [Module k M] [Module (D θ' β') M] [IsScalarTower k (D θ' β') M]
    [FiniteDimensional k M] :
    Module.finrank k (fixSub k (ParabolicStandardT Q Λ θ' β' M hQ)
        (lastStrandIdem Q Λ (θ' + β') (some j))) =
      Module.finrank k (ParabolicStandard Q Λ θ₀ β' (Rs (leftAppendHomOfEq Q Λ j hθ β') M)) +
        Module.finrank k
          (ParabolicStandard Q Λ θ' β₀ (Rs (parabolicRightHomOfEq Q Λ j hβ θ') M)) := by
  subst hθ hβ
  have :=
    finiteDimensional_res_of_isScalarTower (parabolicAppendLeft Q Λ j θ₀ ({j} + β₀)) M
  have :=
    finiteDimensional_res_of_isScalarTower (parabolicAppendRight Q Λ j β₀ ({j} + θ₀)) M
  have := finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQ θ₀ ({j} + β₀)
    (LastResLeft Q Λ j θ₀ β₀ M)
  have := finiteDimensional_parabolicStandard_of_finiteDimensional (Λ := Λ) hR hQ ({j} + θ₀) β₀
    (LastResRight Q Λ j θ₀ β₀ M)
  have := finiteDimensional_lastBlackRes Q Λ j θ₀ β₀ M hQ
  have h := finrank_fixSub_lastStrandIdem_parabolicStandardT_eq Q Λ j θ₀ β₀ M hQ
  exact h

/-- **The black-last piece of `S N`, `j` in the first block only** (Webster,
arXiv:1309.3796v3, proof of Proposition 5.5): for `j + θ₀ = θ'` and `j ∉ β`, the piece of
`S N` whose last strand is black of colour `j` has dimension `dim S(₁E_j N)`. -/
theorem finrank_fixSub_lastStrandIdem_parabolicStandardT_left_of_eq (j : I)
    {θ₀ θ' β : Multiset I} (hθ : {j} + θ₀ = θ') (hj : j ∉ β) (M : Type)
    [AddCommGroup M] [Module k M] [Module (D θ' β) M] [IsScalarTower k (D θ' β) M] :
    Module.finrank k (fixSub k (ParabolicStandardT Q Λ θ' β M hQ)
        (lastStrandIdem Q Λ (θ' + β) (some j))) =
      Module.finrank k (ParabolicStandard Q Λ θ₀ β (Rs (leftAppendHomOfEq Q Λ j hθ β) M)) := by
  subst hθ
  have h := finrank_fixSub_lastStrandIdem_parabolicStandardT_left Q Λ j θ₀ β M hQ hj
  exact h

/-- **The black-last piece of `S N`, `j` in the second block only** (Webster,
arXiv:1309.3796v3, proof of Proposition 5.5): for `j + β₀ = β'` and `j ∉ θ`, the piece of
`S N` whose last strand is black of colour `j` has dimension `dim S(₂E_j N)`. -/
theorem finrank_fixSub_lastStrandIdem_parabolicStandardT_right_of_eq (j : I)
    {θ β₀ β' : Multiset I} (hβ : {j} + β₀ = β') (hj : j ∉ θ) (M : Type)
    [AddCommGroup M] [Module k M] [Module (D θ β') M] [IsScalarTower k (D θ β') M] :
    Module.finrank k (fixSub k (ParabolicStandardT Q Λ θ β' M hQ)
        (lastStrandIdem Q Λ (θ + β') (some j))) =
      Module.finrank k
        (ParabolicStandard Q Λ θ β₀ (Rs (parabolicRightHomOfEq Q Λ j hβ θ) M)) := by
  subst hβ
  have h := finrank_fixSub_lastStrandIdem_parabolicStandardT_right Q Λ j θ β₀ M hQ hj
  exact h

end EqContents

/-- Finite-dimensionality of `Fᵢ` along an equality of black weights. -/
theorem finiteDimensional_indK_transport (i : I) {ν ν' : Multiset I} (h : ν = ν')
    (X X' : Type) [AddCommGroup X] [Module k X] [Module (TensorProductAlgebra k Q Λ ν) X]
    [AddCommGroup X'] [Module k X'] [Module (TensorProductAlgebra k Q Λ ν') X']
    (e : X ≃ₗ[k] X')
    (he : ∀ (t : TensorProductAlgebra k Q Λ ν) (x : X),
      e (t • x) = castTensorProductAlgebra Q Λ h t • e x)
    [FiniteDimensional k (IndK k X' (appendBlackNU (Q := Q) (Λ := Λ) i ν'))] :
    FiniteDimensional k (IndK k X (appendBlackNU (Q := Q) (Λ := Λ) i ν)) := by
  subst h
  let E : IndK k X (appendBlackNU (Q := Q) (Λ := Λ) i ν) ≃ₗ[TensorProductAlgebra k Q Λ
      ((Singleton.singleton i : Multiset I) + ν)] IndK k X' (appendBlackNU (Q := Q) (Λ := Λ) i ν) :=
    Ind.mapEquiv (castLinearEquiv X X' e he)
  exact Module.Finite.equiv (E.restrictScalars k).symm

include hR in
/-- `Fᵢ X` is finite-dimensional for a finitely generated `T(ν)`-module `X`. -/
theorem finiteDimensional_indK_appendBlackNU (i : I) (ν : Multiset I) (X : Type)
    [AddCommGroup X] [Module (TensorProductAlgebra k Q Λ ν) X]
    [Module.Finite (TensorProductAlgebra k Q Λ ν) X] :
    FiniteDimensional k (IndK k X (appendBlackNU (Q := Q) (Λ := Λ) i ν)) := by
  have := tensorProductAlgebra_finite Λ ((Singleton.singleton i : Multiset I) + ν) hR
  exact IndK.finite_restrict k X _

/-- `S(₁E_j N)` as a module over `T(θ₀ + (j + β₀))` is the standardization `S(₁E_j N)`. -/
def lastBlackOneEquiv (j : I) (θ₀ β₀ : Multiset I) (N : Type)
    [AddCommGroup N] [Module k N] [Module (D ({j} + θ₀) ({j} + β₀)) N]
    [IsScalarTower k (D ({j} + θ₀) ({j} + β₀)) N] :
    ParabolicStandardT Q Λ θ₀ ({j} + β₀) (LastResLeft Q Λ j θ₀ β₀ N) hQ ≃ₗ[
      TensorProductAlgebra k Q Λ (θ₀ + ({j} + β₀))] LastBlackOneT Q Λ j θ₀ β₀ N hQ :=
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- `S(₁E_j N)` is finite over `T(θ₀ + (j + β₀))` when `N` is finite-dimensional. -/
theorem finite_lastBlackOneT (j : I) (θ₀ β₀ : Multiset I) (N : Type)
    [AddCommGroup N] [Module k N] [Module (D ({j} + θ₀) ({j} + β₀)) N]
    [IsScalarTower k (D ({j} + θ₀) ({j} + β₀)) N] [FiniteDimensional k N] :
    Module.Finite (TensorProductAlgebra k Q Λ (θ₀ + ({j} + β₀)))
      (LastBlackOneT Q Λ j θ₀ β₀ N hQ) := by
  have := finiteDimensional_res_of_isScalarTower (parabolicAppendLeft Q Λ j θ₀ ({j} + β₀)) N
  have h := finite_parabolicStandardT_of_finiteDimensional (Λ := Λ) hQ θ₀ ({j} + β₀)
    (LastResLeft Q Λ j θ₀ β₀ N)
  exact Module.Finite.equiv (lastBlackOneEquiv (Λ := Λ) hQ j θ₀ β₀ N)

/-- `Fᵢ S(₁E_j N)` computed through `LastBlackOneT`. -/
theorem finrank_firstIndF_lastBlackOneT (i j : I) (θ₀ β₀ : Multiset I) (N : Type)
    [AddCommGroup N] [Module k N] [Module (D ({j} + θ₀) ({j} + β₀)) N]
    [IsScalarTower k (D ({j} + θ₀) ({j} + β₀)) N] :
    Module.finrank k (FirstIndF Q Λ i θ₀ ({j} + β₀) (LastResLeft Q Λ j θ₀ β₀ N) hQ) =
      Module.finrank k (IndK k (LastBlackOneT Q Λ j θ₀ β₀ N hQ)
        (appendBlackNU (Q := Q) (Λ := Λ) i (θ₀ + ({j} + β₀)))) := by
  let E : IndK k (ParabolicStandardT Q Λ θ₀ ({j} + β₀) (LastResLeft Q Λ j θ₀ β₀ N) hQ)
      (appendBlackNU (Q := Q) (Λ := Λ) i (θ₀ + ({j} + β₀))) ≃ₗ[TensorProductAlgebra k Q Λ
      ((Singleton.singleton i : Multiset I) + (θ₀ + ({j} + β₀)))]
      IndK k (LastBlackOneT Q Λ j θ₀ β₀ N hQ)
        (appendBlackNU (Q := Q) (Λ := Λ) i (θ₀ + ({j} + β₀))) :=
    Ind.mapEquiv (lastBlackOneEquiv (Λ := Λ) hQ j θ₀ β₀ N)
  exact (E.restrictScalars k).finrank_eq

/-- `S(₂E_j N)` over `T(θ₀ + (j + β₀))` is `S(₂E_j N)` over `T((j + θ₀) + β₀)` along the
equality of weights. -/
def lastBlackTwoEquiv (j : I) (θ₀ β₀ : Multiset I) (N : Type)
    [AddCommGroup N] [Module k N] [Module (D ({j} + θ₀) ({j} + β₀)) N]
    [IsScalarTower k (D ({j} + θ₀) ({j} + β₀)) N] :
    LastBlackTwoT Q Λ j θ₀ β₀ N hQ ≃ₗ[k]
      ParabolicStandardT Q Λ ({j} + θ₀) β₀ (LastResRight Q Λ j θ₀ β₀ N) hQ :=
  { toFun := fun x => x
    invFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- `Fᵢ S(₂E_j N)` has the same dimension over both presentations of its weight. -/
theorem finrank_indK_lastBlackTwoT (i j : I) (θ₀ β₀ : Multiset I) (N : Type)
    [AddCommGroup N] [Module k N] [Module (D ({j} + θ₀) ({j} + β₀)) N]
    [IsScalarTower k (D ({j} + θ₀) ({j} + β₀)) N] :
    Module.finrank k (FirstIndF Q Λ i ({j} + θ₀) β₀ (LastResRight Q Λ j θ₀ β₀ N) hQ) =
      Module.finrank k (IndK k (LastBlackTwoT Q Λ j θ₀ β₀ N hQ)
        (appendBlackNU (Q := Q) (Λ := Λ) i (θ₀ + ({j} + β₀)))) :=
  finrank_indK_transport (Q := Q) (Λ := Λ) i (lastBlackTwo_weight j θ₀ β₀) _ _
    (lastBlackTwoEquiv (Λ := Λ) hQ j θ₀ β₀ N) fun _ _ => rfl

/-- `Fᵢ S(₂E_j N)` over `T(θ₀ + (j + β₀))` is finite-dimensional when `N` is. -/
theorem finiteDimensional_indK_lastBlackTwoT (i j : I) (θ₀ β₀ : Multiset I) (N : Type)
    [AddCommGroup N] [Module k N] [Module (D ({j} + θ₀) ({j} + β₀)) N]
    [IsScalarTower k (D ({j} + θ₀) ({j} + β₀)) N]
    [FiniteDimensional k (IndK k
        (ParabolicStandardT Q Λ ({j} + θ₀) β₀ (LastResRight Q Λ j θ₀ β₀ N) hQ)
        (appendBlackNU (Q := Q) (Λ := Λ) i (({j} + θ₀) + β₀)))] :
    FiniteDimensional k (IndK k (LastBlackTwoT Q Λ j θ₀ β₀ N hQ)
        (appendBlackNU (Q := Q) (Λ := Λ) i (θ₀ + ({j} + β₀)))) :=
  finiteDimensional_indK_transport (Q := Q) (Λ := Λ) i (lastBlackTwo_weight j θ₀ β₀) _ _
    (lastBlackTwoEquiv (Λ := Λ) hQ j θ₀ β₀ N) fun _ _ => rfl

include hR in
/-- **`Fᵢ E_j S(N)` when `j` occurs in both blocks** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5): `Fᵢ` applied to `0 → S(₂E_j N) → E_j S(N) → S(₁E_j N) → 0` gives
`dim Fᵢ E_j S(N) = dim Fᵢ S(₁E_j N) + dim Fᵢ S(₂E_j N)`. -/
theorem finrank_indK_blackRes_lastStandardT (i j : I) (θ₀ β₀ : Multiset I) (N : Type)
    [AddCommGroup N] [Module k N] [Module (D ({j} + θ₀) ({j} + β₀)) N]
    [IsScalarTower k (D ({j} + θ₀) ({j} + β₀)) N] [FiniteDimensional k N] :
    Module.finrank k (IndK k (BlackRes (Q := Q) (Λ := Λ) j (θ₀ + ({j} + β₀))
        (LastStandardT Q Λ j θ₀ β₀ N hQ)) (appendBlackNU (Q := Q) (Λ := Λ) i (θ₀ + ({j} + β₀)))) =
      Module.finrank k (FirstIndF Q Λ i θ₀ ({j} + β₀) (LastResLeft Q Λ j θ₀ β₀ N) hQ) +
        Module.finrank k (FirstIndF Q Λ i ({j} + θ₀) β₀ (LastResRight Q Λ j θ₀ β₀ N) hQ) := by
  have :=
    finiteDimensional_res_of_isScalarTower (parabolicAppendLeft Q Λ j θ₀ ({j} + β₀)) N
  have :=
    finiteDimensional_res_of_isScalarTower (parabolicAppendRight Q Λ j β₀ ({j} + θ₀)) N
  have := tensorProductAlgebra_finite Λ ((Singleton.singleton i : Multiset I) + (θ₀ + ({j} + β₀)))
    hR
  have := tensorProductAlgebra_finite Λ ((Singleton.singleton i : Multiset I) + (({j} + θ₀) + β₀))
    hR
  have hone := finite_parabolicStandardT_of_finiteDimensional (Λ := Λ) hQ θ₀ ({j} + β₀)
    (LastResLeft Q Λ j θ₀ β₀ N)
  have htwo := finite_parabolicStandardT_of_finiteDimensional (Λ := Λ) hQ ({j} + θ₀) β₀
    (LastResRight Q Λ j θ₀ β₀ N)
  have := finite_lastBlackOneT (Λ := Λ) hQ j θ₀ β₀ N
  have := finiteDimensional_indK_appendBlackNU (Λ := Λ) hR i (θ₀ + ({j} + β₀))
    (LastBlackOneT Q Λ j θ₀ β₀ N hQ)
  have := finiteDimensional_indK_appendBlackNU (Λ := Λ) hR i (({j} + θ₀) + β₀)
    (ParabolicStandardT Q Λ ({j} + θ₀) β₀ (LastResRight Q Λ j θ₀ β₀ N) hQ)
  have htw := finrank_indK_lastBlackTwoT (Λ := Λ) hQ i j θ₀ β₀ N
  have := finiteDimensional_indK_lastBlackTwoT (Λ := Λ) hQ i j θ₀ β₀ N
  have hs := lastBlackResOneT_surjective Q Λ j θ₀ β₀ N hQ
  have he := lastBlackResT_exact Q Λ j θ₀ β₀ N hQ
  have hi := lastBlackResTwoT_injective Q Λ j θ₀ β₀ N hQ
  have := finiteDimensional_indK_appendBlack_of_exact (i := i) C hR hs he
  have h1 := finrank_indK_appendBlack_of_exact (i := i) C hR hi hs he
  have h2 := finrank_firstIndF_lastBlackOneT (Λ := Λ) hQ i j θ₀ β₀ N
  omega

end Categorification.Stendhal
