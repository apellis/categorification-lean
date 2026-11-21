/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndShortExact
import Categorification.WeightedKLR.RedStrands.TensorFinite
import Categorification.Algebra.InductionAlongFinite

/-!
# Finiteness of standardization and of the modules of Proposition 5.5

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Proposition 5.5. The dimension count behind injectivity of `δ₁ : S(₁Fᵢ N) → Fᵢ S(N)` needs all
modules of the sequence `0 → S(₁Fᵢ N) → Fᵢ S(N) → S(₂Fᵢ N) → 0` to be finite-dimensional.

Standardization `S N` is a quotient of the affine induced module, which is generated over the
affine KLR algebra by finitely many vectors when `N` is a finitely generated module over the
factor algebra (the input map from the affine algebra onto the factor algebra is surjective).
The action of the tensor product algebra on `S N` is induced by the affine action, so `S N` is
a finitely generated module over the tensor product algebra. The inductions `₁Fᵢ`, `₂Fᵢ` and
`Fᵢ` preserve finite generation. Finally the tensor product algebra is a finite module over the
coefficient ring (`tensorProductAlgebra_finite`, for Rouquier parameters).

## Main results

* `parabolicStandardT_finite`: `S N` is finitely generated over `T(θ + β)`.
* `firstIndStandardT_finite`, `firstIndF_finite`, `lastIndStandardT_finite`: `S(₁Fᵢ N)`,
  `Fᵢ S(N)` and `S(₂Fᵢ N)` are finitely generated over `T(i + (θ + β))`.
* `*_restrict_finite`: the same modules are finite over `k` through the tensor product algebra.
* `firstIndDeltaInjective_iff_finrank_of_finite`: the dimension criterion for injectivity of
  `δ₁` for every finite-dimensional `N`, with no finiteness hypotheses left.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong MulOpposite
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section CommRing

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]

local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ))
  (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "T" => TensorProductAlgebra k Q Λ (θ + β)

omit [Module k N] [IsScalarTower k D N] in
/-- The input module of standardization is finitely generated over `R(α) ⊗ R(δ)` when `N` is
finitely generated over the factor algebra, since the input map is surjective. -/
theorem parabolicInput_finite [Module.Finite D N] :
    Module.Finite (TensorKLR S α δ) (ParabolicInput Q Λ θ β N) :=
  have : Module.Finite D (ParabolicInput Q Λ θ β N) := ‹Module.Finite D N›
  Module.Finite.of_surjective_compatible (A := D) (M := ParabolicInput Q Λ θ β N)
    (V := ParabolicInput Q Λ θ β N) (AddMonoidHom.id _) Function.surjective_id
    (fun d => (parabolicInputMap_surjective Q Λ θ β d).choose) fun d n => by
      change d • (n : N) = parabolicInputMap Q Λ θ β _ • (n : N)
      rw [(parabolicInputMap_surjective Q Λ θ β d).choose_spec]

/-- The affine induced module is finitely generated over the affine KLR algebra. -/
theorem parabolicShuffle_finite [Module.Finite D N] :
    Module.Finite (KLRAlgebra k S (α + δ)) (ParabolicShuffle Q Λ θ β N) :=
  have := parabolicInput_finite Q Λ θ β N
  BalancedTensor.finite

/-- **Standardization of a finitely generated module is finitely generated** over the tensor
product algebra `T(θ + β)` (Webster, arXiv:1309.3796v3, proof of Proposition 5.5). -/
theorem parabolicStandardT_finite (hQ : KLRSymm Q) [Module.Finite D N] :
    Module.Finite T (ParabolicStandardT Q Λ θ β N hQ) := by
  have := parabolicShuffle_finite Q Λ θ β N
  refine Module.Finite.of_surjective_compatible
    ((excludedSpace (parabolicShuffleAction Q Λ θ β N)
      (parabolicOrderedLoadings (ℓ := ℓ) θ β)).mkQ.toAddMonoidHom :
        ParabolicShuffle Q Λ θ β N →+ ParabolicStandardT Q Λ θ β N hQ)
    (Submodule.mkQ_surjective _)
    (fun a => TensorProductAlgebra.mk Q Λ (θ + β)
      (orderProjection Q Λ (θ + β) (StendhalAlgebraAllOrders.ofKLR k Q Λ (θ + β)
        (castKLR S (parabolicInputWeights_add (ℓ := ℓ) θ β) a)))) fun a m => ?_
  change _ = parabolicStandardAction Q Λ θ β N hQ _ _
  rw [parabolicStandardAction_affine]
  rfl

/-- **Standardization of a finitely generated module is finite over `k`**, through the tensor
product algebra, for Rouquier parameters (Webster, arXiv:1309.3796v3, proof of
Proposition 5.5). -/
theorem parabolicStandardT_restrict_finite {C : QuantumGroup.CartanDatum I}
    (hR : IsRouquierQ C Q) (hQ : KLRSymm Q) [Module.Finite D N] :
    Module.Finite k (RestrictScalars k T (ParabolicStandardT Q Λ θ β N hQ)) :=
  have := tensorProductAlgebra_finite Λ (θ + β) hR
  have := parabolicStandardT_finite Q Λ θ β N hQ
  Module.Finite.restrictScalars_of_finite k T _

end CommRing

section Field

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (θ β : Multiset I)
  (N : Type*) [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] (hQ : KLRSymm Q)

local notation "Si" j => (Singleton.singleton j : Multiset I)
local notation "D" => parabolicFactorAlgebra Q Λ θ β
local notation "T′" => TensorProductAlgebra k Q Λ ((Si i) + (θ + β))

omit [Module k N] [IsScalarTower k D N] in
/-- `₁Fᵢ N` is finitely generated over the factor algebra of `(i + θ, β)`. -/
theorem firstIndLeft_finite [Module.Finite D N] :
    Module.Finite (parabolicFactorAlgebra Q Λ ((Si i) + θ) β) (FirstIndLeft Q Λ i θ β N) :=
  IndK.finite k N _

omit [Module k N] [IsScalarTower k D N] in
/-- `₂Fᵢ N` is finitely generated over the factor algebra of `(θ, i + β)`. -/
theorem lastIndRight_finite [Module.Finite D N] :
    Module.Finite (parabolicFactorAlgebra Q Λ θ ((Si i) + β)) (LastIndRight Q Λ i θ β N) :=
  IndK.finite k N _

omit [Module k N] [IsScalarTower k D N] in
/-- **`S(₁Fᵢ N)` is finitely generated** over `T(i + (θ + β))`. -/
theorem firstIndStandardT_finite [Module.Finite D N] :
    Module.Finite T′ (FirstIndStandardT Q Λ i θ β N hQ) := by
  have := firstIndLeft_finite Q Λ i θ β N
  have := parabolicStandardT_finite Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N) hQ
  refine Module.Finite.of_surjective_compatible
    (M := ParabolicStandardT Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N) hQ)
    (V := FirstIndStandardT Q Λ i θ β N hQ)
    (AddMonoidHom.id (ParabolicStandard Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N)))
    Function.surjective_id
    (castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β)).symm fun t m => ?_
  change _ = parabolicStandardAction Q Λ ((Si i) + θ) β (FirstIndLeft Q Λ i θ β N) hQ
    (castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β)
      ((castTensorProductAlgebra Q Λ (firstInd_blackWeight i θ β)).symm t)) m
  rw [AlgEquiv.apply_symm_apply]
  rfl

omit [Module k N] [IsScalarTower k D N] in
/-- **`S(₂Fᵢ N)` is finitely generated** over `T(i + (θ + β))`. -/
theorem lastIndStandardT_finite [Module.Finite D N] :
    Module.Finite T′ (LastIndStandardT Q Λ i θ β N hQ) := by
  have := lastIndRight_finite Q Λ i θ β N
  have := parabolicStandardT_finite Q Λ θ ((Si i) + β) (LastIndRight Q Λ i θ β N) hQ
  refine Module.Finite.of_surjective_compatible
    (M := ParabolicStandardT Q Λ θ ((Si i) + β) (LastIndRight Q Λ i θ β N) hQ)
    (V := LastIndStandardT Q Λ i θ β N hQ)
    (AddMonoidHom.id (ParabolicStandard Q Λ θ ((Si i) + β) (LastIndRight Q Λ i θ β N)))
    Function.surjective_id
    (castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)).symm fun t m => ?_
  change _ = parabolicStandardAction Q Λ θ ((Si i) + β) (LastIndRight Q Λ i θ β N) hQ
    (castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)
      ((castTensorProductAlgebra Q Λ (lastInd_blackWeight i θ β)).symm t)) m
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- **`Fᵢ S(N)` is finitely generated** over `T(i + (θ + β))`. -/
theorem firstIndF_finite [Module.Finite D N] :
    Module.Finite T′ (FirstIndF Q Λ i θ β N hQ) :=
  have := parabolicStandardT_finite Q Λ θ β N hQ
  IndK.finite k _ _

variable {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)
include hR

omit [Module k N] [IsScalarTower k D N] in
/-- **`S(₁Fᵢ N)` is finite-dimensional** through `T(i + (θ + β))`, for Rouquier parameters
(Webster, arXiv:1309.3796v3, proof of Proposition 5.5). -/
theorem firstIndStandardT_restrict_finite [Module.Finite D N] :
    FiniteDimensional k (RestrictScalars k T′ (FirstIndStandardT Q Λ i θ β N hQ)) :=
  have := tensorProductAlgebra_finite Λ ((Si i) + (θ + β)) hR
  have := firstIndStandardT_finite Q Λ i θ β N hQ
  Module.Finite.restrictScalars_of_finite k T′ _

/-- **`Fᵢ S(N)` is finite-dimensional** through `T(i + (θ + β))`, for Rouquier parameters
(Webster, arXiv:1309.3796v3, proof of Proposition 5.5). -/
theorem firstIndF_restrict_finite [Module.Finite D N] :
    FiniteDimensional k (RestrictScalars k T′ (FirstIndF Q Λ i θ β N hQ)) :=
  have := tensorProductAlgebra_finite Λ ((Si i) + (θ + β)) hR
  have := firstIndF_finite Q Λ i θ β N hQ
  Module.Finite.restrictScalars_of_finite k T′ _

omit [Module k N] [IsScalarTower k D N] in
/-- **`S(₂Fᵢ N)` is finite-dimensional** through `T(i + (θ + β))`, for Rouquier parameters
(Webster, arXiv:1309.3796v3, proof of Proposition 5.5). -/
theorem lastIndStandardT_restrict_finite [Module.Finite D N] :
    FiniteDimensional k (RestrictScalars k T′ (LastIndStandardT Q Λ i θ β N hQ)) :=
  have := tensorProductAlgebra_finite Λ ((Si i) + (θ + β)) hR
  have := lastIndStandardT_finite Q Λ i θ β N hQ
  Module.Finite.restrictScalars_of_finite k T′ _

/-- **Injectivity of `δ₁` as a dimension equality, for finite-dimensional `N`** (Webster,
arXiv:1309.3796v3, proof of Proposition 5.5): for Rouquier parameters and `N`
finite-dimensional, `δ₁` is injective exactly when
`dim Fᵢ S(N) = dim S(₁Fᵢ N) + dim S(₂Fᵢ N)`. -/
theorem firstIndDeltaInjective_iff_finrank_of_finite [FiniteDimensional k N] :
    FirstIndDeltaInjective Q Λ i θ β N hQ ↔
      Module.finrank k (RestrictScalars k T′ (FirstIndF Q Λ i θ β N hQ)) =
        Module.finrank k (RestrictScalars k T′ (FirstIndStandardT Q Λ i θ β N hQ)) +
          Module.finrank k (RestrictScalars k T′ (LastIndStandardT Q Λ i θ β N hQ)) :=
  have : Module.Finite D N := Module.Finite.of_restrictScalars_finite k D N
  have := firstIndStandardT_restrict_finite Q Λ i θ β N hQ hR
  have := firstIndF_restrict_finite Q Λ i θ β N hQ hR
  firstIndDeltaInjective_iff_finrank Q Λ i θ β N hQ

end Field

end Categorification.Stendhal
