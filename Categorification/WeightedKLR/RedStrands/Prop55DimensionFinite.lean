/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Prop55DimensionTransport
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFinite

/-!
# Finiteness of the modules of the dimension count of Proposition 5.5

Webster, arXiv:1309.3796v2, proof of Proposition 5.5. The dimension count (5.13)–(5.14) applies
additivity of dimensions to restrictions and inductions of finite-dimensional modules. This file
records that these modules stay finite-dimensional.

* `finiteDimensional_res_of_nonUnitalAlgHom`: the restriction of a finite-dimensional module
  along a `k`-linear nonunital algebra map is finite-dimensional.
* `finite_res_appendBlackNU`, `finite_res_appendBlackNUOfEq`: restriction along a terminal
  black strand preserves finite generation over tensor product algebras.
* `finiteDimensional_restrictScalars_of_finite`: a finitely generated module over a tensor
  product algebra is finite-dimensional, for Rouquier parameters.
* `finiteDimensional_parabolicStandard_of_finiteDimensional`: standardization of a
  finite-dimensional module is finite-dimensional.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section ResFinite

variable {k A B : Type*} [Field k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  (f : A →ₙₐ[k] B) (M : Type*) [AddCommGroup M] [Module k M] [Module B M]
  [IsScalarTower k B M]

/-- The underlying vector of the restriction along a `k`-linear nonunital algebra map, as a
`k`-linear map. -/
def resValLinear :
    letI := Res.moduleK k (NonUnitalRingHomClass.toNonUnitalRingHom f) M
    Res (NonUnitalRingHomClass.toNonUnitalRingHom f) M →ₗ[k] M :=
  letI := Res.moduleK k (NonUnitalRingHomClass.toNonUnitalRingHom f) M
  { toFun := Res.val
    map_add' := Res.val_add
    map_smul' := fun c r => by
      change f (algebraMap k A c) • r.val = c • r.val
      rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_assoc]
      exact congrArg (c • ·) r.prop }

/-- **Restriction of a finite-dimensional module is finite-dimensional.** -/
theorem finiteDimensional_res_of_nonUnitalAlgHom [FiniteDimensional k M] :
    letI := Res.moduleK k (NonUnitalRingHomClass.toNonUnitalRingHom f) M
    FiniteDimensional k (Res (NonUnitalRingHomClass.toNonUnitalRingHom f) M) :=
  letI := Res.moduleK k (NonUnitalRingHomClass.toNonUnitalRingHom f) M
  Module.Finite.of_injective (resValLinear f M) fun _ _ h => Res.ext h

end ResFinite

section Tensor

universe u

variable {I k : Type u} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (ℓ + 1) → I →₀ ℕ}
  {C : QuantumGroup.CartanDatum I} (hR : IsRouquierQ C Q)

include hR

/-- **Restriction along a terminal black strand preserves finite generation.** -/
theorem finite_res_appendBlackNU (j : I) (μ : Multiset I) (M : Type*) [AddCommGroup M]
    [Module (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + μ)) M]
    [Module.Finite (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + μ)) M] :
    Module.Finite (TensorProductAlgebra k Q Λ μ) (Res (appendBlackNU (Q := Q) (Λ := Λ) j μ) M) := by
  let : Module k M := Module.compHom M
    (algebraMap k (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + μ)))
  have : IsScalarTower k
      (TensorProductAlgebra k Q Λ ((Singleton.singleton j : Multiset I) + μ)) M :=
    ⟨fun c t m => by
      change (c • t) • m = algebraMap k _ c • t • m
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  have := finite_blackRes (Q := Q) (Λ := Λ) j μ M C hR
  exact Module.Finite.equiv (blackResEquivRes Q Λ j μ M)

/-- `finite_res_appendBlackNU` for a black weight given by an equality. -/
theorem finite_res_appendBlackNUOfEq (j : I) {μ ν : Multiset I}
    (h : (Singleton.singleton j : Multiset I) + μ = ν) (M : Type*) [AddCommGroup M]
    [Module (TensorProductAlgebra k Q Λ ν) M] [Module.Finite (TensorProductAlgebra k Q Λ ν) M] :
    Module.Finite (TensorProductAlgebra k Q Λ μ) (Res (appendBlackNUOfEq Q Λ j h) M) := by
  subst h
  exact finite_res_appendBlackNU hR j μ M

/-- **Finitely generated modules over tensor product algebras are finite-dimensional**, for
Rouquier parameters. -/
theorem finiteDimensional_restrictScalars_of_finite (ν : Multiset I) (X : Type*)
    [AddCommGroup X] [Module (TensorProductAlgebra k Q Λ ν) X]
    [Module.Finite (TensorProductAlgebra k Q Λ ν) X] :
    FiniteDimensional k (RestrictScalars k (TensorProductAlgebra k Q Λ ν) X) :=
  have := tensorProductAlgebra_finite Λ ν hR
  Module.Finite.restrictScalars_of_finite k (TensorProductAlgebra k Q Λ ν) X

/-- The scalar tower `k → T(θ + β) → S N`. -/
instance parabolicStandardT_isScalarTower_dimensionCount (hQ : KLRSymm Q) (θ' β' : Multiset I)
    (M : Type*) [AddCommGroup M] [Module k M] [Module (parabolicFactorAlgebra Q Λ θ' β') M]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ' β') M] :
    IsScalarTower k (TensorProductAlgebra k Q Λ (θ' + β')) (ParabolicStandardT Q Λ θ' β' M hQ) :=
  ⟨fun c t y => DFunLike.congr_fun (map_smul (parabolicStandardAction Q Λ θ' β' M hQ) c t) y⟩

omit hR in
/-- `S N` and `S N` over `T(θ + β)` have the same dimension. -/
theorem finrank_restrictScalars_parabolicStandardT (hQ : KLRSymm Q) (θ' β' : Multiset I)
    (M : Type*) [AddCommGroup M] [Module k M] [Module (parabolicFactorAlgebra Q Λ θ' β') M]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ' β') M] :
    Module.finrank k (RestrictScalars k (TensorProductAlgebra k Q Λ (θ' + β'))
        (ParabolicStandardT Q Λ θ' β' M hQ)) =
      Module.finrank k (ParabolicStandard Q Λ θ' β' M) :=
  finrank_restrictScalars_of_tower

/-- **Standardization of a finite-dimensional module is finite-dimensional**, for Rouquier
parameters. -/
theorem finiteDimensional_parabolicStandard_of_finiteDimensional (hQ : KLRSymm Q)
    (θ' β' : Multiset I) (M : Type*) [AddCommGroup M] [Module k M]
    [Module (parabolicFactorAlgebra Q Λ θ' β') M]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ' β') M] [FiniteDimensional k M] :
    FiniteDimensional k (ParabolicStandard Q Λ θ' β' M) := by
  have : Module.Finite (parabolicFactorAlgebra Q Λ θ' β') M :=
    Module.Finite.of_restrictScalars_finite k _ M
  have := parabolicStandardT_restrict_finite Q Λ θ' β' M hR hQ
  exact Module.Finite.equiv (restrictScalarsEquivOfTower k
    (TensorProductAlgebra k Q Λ (θ' + β')) (ParabolicStandardT Q Λ θ' β' M hQ))

omit hR in
/-- **`S N` is finitely generated over `T(θ + β)` for finite-dimensional `N`.** -/
theorem finite_parabolicStandardT_of_finiteDimensional (hQ : KLRSymm Q)
    (θ' β' : Multiset I) (M : Type*) [AddCommGroup M] [Module k M]
    [Module (parabolicFactorAlgebra Q Λ θ' β') M]
    [IsScalarTower k (parabolicFactorAlgebra Q Λ θ' β') M] [FiniteDimensional k M] :
    Module.Finite (TensorProductAlgebra k Q Λ (θ' + β')) (ParabolicStandardT Q Λ θ' β' M hQ) :=
  have : Module.Finite (parabolicFactorAlgebra Q Λ θ' β') M :=
    Module.Finite.of_restrictScalars_finite k _ M
  parabolicStandardT_finite Q Λ θ' β' M hQ

end Tensor

end Categorification.Stendhal
