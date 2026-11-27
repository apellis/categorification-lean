/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardExact

/-!
# Standardization is an additive functor

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5,
Definition 5.4, for the induced model of standardization. The maps of standardizations
`S(g)` induced by maps `g` of modules over the factor algebras (`parabolicStandardMap`) preserve
identities, composition, sums and zero.

## Main results

* `parabolicStandardMap_id`, `parabolicStandardMap_comp`: functoriality.
* `parabolicStandardMap_add`, `parabolicStandardMap_zero`, `parabolicStandardMap_sum`:
  additivity.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ+1) → I →₀ ℕ) (θ β : Multiset I)

local notation "D" => parabolicFactorAlgebra Q Λ θ β

variable {N N' N'' : Type*}
  [AddCommGroup N] [Module k N] [Module (parabolicFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (parabolicFactorAlgebra Q Λ θ β) N']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N']
  [AddCommGroup N''] [Module k N''] [Module (parabolicFactorAlgebra Q Λ θ β) N'']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N'']

omit [IsScalarTower k (parabolicFactorAlgebra Q Λ θ β) N] in
/-- Two maps out of a standardization agree when they agree on the classes of the generators
`r ⊗ n` of affine induction. -/
theorem parabolicStandard_linearMap_ext {Z : Type*} [AddCommGroup Z] [Module k Z]
    {f g : ParabolicStandard Q Λ θ β N →ₗ[k] Z}
    (h : ∀ r (n : ParabolicInput Q Λ θ β N),
      f (Submodule.Quotient.mk (BalancedTensor.tmul r n)) =
        g (Submodule.Quotient.mk (BalancedTensor.tmul r n))) : f = g := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  have key : ∀ y : ParabolicShuffle Q Λ θ β N,
      f (Submodule.Quotient.mk y) = g (Submodule.Quotient.mk y) := by
    intro y
    induction y using BalancedTensor.induction_on with
    | zero => rw [Submodule.Quotient.mk_zero, map_zero, map_zero]
    | tmul r n => exact h r n
    | add y y' hy hy' =>
      rw [Submodule.Quotient.mk_add, map_add, map_add]
      exact congrArg₂ (· + ·) hy hy'
  exact key y

theorem parabolicStandardMap_id :
    parabolicStandardMap Q Λ θ β (LinearMap.id : N →ₗ[D] N) = LinearMap.id :=
  parabolicStandard_linearMap_ext Q Λ θ β fun _ _ => rfl

theorem parabolicStandardMap_comp (g : N →ₗ[D] N') (g' : N' →ₗ[D] N'') :
    parabolicStandardMap Q Λ θ β (g'.comp g) =
      (parabolicStandardMap Q Λ θ β g').comp (parabolicStandardMap Q Λ θ β g) :=
  parabolicStandard_linearMap_ext Q Λ θ β fun _ _ => rfl

theorem parabolicStandardMap_add (g g' : N →ₗ[D] N') :
    parabolicStandardMap Q Λ θ β (g + g') =
      parabolicStandardMap Q Λ θ β g + parabolicStandardMap Q Λ θ β g' :=
  parabolicStandard_linearMap_ext Q Λ θ β fun r n => by
    rw [LinearMap.add_apply, parabolicStandardMap_mk, parabolicStandardMap_mk,
      parabolicStandardMap_mk, ← Submodule.Quotient.mk_add]
    congr 1
    exact BalancedTensor.tmul_add (N := ParabolicInput Q Λ θ β N') r (g n) (g' n)

theorem parabolicStandardMap_zero :
    parabolicStandardMap Q Λ θ β (0 : N →ₗ[D] N') = 0 :=
  parabolicStandard_linearMap_ext Q Λ θ β fun r n => by
    rw [LinearMap.zero_apply, parabolicStandardMap_mk]
    exact (congrArg Submodule.Quotient.mk
      (BalancedTensor.tmul_zero (N := ParabolicInput Q Λ θ β N') r)).trans
        (Submodule.Quotient.mk_zero _)

theorem parabolicStandardMap_sum {ι : Type*} (s : Finset ι) (g : ι → N →ₗ[D] N') :
    parabolicStandardMap Q Λ θ β (∑ i ∈ s, g i) = ∑ i ∈ s, parabolicStandardMap Q Λ θ β (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, parabolicStandardMap_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, parabolicStandardMap_add, ih]

end Categorification.Stendhal
