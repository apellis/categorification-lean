/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedBraidClassMap
import Categorification.WeightedKLR.RedStrands.TensorBraidingUnique

/-!
# The class map of an adjacent braid is determined by its generators

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §6.1, proof
of Corollary 6.10. For `ℓ = k + 2 + m` red strands and a permutation `σ`, the class map
`braidClass σ : V_λ → ConjDual V_{λ ∘ σ}` of the braid functor commutes with every `Fᵢ`
(`braidClass_F_dualAction`). So does `x ↦ B(β x, -)` for every `Fᵢ`-linear `β`. Two such maps
agree once they agree on the pure tensors of weight vectors whose factor `k + 1` is the highest
weight vector (`ext_tensorSpace`). This reduces Corollary 6.10 to its values on those generators.

## Main results

* `braidClass_eq_formDual_comp` : `braidClass σ = formDual ∘ β` from agreement on generators.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR KLRAlgebra KLGamma Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop LusztigF MulOpposite Equiv
open scoped RatFunc

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "𝕂" => RatFunc ℚ
local notation "v" => (RatFunc.X : 𝕂)

variable {I : Type} {k : Type} {Y : Type*} [DecidableEq I] [Field k] [AddCommGroup Y] [Finite I]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
    {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular) {n m : ℕ} (Λ : Fin (n + 2 + m) → I →₀ ℕ)
    (wt : Fin (n + 2 + m) → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))

variable [∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ) (ν : Multiset I),
  Module.Finite k (TensorProductAlgebra k Q Ω ν)]

/-- **Uniqueness step of Corollary 6.10** (Webster, arXiv:1309.3796v2, proof of Corollary 6.10):
if `β : V_λ → V_{λ ∘ σ}` commutes with every `Fᵢ` and `braidClass σ` agrees with `x ↦ B(β x, -)`
on the pure tensors of weight vectors whose factor `n + 1` is the highest weight vector, then
`braidClass σ = formDual ∘ β`. -/
theorem braidClass_eq_formDual_comp (σ : Perm (Fin (n + 2 + m)))
    (β : TensorSpace wt →ₗ[𝕂] TensorSpace (wt ∘ σ))
    (hβ : ∀ (i : I) (z : TensorSpace wt),
      β (tensorRepresentation wt (F R v i) z) = tensorRepresentation (wt ∘ σ) (F R v i) (β z))
    (h : ∀ x : ∀ j, IrreducibleModule R v (wt j).1,
      (∀ j, ∃ ν, x j ∈ depthSpace R (IrreducibleModule R v (wt j).1) (wt j).1 ν) →
      x (Fin.castAdd m (Fin.natAdd n 1)) =
        IrreducibleModule.hwv R v (wt (Fin.castAdd m (Fin.natAdd n 1))).1 →
      braidClass C hQ hR Λ wt hwt σ (PiTensorProduct.tprod 𝕂 x) =
        formDual hR (wt ∘ σ) (β (PiTensorProduct.tprod 𝕂 x))) :
    braidClass C hQ hR Λ wt hwt σ = (formDual hR (wt ∘ σ)).comp β :=
  ext_tensorSpace hR wt (dualAction (wt ∘ σ)) _ _
    (fun i z => braidClass_F_dualAction C hQ hR Λ wt hwt σ i z)
    (fun i z => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hβ, formDual_rho])
    h

end Categorification.Stendhal.FirstWeight
