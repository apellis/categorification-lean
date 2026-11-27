/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationCutParabolic

/-!
# Naturality of the comparison of the last cut with the parabolic model

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. The
identification `parabolicCutStandardEquiv` of the parabolic standardization with the partial
standardization at the last cut is natural in the module over the factor algebra
(`parabolicCutStandardEquiv_natural`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (θ β : Multiset I)

local notation "D" => cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β

variable {N N' : Type*} [AddCommGroup N] [Module k N]
  [Module (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N]
  [AddCommGroup N'] [Module k N'] [Module (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N']
  [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N']

/-- A map of modules over the factor algebra of the last cut, as a map of modules over the
parabolic factor algebra. -/
def parabolicOfCutHom (g : N →ₗ[D] N') :
    ParabolicOfCut Q Λ θ β N →ₗ[parabolicFactorAlgebra Q Λ θ β] ParabolicOfCut Q Λ θ β N' where
  toFun n := (g n : N')
  map_add' := g.map_add
  map_smul' d n := g.map_smul (parabolicCutFactorEquiv Q Λ θ β d) n

/-- **Naturality of `parabolicCutStandardEquiv`.** -/
theorem parabolicCutStandardEquiv_natural (g : N →ₗ[D] N')
    (z : ParabolicStandard Q Λ θ β (ParabolicOfCut Q Λ θ β N)) :
    parabolicCutStandardEquiv Q Λ θ β N'
        (parabolicStandardMap Q Λ θ β (parabolicOfCutHom Q Λ θ β g) z) =
      cutStandardMap (a := ℓ) (r := 1) Q Λ θ β g (parabolicCutStandardEquiv Q Λ θ β N z) := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  have h := LinearMap.congr_fun (BalancedTensor.ext (f :=
      ((parabolicCutShuffleEquiv Q Λ θ β N').toLinearMap.comp
        ((parabolicShuffleMap Q Λ θ β (parabolicOfCutHom Q Λ θ β g)).restrictScalars k)))
      (g := ((cutShuffleMap (a := ℓ) (r := 1) Q Λ θ β g).restrictScalars k).comp
        (parabolicCutShuffleEquiv Q Λ θ β N).toLinearMap) fun _ _ => rfl) y
  exact (parabolicCutStandardEquiv_mk Q Λ θ β N' _).trans
    ((congrArg Submodule.Quotient.mk h).trans
      (congrArg (cutStandardMap (a := ℓ) (r := 1) Q Λ θ β g)
        (parabolicCutStandardEquiv_mk Q Λ θ β N y)).symm)

end Categorification.Stendhal
