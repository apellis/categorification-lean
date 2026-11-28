/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveCutParabolic
import Categorification.WeightedKLR.Rigidity.SMoveStandardizationTor

/-!
# Factor modules of the last red strand as cut modules

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c). The terms of the resolutions of Proposition 7.8
(`exists_stdResolution`) are sums of standard layers `S(M)`, `M` a module over the parabolic
factor algebra `D_{θ,β}` of the last red strand. The S-move associativity
(`SMove.leftStdCutLayerIso`) takes its input as a partial standardization at the cut
`{1, …, ℓ} | {ℓ + 1}`, over the cut factor algebra. The two factor algebras are identified by
`parabolicCutFactorEquiv`; restricting `M` along its inverse gives a cut module `M'` with
`S(M) ≅ 𝕊(M')` (`stdLayerCutIso`).

## Main results

* `cutOfFactorModule`: the restriction of a factor module to the cut factor algebra.
* `stdLayerCutIso`: `S(M) ≅ 𝕊(M')` for the standardization at the last red strand.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)

/-- A factor module of the last red strand, restricted to the cut factor algebra along the
inverse of `parabolicCutFactorEquiv`. -/
def cutOfFactorModule {θ β : Multiset I} (M : FactorModule Q Λ θ β) :
    ModuleCat.{0} (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) :=
  (ModuleCat.restrictScalars (parabolicCutFactorEquiv Q Λ θ β).symm.toRingEquiv.toRingHom).obj
    (ModuleCat.of (parabolicFactorAlgebra Q Λ θ β) M.carrier)

/-- The identity of `M`, as an isomorphism of factor modules onto the factor module of its
cut restriction. -/
def factorCutLinearEquiv {θ β : Multiset I} (M : FactorModule Q Λ θ β) :
    M.carrier ≃ₗ[parabolicFactorAlgebra Q Λ θ β]
      (parabolicOfCutModule Q Λ (cutOfFactorModule Q Λ M)).carrier where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' d m := by
    change d • m = (parabolicCutFactorEquiv Q Λ θ β).symm
      ((parabolicCutFactorEquiv Q Λ θ β) d) • m
    rw [AlgEquiv.symm_apply_apply]

/-- **`S(M) ≅ 𝕊(M')`** (Webster, arXiv:1309.3796v3, §5.1; §7.3, proof of Proposition 7.22):
the standard layer of a factor module of the last red strand is the partial standardization at
the cut `{1, …, ℓ} | {ℓ + 1}` of its cut restriction `M'` (`cutOfFactorModule`). -/
def stdLayerCutIso {θ β ν : Multiset I} (h : θ + β = ν) (M : FactorModule Q Λ θ β) :
    stdLayerModule Q Λ hQ ⟨θ, β, h, M⟩ ≅
      (cutStandardFunctor (a := ℓ) (r := 1) Q hQ Λ θ β
        (castTensorProductAlgebra Q Λ h.symm).toAlgHom).obj (cutOfFactorModule Q Λ M) :=
  stdLayerIso Q Λ hQ h (factorCutLinearEquiv Q Λ M) ≪≫
    (cutStandardParabolicIso Q hQ Λ h (cutOfFactorModule Q Λ M)).symm

end Categorification.Stendhal
