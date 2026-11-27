/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.PartialStandardizationCutParabolicNatural
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFunctor
import Categorification.WeightedKLR.RedStrands.PartialStandardizationBlocks
import Categorification.WeightedKLR.RedStrands.BlackIdempotent

/-!
# Transfer from the last cut to the parabolic model along equal weights

Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1. Let `N`
be a module over the factor algebra `T^{λ'}(θ) ⊗ T^{λ_{ℓ+1}}(β)` of the last cut and `X` a
module over the parabolic factor algebra `T^{λ'}(ν) ⊗ R^{λ_{ℓ+1}}(β)`, where `θ = ν`, and let
`f : N ≃ X` intertwine the two actions through the identification of the factor algebras
(`cutParabolicFactorEquiv`). Then the partial standardization of `N` at the last cut is the
parabolic standardization of `X` (`cutParabolicTransfer`), compatibly with the actions of
`T^λ(θ + β) ≅ T^λ(ν + β)` (`cutParabolicTransfer_action`) and naturally in `N` and `X`
(`cutParabolicTransfer_natural`).
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) {θ ν : Multiset I}
  (β : Multiset I) (hw : θ = ν)

/-- The factor algebra of the last cut at `θ` is the parabolic factor algebra at `ν = θ`. -/
def cutParabolicFactorEquiv :
    cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β ≃ₐ[k] parabolicFactorAlgebra Q Λ ν β :=
  (Algebra.TensorProduct.congr (castTensorProductAlgebra Q (Λ ∘ Fin.castSucc) hw)
    AlgEquiv.refl).trans (parabolicCutFactorEquiv Q Λ ν β).symm

theorem cutParabolicFactorEquiv_rfl (d : cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) :
    cutParabolicFactorEquiv Q Λ β rfl d = (parabolicCutFactorEquiv Q Λ θ β).symm d := by
  induction d using TensorProduct.inductionOn with
  | tmul t c => rfl
  | add d d' hd hd' => rw [map_add, map_add, hd, hd']

variable {N X : Type*} [AddCommGroup N] [Module k N]
  [Module (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N]
  [AddCommGroup X] [Module k X] [Module (parabolicFactorAlgebra Q Λ ν β) X]
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ν β) X]

/-- A parabolic standardization of an isomorphism of modules. -/
def parabolicStandardEquivOf {X' : Type*} [AddCommGroup X'] [Module k X']
    [Module (parabolicFactorAlgebra Q Λ ν β) X']
    [IsScalarTower k (parabolicFactorAlgebra Q Λ ν β) X']
    (u : X ≃ₗ[parabolicFactorAlgebra Q Λ ν β] X') :
    ParabolicStandard Q Λ ν β X ≃ₗ[k] ParabolicStandard Q Λ ν β X' :=
  LinearEquiv.ofLinearMap (parabolicStandardMap Q Λ ν β u.toLinearMap)
    (parabolicStandardMap Q Λ ν β u.symm.toLinearMap)
    (by rw [← parabolicStandardMap_comp, u.comp_symm, parabolicStandardMap_id])
    (by rw [← parabolicStandardMap_comp, u.symm_comp, parabolicStandardMap_id])

omit [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N] in
/-- An intertwining isomorphism `N ≃ X` at equal weights, as an isomorphism of modules over the
parabolic factor algebra out of `ParabolicOfCut N`. -/
def parabolicOfCutEquiv {X : Type*} [AddCommGroup X] [Module k X]
    [Module (parabolicFactorAlgebra Q Λ θ β) X] (f : N ≃ₗ[k] X)
    (hf : ∀ (d : cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) (n : N),
      f (d • n) = cutParabolicFactorEquiv Q Λ β rfl d • f n) :
    ParabolicOfCut Q Λ θ β N ≃ₗ[parabolicFactorAlgebra Q Λ θ β] X where
  toFun n := f (show N from n)
  invFun x := (show ParabolicOfCut Q Λ θ β N from f.symm x)
  left_inv := f.symm_apply_apply
  right_inv := f.apply_symm_apply
  map_add' n n' := f.map_add (show N from n) (show N from n')
  map_smul' d n := by
    rw [parabolicOfCut_smul, hf, cutParabolicFactorEquiv_rfl, AlgEquiv.symm_apply_apply]
    rfl

/-- **The partial standardization at the last cut is the parabolic standardization**, along an
isomorphism `N ≃ X` intertwining the actions of the identified factor algebras. -/
def cutParabolicTransfer (f : N ≃ₗ[k] X)
    (hf : ∀ (d : cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) (n : N),
      f (d • n) = cutParabolicFactorEquiv Q Λ β hw d • f n) :
    CutStandard (a := ℓ) (r := 1) Q Λ θ β N ≃ₗ[k] ParabolicStandard Q Λ ν β X := by
  subst hw
  exact (parabolicCutStandardEquiv Q Λ θ β N).symm.trans
    (parabolicStandardEquivOf Q Λ β (parabolicOfCutEquiv Q Λ β f hf))

variable (hQ : KLRSymm Q)

/-- **The transfer is linear over `T^λ(θ + β) ≅ T^λ(ν + β)`.** -/
theorem cutParabolicTransfer_action (f : N ≃ₗ[k] X)
    (hf : ∀ (d : cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) (n : N),
      f (d • n) = cutParabolicFactorEquiv Q Λ β hw d • f n)
    (t : TensorProductAlgebra k Q Λ (θ + β)) (z : CutStandard (a := ℓ) (r := 1) Q Λ θ β N) :
    cutParabolicTransfer Q Λ β hw f hf (cutStandardAction (a := ℓ) (r := 1) Q Λ θ β N hQ t z) =
      parabolicStandardAction Q Λ ν β X hQ
        (castTensorProductAlgebra Q Λ (congrArg (· + β) hw) t)
        (cutParabolicTransfer Q Λ β hw f hf z) := by
  subst hw
  obtain ⟨z, rfl⟩ := (parabolicCutStandardEquiv Q Λ θ β N).surjective z
  change parabolicStandardMap Q Λ θ β (parabolicOfCutEquiv Q Λ β f hf).toLinearMap
      ((parabolicCutStandardEquiv Q Λ θ β N).symm
        (cutStandardAction (a := ℓ) (r := 1) Q Λ θ β N hQ t
          (parabolicCutStandardEquiv Q Λ θ β N z))) =
    parabolicStandardAction Q Λ θ β X hQ t
      (parabolicStandardMap Q Λ θ β (parabolicOfCutEquiv Q Λ β f hf).toLinearMap
        ((parabolicCutStandardEquiv Q Λ θ β N).symm (parabolicCutStandardEquiv Q Λ θ β N z)))
  rw [← parabolicCutStandardEquiv_action, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, parabolicStandardMap_action]

variable {N' X' : Type*} [AddCommGroup N'] [Module k N']
  [Module (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N']
  [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N']
  [AddCommGroup X'] [Module k X'] [Module (parabolicFactorAlgebra Q Λ ν β) X']
  [IsScalarTower k (parabolicFactorAlgebra Q Λ ν β) X']

/-- **Naturality of the transfer.** -/
theorem cutParabolicTransfer_natural (f : N ≃ₗ[k] X)
    (hf : ∀ (d : cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) (n : N),
      f (d • n) = cutParabolicFactorEquiv Q Λ β hw d • f n) (f' : N' ≃ₗ[k] X')
    (hf' : ∀ (d : cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) (n : N'),
      f' (d • n) = cutParabolicFactorEquiv Q Λ β hw d • f' n)
    (g : N →ₗ[cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β] N')
    (g' : X →ₗ[parabolicFactorAlgebra Q Λ ν β] X') (hg : ∀ n, f' (g n) = g' (f n))
    (z : CutStandard (a := ℓ) (r := 1) Q Λ θ β N) :
    cutParabolicTransfer Q Λ β hw f' hf' (cutStandardMap (a := ℓ) (r := 1) Q Λ θ β g z) =
      parabolicStandardMap Q Λ ν β g' (cutParabolicTransfer Q Λ β hw f hf z) := by
  subst hw
  obtain ⟨z, rfl⟩ := (parabolicCutStandardEquiv Q Λ θ β N).surjective z
  change parabolicStandardMap Q Λ θ β (parabolicOfCutEquiv Q Λ β f' hf').toLinearMap
      ((parabolicCutStandardEquiv Q Λ θ β N').symm
        (cutStandardMap (a := ℓ) (r := 1) Q Λ θ β g (parabolicCutStandardEquiv Q Λ θ β N z))) =
    parabolicStandardMap Q Λ θ β g'
      (parabolicStandardMap Q Λ θ β (parabolicOfCutEquiv Q Λ β f hf).toLinearMap
        ((parabolicCutStandardEquiv Q Λ θ β N).symm (parabolicCutStandardEquiv Q Λ θ β N z)))
  rw [← parabolicCutStandardEquiv_natural, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply, ← parabolicStandardMap_comp,
    ← LinearMap.comp_apply, ← parabolicStandardMap_comp]
  congr 2
  exact LinearMap.ext fun n => hg n

end Categorification.Stendhal
