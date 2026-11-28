/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveModules
import Categorification.WeightedKLR.RedStrands.PartialStandardizationCutParabolic
import Categorification.WeightedKLR.RedStrands.ParabolicStandardFiltration

/-!
# The cut at the last red strand as a standard layer

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. The partial standardization at the cut `{1, …, ℓ} | {ℓ + 1}` is the
standardization of the last red strand (§5.1; library `parabolicCutStandardEquiv`), compatibly
with the action of `T^λ`. So the module `𝕊^{λ_1, λ_2; λ_3}(W ⊠ P_∅)` of the S-move
(`SMove.rightStd`) is the standard layer `S(W ⊠ P_∅)` with no black strand on the last red
strand, the form taken by the Tor lemmas for standardizations.

## Main results

* `cutStandardParabolicEquiv`, `cutStandardParabolicIso`: `𝕊(N) ≅ S(N)` at the last cut,
  over `T^λ(ν)`.
* `SMove.rightStdLayerIso`: `SMove.rightStd W ≅ S(W ⊠ P_∅)`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) {ℓ : ℕ} (Λ : Fin (ℓ + 1) → I →₀ ℕ)

/-- A module over the factor algebra of the last cut, as a factor module of the
standardization of the last red strand. -/
abbrev parabolicOfCutModule {θ β : Multiset I}
    (M : ModuleCat.{0} (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β)) : FactorModule Q Λ θ β :=
  ⟨ParabolicOfCut Q Λ θ β M⟩

theorem parabolicCutStandardEquiv_symm_action {θ β : Multiset I} (N : Type) [AddCommGroup N]
    [Module k N] [Module (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N]
    [IsScalarTower k (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β) N]
    (t : TensorProductAlgebra k Q Λ (θ + β)) (z : CutStandard (a := ℓ) (r := 1) Q Λ θ β N) :
    (parabolicCutStandardEquiv Q Λ θ β N).symm
      (cutStandardAction (a := ℓ) (r := 1) Q Λ θ β N hQ t z) =
      parabolicStandardAction Q Λ θ β (ParabolicOfCut Q Λ θ β N) hQ t
        ((parabolicCutStandardEquiv Q Λ θ β N).symm z) := by
  have h := parabolicCutStandardEquiv_action Q Λ θ β N hQ t
    ((parabolicCutStandardEquiv Q Λ θ β N).symm z)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h, LinearEquiv.symm_apply_apply]

/-- **The cut at the last red strand is the standardization of the last red strand**
(Webster, arXiv:1309.3796v3, §5.1): `𝕊(M) ≅ S(M)` as modules over `T^λ(ν)`, for a split
`θ + β = ν`. -/
def cutStandardParabolicEquiv {θ β ν : Multiset I} (h : θ + β = ν)
    (M : ModuleCat.{0} (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β)) :
    (cutStandardFunctor (a := ℓ) (r := 1) Q hQ Λ θ β
      (castTensorProductAlgebra Q Λ h.symm).toAlgHom).obj M ≃ₗ[
      TensorProductAlgebra k Q Λ ν]
      stdLayerModule Q Λ hQ ⟨θ, β, h, parabolicOfCutModule Q Λ M⟩ where
  toFun z := (parabolicCutStandardEquiv Q Λ θ β M).symm
    (show CutStandard (a := ℓ) (r := 1) Q Λ θ β M from z)
  invFun z := parabolicCutStandardEquiv Q Λ θ β M
    (show ParabolicStandard Q Λ θ β (ParabolicOfCut Q Λ θ β M) from z)
  left_inv z := (parabolicCutStandardEquiv Q Λ θ β M).apply_symm_apply
    (show CutStandard (a := ℓ) (r := 1) Q Λ θ β M from z)
  right_inv z := (parabolicCutStandardEquiv Q Λ θ β M).symm_apply_apply
    (show ParabolicStandard Q Λ θ β (ParabolicOfCut Q Λ θ β M) from z)
  map_add' x y := map_add _ x y
  map_smul' t z :=
    parabolicCutStandardEquiv_symm_action Q hQ Λ M (castTensorProductAlgebra Q Λ h.symm t) z

/-- `cutStandardParabolicEquiv` as an isomorphism in `ModuleCat`. -/
def cutStandardParabolicIso {θ β ν : Multiset I} (h : θ + β = ν)
    (M : ModuleCat.{0} (cutFactorAlgebra (a := ℓ) (r := 1) Q Λ θ β)) :
    (cutStandardFunctor (a := ℓ) (r := 1) Q hQ Λ θ β
      (castTensorProductAlgebra Q Λ h.symm).toAlgHom).obj M ≅
      stdLayerModule Q Λ hQ ⟨θ, β, h, parabolicOfCutModule Q Λ M⟩ :=
  letI := StdLayer.instModule Q Λ hQ ⟨θ, β, h, parabolicOfCutModule Q Λ M⟩
  (cutStandardParabolicEquiv Q hQ Λ h M).toModuleIso

namespace SMove

variable (Λ₃ : Fin (2 + 1) → I →₀ ℕ) (β : Multiset I)

/-- **`𝕊^{λ_1, λ_2; λ_3}(W ⊠ P_∅)` is the standard layer `S(W ⊠ P_∅)`** (Webster,
arXiv:1309.3796v3, §7.3, proof of Proposition 7.22): the S-move module `SMove.rightStd W` is
the standardization of the last red strand with no black strand on it. -/
def rightStdLayerIso (W : ModuleCat.{0} (TensorProductAlgebra k Q (Λ₃ ∘ Fin.castAdd 1) β)) :
    (rightStd Q hQ Λ₃ β).obj W ≅
      stdLayerModule Q Λ₃ hQ
        ⟨β, 0, add_zero β, parabolicOfCutModule Q Λ₃ ((emptyRightTensor Q Λ₃ β).obj W)⟩ :=
  cutStandardParabolicIso Q hQ Λ₃ (add_zero β) ((emptyRightTensor Q Λ₃ β).obj W)

end SMove

end Categorification.Stendhal
