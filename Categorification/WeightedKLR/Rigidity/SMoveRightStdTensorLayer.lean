/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveCutParabolic
import Categorification.WeightedKLR.RedStrands.ParabolicStandardTensorProj
import Categorification.WeightedKLR.Rigidity.SMoveStandardizationTor

/-!
# The right side of the S-move as `S(W ⊠ R e(∅))`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22. `SMove.rightStdLayerIso` identifies `𝕊^{λ_1, λ_2; λ_3}(W ⊠ P_∅)` with the
standard layer of the factor module `W ⊠ T^{λ_3}(0)`, seen over the parabolic factor algebra
`T^{λ_1, λ_2}(β) ⊗ R^{λ_3}(0)` through `parabolicCutFactorEquiv`. Here this factor module is
identified with `W ⊠ R^{λ_3}(0) e(∅)`, the form `S(W ⊠ R e(u))` (`tensorLayer`) in which the
standard filtration of `W` passes to the standard layer with the black counts of its labels
(`hasFiltration_tensorLayer_standard`).

## Main definitions

* `SMove.rightEmptyFactorEquiv`: `W ⊠ T^{λ_3}(0) ≅ W ⊠ R^{λ_3}(0) e(∅)` over the parabolic
  factor algebra.
* `SMove.rightStdTensorLayerIso`: `SMove.rightStd W ≅ S(W ⊠ R e(∅))`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory KLR
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q) (Λ : Fin (2 + 1) → I →₀ ℕ) (β : Multiset I)

/-- The cyclotomic factor of `parabolicCutFactorEquiv`. -/
abbrev lastCycEquiv :
    CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last 2) j) 0 ≃ₐ[k]
      TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 2) 0 :=
  (SingleRed.cyclotomicEquiv Q (fun _ : Fin 1 => Λ (Fin.last 2)) 0).trans
    (tensorProductAlgebraCast Q (congrArg (Λ ∘ ·) lastIndex_eq_natAdd) 0)

/-- The `k`-linear identification `T^{λ_3}(0) ≅ R^{λ_3}(0) e(∅)`. -/
def lastEmptyLinearEquiv (u : Seq (0 : Multiset I)) :
    TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 2) 0 ≃ₗ[k] KMod (k := k) (cycProj Q Λ 0 u) :=
  (lastCycEquiv Q Λ).symm.toLinearEquiv.trans
    ((cycProjZeroEquiv Q Λ u).restrictScalars k)

theorem lastEmptyLinearEquiv_mul (u : Seq (0 : Multiset I))
    (c : CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last 2) j) 0)
    (y : TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 2) 0) :
    lastEmptyLinearEquiv Q Λ u (lastCycEquiv Q Λ c * y) =
      c • lastEmptyLinearEquiv Q Λ u y := by
  change cycProjZeroEquiv Q Λ u ((lastCycEquiv Q Λ).symm (lastCycEquiv Q Λ c * y)) =
    c • cycProjZeroEquiv Q Λ u ((lastCycEquiv Q Λ).symm y)
  rw [map_mul, AlgEquiv.symm_apply_apply, ← (cycProjZeroEquiv Q Λ u).map_smul]
  rfl

/-- The `k`-linear map `W ⊠ T^{λ_3}(0) → W ⊠ R^{λ_3}(0) e(∅)`. -/
abbrev rightEmptyLinearEquiv
    (W : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) β))
    (u : Seq (0 : Multiset I)) :
    ExtTensor k W (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 2) 0) ≃ₗ[k]
      ExtTensor k (KMod (k := k) W) (KMod (k := k) (cycProj Q Λ 0 u)) :=
  TensorProduct.congr (LinearEquiv.refl k W) (lastEmptyLinearEquiv Q Λ u)

theorem rightEmptyLinearEquiv_smul
    (W : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) β))
    (u : Seq (0 : Multiset I)) (a : TensorProductAlgebra k Q (Λ ∘ Fin.castSucc) β)
    (c : CycKLR k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ (Fin.last 2) j) 0)
    (x : ExtTensor k W (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 2) 0)) :
    rightEmptyLinearEquiv Q Λ β W u ((a ⊗ₜ[k] lastCycEquiv Q Λ c) • x) =
      (a ⊗ₜ[k] c) • rightEmptyLinearEquiv Q Λ β W u x := by
  induction x using ExtTensor.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x x' hx hx' => rw [smul_add, map_add, hx, hx', map_add, smul_add]
  | tmul w y =>
    rw [ExtTensor.smul_tmul]
    change (a • w) ⊗ₜ[k] lastEmptyLinearEquiv Q Λ u (lastCycEquiv Q Λ c * y) =
      (a ⊗ₜ[k] c) • ExtTensor.tmul (k := k) (show KMod (k := k) W from w)
        (lastEmptyLinearEquiv Q Λ u y)
    rw [ExtTensor.smul_tmul, lastEmptyLinearEquiv_mul]
    rfl

/-- **`W ⊠ T^{λ_3}(0) ≅ W ⊠ R^{λ_3}(0) e(∅)`** as modules over the parabolic factor algebra
`T^{λ_1, λ_2}(β) ⊗ R^{λ_3}(0)`. -/
def rightEmptyFactorEquiv (W : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) β))
    (u : Seq (0 : Multiset I)) :
    (parabolicOfCutModule Q Λ ((emptyRightTensor Q Λ β).obj W)).carrier ≃ₗ[
      parabolicFactorAlgebra Q Λ β 0] (tensorFactor Q Λ W (cycProj Q Λ 0 u)).carrier where
  toFun x := rightEmptyLinearEquiv Q Λ β W u x
  invFun x := (rightEmptyLinearEquiv Q Λ β W u).symm x
  left_inv x := (rightEmptyLinearEquiv Q Λ β W u).left_inv x
  right_inv x := (rightEmptyLinearEquiv Q Λ β W u).right_inv x
  map_add' x y := map_add (rightEmptyLinearEquiv Q Λ β W u) x y
  map_smul' d x := by
    rw [RingHom.id_apply]
    induction d using TensorProduct.inductionOn with
    | add d d' hd hd' => rw [add_smul, map_add, hd, hd', add_smul]
    | tmul a c =>
      rw [parabolicOfCut_smul]
      exact rightEmptyLinearEquiv_smul Q Λ β W u a c x

/-- **`𝕊^{λ_1, λ_2; λ_3}(W ⊠ P_∅) ≅ S(W ⊠ R e(∅))`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22): the right side of the S-move in the form `tensorLayer`, with no black strand
on the last red strand. -/
def rightStdTensorLayerIso
    (W : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) β))
    (u : Seq (0 : Multiset I)) :
    (rightStd Q hQ Λ β).obj W ≅
      stdLayerModule Q Λ hQ (tensorLayer Q Λ (add_zero β) W (cycProj Q Λ 0 u)) :=
  rightStdLayerIso Q hQ Λ β W ≪≫ stdLayerIso Q Λ hQ (add_zero β) (rightEmptyFactorEquiv Q Λ β W u)

end Categorification.Stendhal.SMove
