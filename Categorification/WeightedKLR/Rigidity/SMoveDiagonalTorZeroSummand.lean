/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.SMoveDiagonalTorZeroCount
import Categorification.WeightedKLR.Rigidity.SMoveModules

/-!
# The diagonal `Tor₀` of the S-move against the summand `Y₀`

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22, gap (c), the `Tor₀` of the diagonal pair. The partial standardizations
`𝕊(− ⊠ P_∅)` and `𝕊(P_∅ ⊠ −)` of the S-move (`SMove.rightStd`, `SMove.leftStd`) are additive
functors (`SMove.rightStd_additive`, `SMove.leftStd_additive`), so they carry a sum of `|J|`
copies of `Y` to a sum of `|J|` copies of their image. With
`finrank_tensorProductOver_reflectOne_bicone` this gives, for `Z = 𝕊(Y ⊠ P_∅)` and
`Z_J = 𝕊(Y' ⊠ P_∅)` with `Y' ≅ Y^{⊕ J}`,

  `dim (W^r ⊗_T Z_J) = |J| · dim (W^r ⊗_T Z)`

(`SMove.finrank_tensorProductOver_reflectOne_rightStd_bicone`). In the S-move, `Y = S(T e(t) ⊠
Y₀)` and `Y' = S(T e(t) ⊠ R e(u))` (`tensorStdBiconeIsBilimit`), and `Z_J ≅ S_s` is the standard
module of the diagonal loading, so the diagonal `Tor₀` is `dim e(s) W / |J|`. No route
hypotheses.

## Main results

* `SMove.regularRightTensor_additive`, `SMove.regularLeftTensor_additive`.
* `SMove.rightStd_additive`, `SMove.leftStd_additive`.
* `SMove.finrank_tensorProductOver_reflectOne_rightStd_bicone`.
-/

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory CategoryTheory.Limits KLR Equiv BraidedStendhalAlgebra DG

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

section ExtTensorAdditive

variable {k A B : Type} [Field k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]

instance regularRightTensor_additive :
    (regularRightTensor (k := k) (A := A) B).Additive where
  map_add {X Y f g} := ModuleCat.hom_ext (LinearMap.ext fun x => by
    induction x using ExtTensor.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul p q => exact ExtTensor.add_tmul (f.hom p) (g.hom p) q
    | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
        (map_add _ x y).symm))

instance regularLeftTensor_additive :
    (regularLeftTensor (k := k) A (B := B)).Additive where
  map_add {X Y f g} := ModuleCat.hom_ext (LinearMap.ext fun x => by
    induction x using ExtTensor.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | tmul p q => exact ExtTensor.tmul_add p (f.hom q) (g.hom q)
    | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans
        (map_add _ x y).symm))

end ExtTensorAdditive

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

instance rightStd_additive (Λ : Fin (2 + 1) → I →₀ ℕ) (β : Multiset I) :
    (rightStd Q hQ Λ β).Additive := by
  unfold rightStd
  infer_instance

instance leftStd_additive (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (β : Multiset I) :
    (leftStd Q hQ Λ β).Additive := by
  unfold leftStd
  infer_instance

variable (Λ : Fin (2 + 1) → I →₀ ℕ) {ν : Multiset I}
  {ρ : Perm (Fin (Multiset.card (stendhalWeight (2 + 1) ν))) → List ℕ}
  (hρ : TypeA.IsReducedChoice ρ)

/-- **`Tor₀` against a standardized sum counts copies** (Webster, arXiv:1309.3796v3, §7.3,
proof of Proposition 7.22, `Tor₀` on the diagonal): if `Y'` is the sum of `|J|` copies of `Y`
over `T^{λ_1, λ_2}(ν)`, then `dim (W^r ⊗_T 𝕊(Y' ⊠ P_∅)) = |J| · dim (W^r ⊗_T 𝕊(Y ⊠ P_∅))`. -/
theorem finrank_tensorProductOver_reflectOne_rightStd_bicone
    (W : ModuleCat.{0} (TensorProductAlgebra k Q Λ ν))
    (Y : ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) ν)) {J : Type}
    [Fintype J] [DecidableEq J] {b : Bicone (fun _ : J => Y)} (hb : b.IsBilimit) :
    Module.finrank k (TensorProductOver (TensorProductAlgebra k Q Λ ν)
        ((reflectOne (ℓ := 2) Q Λ hQ hρ).obj W) ((rightStd Q hQ Λ ν).obj b.pt)) =
      Fintype.card J * Module.finrank k (TensorProductOver (TensorProductAlgebra k Q Λ ν)
        ((reflectOne (ℓ := 2) Q Λ hQ hρ).obj W) ((rightStd Q hQ Λ ν).obj Y)) :=
  finrank_tensorProductOver_reflectOne_bicone Q Λ hQ hρ W ((rightStd Q hQ Λ ν).obj Y)
    (b := (rightStd Q hQ Λ ν).mapBicone b) (isBilimitOfPreserves (rightStd Q hQ Λ ν) hb)

end Categorification.Stendhal.SMove
