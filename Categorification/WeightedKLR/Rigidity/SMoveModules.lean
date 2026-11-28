/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.G0Ind
import Categorification.WeightedKLR.RedStrands.PlusStagedTensorRepresented

/-!
# The partial standardizations of the S-move

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof
of Proposition 7.22 (the S-move). For three red strands `(λ_1, λ_2, λ_3)` (in the S-move
`(λ, λ*, λ)`), the two sides of the S-move pairing are the partial standardizations
`𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ −)` (blocks `{1}`, `{2, 3}`) and `𝕊^{λ_1, λ_2; λ_3}(− ⊠ P_∅)`
(blocks `{1, 2}`, `{3}`) of §5.1 (after Definition 5.4). Here `P_∅` is the projective of the
one-red block with no black strands, the regular module of `T^{λ_j}(0)`.

Both are instances of the partial standardization at a cut (`cutStandardFunctor`), composed with
the external tensor product by `P_∅`, and both are exact.

These are left modules over `T^λ(β)`. The reflected (right) form of the second used in the
pairing of §7.3 is obtained by relabelling and reflecting, as for
`BraidedStendhalAlgebra.exteriorStandardizationRight`.

## Main definitions

* `SMove.emptyLeftTensor`, `SMove.emptyRightTensor`: `P_∅ ⊠ −` and `− ⊠ P_∅`.
* `SMove.leftStd`: `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ −)`.
* `SMove.rightStd`: `𝕊^{λ_1, λ_2; λ_3}(− ⊠ P_∅)`.

## Main results

* `SMove.moduleExactFunctor_leftStd`, `SMove.moduleExactFunctor_rightStd`: both are exact.
-/

noncomputable section

namespace Categorification.Stendhal.SMove

open CategoryTheory KLR
open scoped TensorProduct

attribute [local instance] moduleCatScalars moduleCatScalars_isScalarTower

variable {I k : Type} [DecidableEq I] [Field k] (Q : I → I → MvPolynomial (Fin 2) k)
  (hQ : KLRSymm Q)

/-! ### External tensor products with a fixed module -/

section ExtTensorFunctor

variable {A B : Type} [Ring A] [Algebra k A] [Ring B] [Algebra k B]

variable (A) in
/-- `A ⊠ −`: the external tensor product with the regular module of `A`. -/
def regularLeftTensor : ModuleCat.{0} B ⥤ ModuleCat.{0} (A ⊗[k] B) where
  obj X := ModuleCat.of _ (ExtTensor k A X)
  map g := ModuleCat.ofHom (ExtTensor.map (LinearMap.id : A →ₗ[A] A) g.hom)
  map_id _ := ModuleCat.hom_ext ExtTensor.map_id
  map_comp g g' := ModuleCat.hom_ext (by
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      ModuleCat.hom_ofHom, ← ExtTensor.map_comp]
    rfl)

variable (B) in
/-- `− ⊠ B`: the external tensor product with the regular module of `B`. -/
def regularRightTensor : ModuleCat.{0} A ⥤ ModuleCat.{0} (A ⊗[k] B) where
  obj X := ModuleCat.of _ (ExtTensor k X B)
  map g := ModuleCat.ofHom (ExtTensor.map g.hom (LinearMap.id : B →ₗ[B] B))
  map_id _ := ModuleCat.hom_ext ExtTensor.map_id
  map_comp g g' := ModuleCat.hom_ext (by
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      ModuleCat.hom_ofHom, ← ExtTensor.map_comp]
    rfl)

/-- `A ⊠ −` is exact: `A` is flat over the field `k`. -/
theorem moduleExactFunctor_regularLeftTensor :
    ModuleExactFunctor (regularLeftTensor (k := k) A (B := B)) where
  exact f g h := by
    change Function.Exact (ExtTensor.map (k := k) LinearMap.id f.hom)
      (ExtTensor.map (k := k) LinearMap.id g.hom)
    rw [ExtTensor.coe_map_id_right, ExtTensor.coe_map_id_right]
    exact Module.Flat.lTensor_exact A (f := f.hom.restrictScalars k)
      (g := g.hom.restrictScalars k) h
  injective f h := ExtTensor.map_id_injective_right h
  surjective f h := ExtTensor.map_surjective Function.surjective_id h

/-- `− ⊠ B` is exact: `B` is flat over the field `k`. -/
theorem moduleExactFunctor_regularRightTensor :
    ModuleExactFunctor (regularRightTensor (k := k) (A := A) B) where
  exact f g h := by
    change Function.Exact (ExtTensor.map (k := k) f.hom LinearMap.id)
      (ExtTensor.map (k := k) g.hom LinearMap.id)
    rw [ExtTensor.coe_map_id_left, ExtTensor.coe_map_id_left]
    exact Module.Flat.rTensor_exact B (f := f.hom.restrictScalars k)
      (g := g.hom.restrictScalars k) h
  injective f h := ExtTensor.map_id_injective_left h
  surjective f h := ExtTensor.map_surjective h Function.surjective_id

end ExtTensorFunctor

/-! ### Partial standardization at a cut is exact -/

theorem moduleExactFunctor_cutStandardFunctor {a r : ℕ} (Λ : Fin (a + r) → I →₀ ℕ)
    (θ β : Multiset I) {A : Type} [Ring A] [Algebra k A]
    (ψ : A →ₐ[k] TensorProductAlgebra k Q Λ (θ + β)) :
    ModuleExactFunctor (cutStandardFunctor Q hQ Λ θ β ψ) :=
  ⟨fun f g h => cutStandardMap_exact Q Λ θ β hQ f.hom g.hom h,
    fun f h => cutStandardMap_injective Q Λ θ β hQ f.hom h,
    fun f h => cutStandardMap_surjective Q Λ θ β hQ f.hom h⟩

/-! ### The two sides of the S-move -/

section Left

variable (Λ : Fin (1 + (1 + 1)) → I →₀ ℕ) (β : Multiset I)

/-- `P_∅ ⊠ −` for the blocks `{1}`, `{2, 3}`: `P_∅` is the regular module of the one-red
algebra `T^{λ_1}(0)` with no black strands. -/
abbrev emptyLeftTensor :
    ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β) ⥤
      ModuleCat.{0} (cutFactorAlgebra Q Λ 0 β) :=
  regularLeftTensor (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 2) 0)

/-- **`𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ −)`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22; partial standardization of §5.1): from modules over `T^{λ_2, λ_3}(β)` to
modules over `T^{λ_1, λ_2, λ_3}(β)`. -/
def leftStd :
    ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 1) β) ⥤
      ModuleCat.{0} (TensorProductAlgebra k Q Λ β) :=
  emptyLeftTensor Q Λ β ⋙ cutStandardFunctor Q hQ Λ 0 β
    (castTensorProductAlgebra Q Λ (zero_add β).symm).toAlgHom

/-- `𝕊^{λ_1; λ_2, λ_3}(P_∅ ⊠ −)` is exact. -/
theorem moduleExactFunctor_leftStd : ModuleExactFunctor (leftStd Q hQ Λ β) :=
  (moduleExactFunctor_regularLeftTensor (k := k)).comp
    (moduleExactFunctor_cutStandardFunctor Q hQ Λ 0 β _)

end Left

section Right

variable (Λ : Fin (2 + 1) → I →₀ ℕ) (β : Multiset I)

/-- `− ⊠ P_∅` for the blocks `{1, 2}`, `{3}`: `P_∅` is the regular module of the one-red
algebra `T^{λ_3}(0)` with no black strands. -/
abbrev emptyRightTensor :
    ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) β) ⥤
      ModuleCat.{0} (cutFactorAlgebra Q Λ β 0) :=
  regularRightTensor (TensorProductAlgebra k Q (Λ ∘ Fin.natAdd 2) 0)

/-- **`𝕊^{λ_1, λ_2; λ_3}(− ⊠ P_∅)`** (Webster, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.22; partial standardization of §5.1): from modules over `T^{λ_1, λ_2}(β)` to
modules over `T^{λ_1, λ_2, λ_3}(β)`. -/
def rightStd :
    ModuleCat.{0} (TensorProductAlgebra k Q (Λ ∘ Fin.castAdd 1) β) ⥤
      ModuleCat.{0} (TensorProductAlgebra k Q Λ β) :=
  emptyRightTensor Q Λ β ⋙ cutStandardFunctor Q hQ Λ β 0
    (castTensorProductAlgebra Q Λ (add_zero β).symm).toAlgHom

/-- `𝕊^{λ_1, λ_2; λ_3}(− ⊠ P_∅)` is exact. -/
theorem moduleExactFunctor_rightStd : ModuleExactFunctor (rightStd Q hQ Λ β) :=
  (moduleExactFunctor_regularRightTensor (k := k)).comp
    (moduleExactFunctor_cutStandardFunctor Q hQ Λ β 0 _)

end Right

end Categorification.Stendhal.SMove
