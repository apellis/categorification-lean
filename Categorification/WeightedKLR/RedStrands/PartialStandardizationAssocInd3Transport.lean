/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.BalancedTensorTransport
import Categorification.WeightedKLR.RedStrands.PartialStandardizationAssocInd

/-!
# Transport of one-step induction for three blocks

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, induction, for the one-step induction `Ind3` along
`ι₃ = ι_{ν,ν'+ν''} ∘ (id ⊗ ι_{ν',ν''})` of `PartialStandardizationAssocInd`: isomorphisms of KLR
algebras intertwining the inclusions `ι₃` induce isomorphisms of the one-step inductions
(`ind3Transport`). This is used to compare the two nestings of the cuts of an iterated partial
standardization (Webster, arXiv:1309.3796v3, §5.1), whose one-step models live over the two
alphabets `Fin ((a + m) + r)` and `Fin (a + (m + r))` of red strands.

## Main definitions

* `KLRAlgebra.bimod3Transport`: the isomorphism of the induction bimodules.
* `KLRAlgebra.ind3Transport`: `Ind3 N₁ ≃ Ind3 N₂`, semilinear along the isomorphism of the
  KLR algebras of all strands.
-/

noncomputable section

namespace Categorification.KLR

open scoped TensorProduct
open MulOpposite

namespace KLRAlgebra

variable {I₁ I₂ : Type*} [DecidableEq I₁] [DecidableEq I₂] {k : Type*} [CommRing k]
  {Q₁ : I₁ → I₁ → MvPolynomial (Fin 2) k} {Q₂ : I₂ → I₂ → MvPolynomial (Fin 2) k}
  {ν₁ ν₁' ν₁'' : Multiset I₁} {ν₂ ν₂' ν₂'' : Multiset I₂}
  (σ : KLRAlgebra k Q₁ (ν₁ + (ν₁' + ν₁'')) ≃ₐ[k] KLRAlgebra k Q₂ (ν₂ + (ν₂' + ν₂'')))
  (σ₀ : TensorKLR3 Q₁ ν₁ ν₁' ν₁'' ≃ₐ[k] TensorKLR3 Q₂ ν₂ ν₂' ν₂'')
  (hc : ∀ t, σ (concat3 Q₁ ν₁ ν₁' ν₁'' t) = concat3 Q₂ ν₂ ν₂' ν₂'' (σ₀ t))

include hc in
theorem transport_oneConcat3 : σ (oneConcat3 Q₁ ν₁ ν₁' ν₁'') = oneConcat3 Q₂ ν₂ ν₂' ν₂'' := by
  rw [oneConcat3, hc, map_one]

/-- The isomorphism of the one-step induction bimodules. -/
def bimod3Transport : IndBimod3 Q₁ ν₁ ν₁' ν₁'' ≃ₗ[k] IndBimod3 Q₂ ν₂ ν₂' ν₂'' where
  toFun m := ⟨σ (m : KLRAlgebra k Q₁ (ν₁ + (ν₁' + ν₁''))), by
    change σ m * oneConcat3 Q₂ ν₂ ν₂' ν₂'' = σ m
    rw [← transport_oneConcat3 σ σ₀ hc, ← map_mul, m.2]⟩
  invFun m := ⟨σ.symm (m : KLRAlgebra k Q₂ (ν₂ + (ν₂' + ν₂''))), by
    change σ.symm m * oneConcat3 Q₁ ν₁ ν₁' ν₁'' = σ.symm m
    rw [show oneConcat3 Q₁ ν₁ ν₁' ν₁'' = σ.symm (oneConcat3 Q₂ ν₂ ν₂' ν₂'') from
      (σ.symm_apply_eq.2 (transport_oneConcat3 σ σ₀ hc).symm).symm, ← map_mul, m.2]⟩
  map_add' m m' := Subtype.ext (map_add σ (m : KLRAlgebra k Q₁ (ν₁ + (ν₁' + ν₁''))) m')
  map_smul' c m := Subtype.ext (map_smul σ c (m : KLRAlgebra k Q₁ (ν₁ + (ν₁' + ν₁''))))
  left_inv m := Subtype.ext (σ.symm_apply_apply _)
  right_inv m := Subtype.ext (σ.apply_symm_apply _)

theorem coe_bimod3Transport (m : IndBimod3 Q₁ ν₁ ν₁' ν₁'') :
    ((bimod3Transport σ σ₀ hc m : IndBimod3 Q₂ ν₂ ν₂' ν₂'') :
      KLRAlgebra k Q₂ (ν₂ + (ν₂' + ν₂''))) = σ m := rfl

theorem bimod3Transport_op_smul (t : TensorKLR3 Q₁ ν₁ ν₁' ν₁'') (m : IndBimod3 Q₁ ν₁ ν₁' ν₁'') :
    bimod3Transport σ σ₀ hc (op t • m) = op (σ₀ t) • bimod3Transport σ σ₀ hc m :=
  Subtype.ext (by
    rw [coe_bimod3Transport, coe_op_smul3, coe_op_smul3, unop_op, unop_op, map_mul, hc]; rfl)

theorem bimod3Transport_smul (a : KLRAlgebra k Q₁ (ν₁ + (ν₁' + ν₁'')))
    (m : IndBimod3 Q₁ ν₁ ν₁' ν₁'') :
    bimod3Transport σ σ₀ hc (a • m) = σ a • bimod3Transport σ σ₀ hc m :=
  Subtype.ext (map_mul σ a m)

variable {N₁ N₂ : Type*} [AddCommGroup N₁] [Module k N₁] [Module (TensorKLR3 Q₁ ν₁ ν₁' ν₁'') N₁]
  [AddCommGroup N₂] [Module k N₂] [Module (TensorKLR3 Q₂ ν₂ ν₂' ν₂'') N₂]
  (g : N₁ ≃ₗ[k] N₂) (hg : ∀ (t : TensorKLR3 Q₁ ν₁ ν₁' ν₁'') (n : N₁), g (t • n) = σ₀ t • g n)

/-- **Transport of the one-step induction for three blocks** along isomorphisms of KLR algebras
intertwining the inclusions `ι₃`: `Ind3 N₁ ≃ Ind3 N₂`, semilinear along `σ`. -/
def ind3Transport : Ind3 Q₁ ν₁ ν₁' ν₁'' N₁ ≃ₗ[k] Ind3 Q₂ ν₂ ν₂' ν₂'' N₂ :=
  BalancedTensor.changeRingEquiv σ₀.toRingEquiv (bimod3Transport σ σ₀ hc) g
    (bimod3Transport_op_smul σ σ₀ hc) hg

theorem ind3Transport_tmul (m : IndBimod3 Q₁ ν₁ ν₁' ν₁'') (n : N₁) :
    ind3Transport σ σ₀ hc g hg (BalancedTensor.tmul m n) =
      BalancedTensor.tmul (bimod3Transport σ σ₀ hc m) (g n) := rfl

/-- `ind3Transport` is semilinear along `σ`. -/
theorem ind3Transport_smul (a : KLRAlgebra k Q₁ (ν₁ + (ν₁' + ν₁''))) (y : Ind3 Q₁ ν₁ ν₁' ν₁'' N₁) :
    ind3Transport σ σ₀ hc g hg (a • y) = σ a • ind3Transport σ σ₀ hc g hg y :=
  BalancedTensor.changeRingEquiv_smul _ _ _ _ _ σ.toRingEquiv (bimod3Transport_smul σ σ₀ hc) a y

end KLRAlgebra

end Categorification.KLR
