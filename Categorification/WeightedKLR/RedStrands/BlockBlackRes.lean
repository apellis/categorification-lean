/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.Standardization
import Categorification.KLR.CyclotomicAction.Induction
import Categorification.WeightedKLR.RedStrands.ParabolicInputLastStrand
import Categorification.Algebra.PiTensorProductNonUnitalMap
import Categorification.Algebra.InductionAlongRes

/-!
# The functors `ₖEᵢ` on modules over the block algebra

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
functors `ₖEᵢ` before Proposition 5.5, acting on the `k`-th tensor factor. For the block algebra
`B = R(b_0) ⊗ R^{λ_0}(b_1) ⊗ ⋯ ⊗ R^{λ_{ℓ-1}}(b_ℓ)` and a family `b'` which agrees with `b` except
that `b_{k+1} = i + b'_{k+1}`, the last-strand inclusion `R^{λ_k}(b'_{k+1}) → R^{λ_k}(b_{k+1})` on
the `k`-th cyclotomic factor and the identity on the others give a nonunital algebra map
`B' → B` (`blockBlackRes`). For a right `B`-module `M`, `ₖEᵢ M = M e` is restriction along it
(`BlockBlackRes`), where `e` is the image of `1`.

## Main definitions

* `blockFactorRes`, `blockBlackRes`: the factor maps and the map of block algebras.
* `BlockBlackRes`: the right `B'`-module `ₖEᵢ M`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra MulOpposite InductionAlong
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace StendhalAlgebra

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (i : I) (κ : Fin ℓ)
  {b b' : Fin (ℓ + 1) → Multiset I} (h0 : leftBlock b' = leftBlock b)
  (hr : ∀ r, r ≠ κ → rightBlock b' r = rightBlock b r)
  (hκ : {i} + rightBlock b' κ = rightBlock b κ)

omit [DecidableEq I] in
include hκ in
theorem blockBlackRes_weight (r : Fin ℓ) (h : r = κ) : {i} + rightBlock b' r = rightBlock b r := by
  subst h
  exact hκ

/-- The factor maps: the last-strand inclusion on the factor `κ`, the identity elsewhere. -/
def blockFactorRes (r : Fin ℓ) :
    CycKLR k Q (redCyc Λ r) (rightBlock b' r) →ₙₐ[k] CycKLR k Q (redCyc Λ r) (rightBlock b r) :=
  if h : r = κ then
    (CyclotomicAction.castCyc Q (redCyc Λ r)
        (blockBlackRes_weight i κ hκ r h)).toAlgHom.toNonUnitalAlgHom.comp
      (AbsentColour.cyclotomicLast Q i (redCyc Λ r) (rightBlock b' r))
  else (CyclotomicAction.castCyc Q (redCyc Λ r) (hr r h)).toAlgHom.toNonUnitalAlgHom

/-- **The map of block algebras `B' → B`** for `b_{κ+1} = i + b'_{κ+1}`. -/
def blockBlackRes : BlockAlgebra k Q Λ b' →ₙₐ[k] BlockAlgebra k Q Λ b :=
  NonUnitalAlgHom.tensorMap (castKLR Q h0).toAlgHom.toNonUnitalAlgHom
    (PiTensorProduct.nonUnitalMap (blockFactorRes Q Λ i κ hr hκ))

/-- The opposite map, along which right modules restrict. -/
abbrev blockBlackResOp : (BlockAlgebra k Q Λ b')ᵐᵒᵖ →ₙ+* (BlockAlgebra k Q Λ b)ᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom (blockBlackRes Q Λ i κ h0 hr hκ))

variable (M : Type) [AddCommGroup M] [Module k M] [Module (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]
  [IsScalarTower k (BlockAlgebra k Q Λ b)ᵐᵒᵖ M]

/-- **`ₖEᵢ M = M e`** as a right module over the block algebra of `b'`. -/
abbrev BlockBlackRes := Res (blockBlackResOp Q Λ i κ h0 hr hκ) M

instance : Module k (BlockBlackRes Q Λ i κ h0 hr hκ M) :=
  Module.compHom _ (algebraMap k (BlockAlgebra k Q Λ b')ᵐᵒᵖ)

instance : IsScalarTower k (BlockAlgebra k Q Λ b')ᵐᵒᵖ (BlockBlackRes Q Λ i κ h0 hr hκ M) where
  smul_assoc c x m := by
    change (c • x) • m = algebraMap k (BlockAlgebra k Q Λ b')ᵐᵒᵖ c • (x • m)
    rw [show c • x = algebraMap k (BlockAlgebra k Q Λ b')ᵐᵒᵖ c * x from Algebra.smul_def c x,
      mul_smul]

end StendhalAlgebra

end Categorification.Stendhal
