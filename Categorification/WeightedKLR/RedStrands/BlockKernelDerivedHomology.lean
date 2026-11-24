/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelTensor
import Categorification.Algebra.DerivedRightTensorHomology
import Categorification.Algebra.DerivedTensorFiltration

/-!
# The degree-zero braid map on the block kernel

For Webster, arXiv:1309.3796v2, Lemma 6.8, equation (6.21), the ordinary test is
injectivity on the tensor of the loading kernel inclusion. This transfers that
input to the degree-zero cohomology map for the actual braid functor. The source
and target are derived categories over the opposite rings of the two red-order
corners.
-/

open CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w u v

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ℓ : ℕ} {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (t : KLR.Seq (stendhalWeight ℓ ν)) (a b : Fin ℓ) (κ : List (Fin ℓ))

local notation "mk" => violMk k Q Λ ν
local notation "E" => mk (redProj k Q Λ ν (redWord t))
local notation "F" => mk (redProj k Q Λ ν κ)
local notation "T" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν κ)
local notation "P" => rIdeal (orderedLoadingIdem Q Λ t)
local notation "K" => blockLoadingKernel Q Λ t a b
local notation "X" => RedBlock.crossingSpace (k := k) E F

private local instance crossingTower : IsScalarTower k T X where
  smul_assoc c r x := Subtype.ext (smul_mul_assoc c r.1 x.1)

private local instance crossingComm : SMulCommClass T k X where
  smul_comm r c x := Subtype.ext (by
    change r.1 * (c • x.1) = c • (r.1 * x.1)
    rw [mul_smul_comm])

private local instance crossingRight : Module Uᵐᵒᵖ X :=
  cornerBimodule.instModuleRight (isIdempotentElem_violMk_redProj k Q Λ ν κ)

private local instance crossingActionsComm : SMulCommClass T Uᵐᵒᵖ X :=
  cornerBimodule.instSMulCommClass (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
    (isIdempotentElem_violMk_redProj k Q Λ ν κ)

private theorem loading_scalar_compatibility (c : k) (p : P) :
    op (algebraMap k T c) • p = c • p := by
  apply Subtype.ext
  apply Subtype.ext
  change p.1.1 * (c • E) = c • p.1.1
  rw [mul_smul_comm, CornerEndomorphism.corner_mul_right _ p.1]

private theorem kernel_scalar_compatibility (c : k) (x : K) :
    op (algebraMap k T c) • x = c • x :=
  Subtype.ext (loading_scalar_compatibility Q Λ t c x.1)

/-- The actual inclusion of the loading kernel as an ordinary dg module map. -/
def blockLoadingKernelInclusionDG : DGModuleCat.of Tᵐᵒᵖ (InDegreeZero K) ⟶
    DGModuleCat.of Tᵐᵒᵖ (InDegreeZero P) :=
  (degreeZeroModuleFunctor Tᵐᵒᵖ).map (ModuleCat.ofHom (K).subtype)


set_option backward.isDefEq.respectTransparency false in
/-- The ordinary BlockKernel inclusion test implies the actual degree-zero braid map is monic. -/
theorem blockKernelDerivedHomology_mono [DG.HasDerivedCategory.{w, max u v} Tᵐᵒᵖ]
    [DG.HasDerivedCategory.{w, max u v} Uᵐᵒᵖ]
    (hi : Function.Injective (blockKernelTensorInclusion Q Λ t a b κ)) :
    Mono ((homologyFunctor (A := Uᵐᵒᵖ) ℤ 0).map
      ((braidingFunctor (k := k) (Q := Q) (Λ := Λ) (ν := ν) (redWord t) κ).map (DG.DerivedCategory.Q.map (blockLoadingKernelInclusionDG Q Λ t a b)))) := by
  let μ : BalancedTensor k k T K X →+ BalancedTensor k k T P X :=
    (blockKernelTensorInclusion Q Λ t a b κ).toAddMonoidHom
  have hμ (x : K) (y : X) : μ (BalancedTensor.tmul x y) =
      BalancedTensor.tmul (blockLoadingKernelInclusionDG Q Λ t a b x) y :=
    blockKernelTensorInclusion_tmul Q Λ t a b κ x y
  have hi' : Function.Injective μ := hi
  exact mono_derivedRightTensorHomology_of_balanced (k := k) (C := T) (C' := U)
    («X» := X) (N := K) («P» := P)
    (kernel_scalar_compatibility Q Λ t a b) (loading_scalar_compatibility Q Λ t)
    (blockLoadingKernelInclusionDG Q Λ t a b) μ hμ hi'

end

end Categorification.Stendhal.BraidedStendhalAlgebra
