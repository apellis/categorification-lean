/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedHomology
import Categorification.WeightedKLR.RedStrands.FiveSlotKernelColumn

/-!
# Degree-zero braid comparison at the five-slot loading

The ordinary kernel-column result gives the corresponding monomorphism
on degree-zero derived homology for Webster (6.21).
-/

open CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w
variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "topLoading" => fixedTopFourExitCut 2
local notation "botLoading" => fixedTopFourExitBottom
local notation "E" => violMk k Q Λ ν₀ (redProj k Q Λ ν₀ (redWord topLoading))
local notation "F" => violMk k Q Λ ν₀ (ofKLR k Q Λ ν₀ (KLRAlgebra.e botLoading))
local notation "X" => RedBlock.crossingSpace (k := k) E F

local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord topLoading))
local notation "U" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_loading Q Λ botLoading)

private local instance columnCrossingTower : IsScalarTower k T X where
  smul_assoc c r x := Subtype.ext (smul_mul_assoc c r.1 x.1)

private local instance columnCrossingComm : SMulCommClass T k X where
  smul_comm r c x := Subtype.ext (by
    change r.1 * (c • x.1) = c • (r.1 * x.1)
    rw [mul_smul_comm])

private local instance columnCrossingRight : Module Uᵐᵒᵖ X :=
  cornerBimodule.instModuleRight (isIdempotentElem_violMk_loading Q Λ botLoading)

private local instance columnCrossingActionsComm : SMulCommClass T Uᵐᵒᵖ X :=
  cornerBimodule.instSMulCommClass (isIdempotentElem_violMk_redProj k Q Λ ν₀ (redWord topLoading))
    (isIdempotentElem_violMk_loading Q Λ botLoading)

/-- The degree-zero derived kernel map is monic on the five-slot bottom loading. -/
theorem fiveSlot_blockKernelColumnDerivedHomology_mono (hQ : KLRSymm Q)
    [DG.HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} Uᵐᵒᵖ] :
    Mono ((homologyFunctor (A := Uᵐᵒᵖ) ℤ 0).map
      ((derivedRightTensor.{w} T U X).map
        (DG.DerivedCategory.Q.map (blockLoadingKernelInclusionDG Q Λ topLoading 1 2)))) :=
  blockKernelColumnDerivedHomology_mono Q Λ (fixedTopFourExitCut 2) 1 2 fixedTopFourExitBottom
    (fiveSlot_blockKernelColumnInclusion_injective Q Λ hQ)

end

end Categorification.Stendhal.BraidedStendhalAlgebra
