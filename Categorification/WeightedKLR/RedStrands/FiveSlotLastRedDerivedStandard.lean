/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotLastRedDerived
import Categorification.WeightedKLR.RedStrands.FiveSlotAllTops

/-!
# Standard parameters with the final red on the right, at the five-slot loading

Webster, arXiv:1309.3796v2, Lemma 6.8, (6.21). The two required ordinary
balanced injectivity statements follow from the all-top comparison at the
exchanged red order.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA QuantumGroup KL3.Diagram CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w
variable {k : Type} [Field k] (C : CartanDatum Unit)
local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "N" => Multiset.card (stendhalWeight 3 ν)
local notation "t" => sadj N 3 • (sadj N 2 • fixedTopFourExitCut 2)
local notation "s" => fiveSlotHigherLoading 2
local notation "κ" => ([0,2,1] : List (Fin 3))

set_option quotPrecheck false in
local notation "T" weights:arg =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd weights ν (redWord t))
set_option quotPrecheck false in
local notation "U" weights:arg =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd weights ν κ)

/-- Webster, arXiv:1309.3796v2, Lemma 6.8 after (6.21), with the final red on the right, at the
five-slot loading. The actual partial-standard braid is concentrated in
degree zero at standard parameters and arbitrary red pairings. -/
theorem fiveSlotLastRed_partialStandard_braid_homology_vanish_exchanged
    (weights : Fin 3 → Unit →₀ ℕ)
    [HasDerivedCategory.{w,0} (T weights)ᵐᵒᵖ] [HasDerivedCategory.{w,0} (U weights)ᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := (U weights)ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Qstd weights ν (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (T weights)ᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd weights t 1 2).X₃)))) := by
  have hQ : KLRSymm Qstd := fun i j h => (h (Subsingleton.elim i j)).elim
  exact fiveSlotLastRed_partialStandard_braid_homology_vanish Qstd weights κ hQ
    (fiveSlot_blockKernelTensorInclusion_injective_standard_allTops C weights s (by decide))
    (fiveSlot_blockKernelTensorInclusion_injective_standard_allTops C weights t (by decide)) n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
