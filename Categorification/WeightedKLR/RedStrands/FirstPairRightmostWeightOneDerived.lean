/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstPairRightmostResidual
import Categorification.WeightedKLR.RedStrands.FirstPairTerminalColumnCancel
import Categorification.WeightedKLR.RedStrands.ProjectiveKernelDerived

/-!
# The rightmost first-pair braid at spectator weight one

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 at (6.21).
The split terminal nilHecke summand gives projectivity of the higher
kernel. Ordinary balanced injectivity then gives derived concentration.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR QuantumGroup KL3.Diagram CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w

variable {k : Type} [Field k] (C : CartanDatum Unit) (weights : Fin 3 → Unit →₀ ℕ)

local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "t" => firstPairTwoAfterSpectator
local notation "κ" => ([1,0,2] : List (Fin 3))

set_option quotPrecheck false in
local notation "corner" order => (isIdempotentElem_violMk_redProj k Qstd weights ν order).Corner

set_option backward.isDefEq.respectTransparency false in
/-- At standard rank-one parameters and final spectator weight one,
the rightmost partial standard has braid cohomology concentrated in
degree zero for the full first-pair exchange. -/
theorem firstPairRightmost_partialStandard_braid_homology_vanish_of_weight_one
    [HasDerivedCategory.{w,0} (corner (redWord t))ᵐᵒᵖ]
    [HasDerivedCategory.{w,0} (corner κ)ᵐᵒᵖ]
    (one : weights 2 () = 1) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := (corner κ)ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Qstd weights ν (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (corner (redWord t))ᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd weights t 0 1).X₃)))) := by
  have hQ : KLRSymm Qstd := fun i j h => (h (Subsingleton.elim i j)).elim
  exact blockPartialStandard_braid_homology_vanish_of_projective_kernel Qstd weights t 0 1 κ
    (firstPairRightmost_blockLoadingKernel_projective_of_weight_one Qstd weights hQ one)
    (firstPairRightmost_blockKernelTensorInclusion_injective_standard (k₀ := k) C weights) n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
