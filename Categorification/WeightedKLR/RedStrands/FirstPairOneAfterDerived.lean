/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FirstPairOneAfterProjective
import Categorification.WeightedKLR.RedStrands.FirstPairTerminalColumnCancel
import Categorification.WeightedKLR.RedStrands.ProjectiveKernelDerived

/-!
# Derived first-pair braids with one black strand beyond the spectator

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
Both principal higher kernels give degree-zero braid concentration in the
full exchanged red order at standard parameters.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR QuantumGroup KL3.Diagram CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero

attribute [local instance 1200] Ring.toIntAlgebra

universe w

variable {k : Type} [Field k] (C : CartanDatum Unit) (weights : Fin 3 → Unit →₀ ℕ)

local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "κ" => ([1, 0, 2] : List (Fin 3))
local notation "t" side:arg => firstPairOneAfterSpectator side
local notation "T" side:arg =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd weights ν (redWord (t side)))
local notation "U" =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd weights ν κ)

set_option backward.isDefEq.respectTransparency false in
/-- The actual first-pair partial standard at either one-after-spectator loading
has no nonzero cohomology under the full exchanged braid. -/
theorem firstPairOneAfter_partialStandard_braid_homology_vanish_exchanged
    (side : Bool)
    [HasDerivedCategory.{w,0} (T side)ᵐᵒᵖ] [HasDerivedCategory.{w,0} Uᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Qstd weights ν (redWord (t side)) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (T side)ᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd weights (t side) 0 1).X₃)))) := by
  have hQ : KLRSymm Qstd := fun i j hij => (hij (Subsingleton.elim i j)).elim
  exact blockPartialStandard_braid_homology_vanish_of_projective_kernel Qstd weights (t side) 0 1 κ
    (FiveSlotFlag.firstPairOneAfter_blockKernel_projective Qstd weights side hQ)
    (firstPairOneAfter_blockKernelTensorInclusion_injective_standard C weights side) n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
