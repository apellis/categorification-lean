/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedNegOne
import Categorification.WeightedKLR.RedStrands.FirstPairTerminalColumnCancel

/-!
# Degree minus one for the first paired red exchange

Webster, arXiv:1309.3796v2, §6.1, Lemma 6.8 and (6.21).
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
local notation "μ" => stendhalWeight 3 ν
local notation "κ" => ([1, 0, 2] : List (Fin 3))
set_option quotPrecheck false in
local notation "corner" order => (isIdempotentElem_violMk_redProj k Qstd weights ν order).Corner

set_option backward.isDefEq.respectTransparency false in
/-- For the first paired exchange at standard rank-one parameters, degree
minus one vanishes at every five-slot loading in source order `[0,1,2]`. -/
theorem firstPair_partialStandard_braid_homology_negOne_allTops_standard
    (t : Seq μ)
    [HasDerivedCategory.{w, 0} (corner (redWord t))ᵐᵒᵖ]
    [HasDerivedCategory.{w, 0} (corner κ)ᵐᵒᵖ]
    (ht : redWord t = [0, 1, 2]) :
    IsZero ((homologyFunctor (A := (corner κ)ᵐᵒᵖ) ℤ (-1)).obj
      ((braidingFunctor k Qstd weights ν (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (corner (redWord t))ᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd weights t 0 1).X₃)))) :=
  blockPartialStandard_braid_homology_negOne_vanish Qstd weights t 0 1 κ
    (firstPair_blockKernelTensorInclusion_injective_standard_allTops (k₀ := k) C weights t ht)

end Categorification.Stendhal.BraidedStendhalAlgebra
