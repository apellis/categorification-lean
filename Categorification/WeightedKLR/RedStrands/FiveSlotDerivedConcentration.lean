/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralPrincipalDerived
import Categorification.WeightedKLR.RedStrands.FiveSlotLastRedDerivedStandard
import Categorification.WeightedKLR.RedStrands.FiveSlotLeftDerived
import Categorification.WeightedKLR.RedStrands.FiveSlotMiddleRightResidual
import Categorification.WeightedKLR.RedStrands.FiveSlotRightmostDerivedStandard

/-!
# Braid concentration at all five-slot loadings

Webster, arXiv:1309.3796v2, Lemma 6.8 after (6.21).
An ordered five-slot loading which survives violation is one of six
configurations. In the exchanged red order, each configuration has zero
derived braid homology outside degree zero.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR TypeA QuantumGroup KL3.Diagram CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w
local notation "ν" => ({()} + {()} : Multiset Unit)
local notation "μ" => stendhalWeight 3 ν
local notation "κ" => ([0, 2, 1] : List (Fin 3))

private theorem violated_kernel_eq_bot {k : Type} [CommRing k]
    (Q : Unit → Unit → MvPolynomial (Fin 2) k) (weights : Fin 3 → Unit →₀ ℕ)
    (t : Seq μ) (ht : IsViolated t) : blockLoadingKernel Q weights t 1 2 = ⊥ := by
  have hzero : orderedLoadingIdem Q weights t = 0 := by
    apply Subtype.ext
    exact violMk_e ht
  apply le_antisymm _ bot_le
  intro x _
  rw [Submodule.mem_bot]
  apply Subtype.ext
  calc
    x.1 = orderedLoadingIdem Q weights t * x.1 := x.2.symm
    _ = 0 := (congrArg (fun e => e * x.1) hzero).trans (zero_mul _)

variable {k : Type} [Field k] (C : CartanDatum Unit) (weights : Fin 3 → Unit →₀ ℕ)

local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "T" t:arg =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd weights ν (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd weights ν κ)

set_option backward.isDefEq.respectTransparency false in
/-- At standard rank-one parameters, the braid of every actual five-slot
partial standard is concentrated in degree zero in the exchanged red order. -/
theorem fiveSlot_partialStandard_braid_homology_vanish_all_tops_standard
    (t : Seq μ)
    [HasDerivedCategory.{w, 0} (T t)ᵐᵒᵖ] [HasDerivedCategory.{w, 0} Uᵐᵒᵖ]
    (order : redWord t = [0, 1, 2]) (n : ℤ) (hn : n ≠ 0) :
    IsZero ((homologyFunctor (A := Uᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Qstd weights ν (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (T t)ᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd weights t 1 2).X₃)))) := by
  by_cases violated : IsViolated t
  · exact blockPartialStandard_braid_homology_vanish_of_bot Qstd weights t 1 2 κ
      (violated_kernel_eq_bot Qstd weights t violated) n hn
  have sourceOrder : redWord t = redWord (fixedTopFourExitCut 0) := order.trans (by decide)
  obtain hr | rfl | rfl | rfl := fiveSlot_nonviolated_tops t sourceOrder violated
  · rcases hr with rfl | rfl | rfl
    · exact fiveSlotRightmost_partialStandard_braid_homology_vanish_exchanged C weights n hn
    · exact fiveSlotMiddleRight_partialStandard_braid_homology_vanish_standard C weights n hn
    · exact fiveSlotLastRed_partialStandard_braid_homology_vanish_exchanged C weights n hn
  · exact blockPartialStandard_braid_homology_vanish_of_bot Qstd weights
      (fixedTopFourExitCut 0) 1 2 κ (fiveSlotLeftExtreme_blockLoadingKernel_eq_bot Qstd weights) n hn
  · exact fiveSlotCentral_partialStandard_braid_homology_vanish_exchanged
      (C₀ := C) (F₀ := k) weights n hn
  · exact fiveSlotNextRetainedPartialStandard_braid_homology_vanish_exchanged
      (C₀ := C) (F₀ := k) weights n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
