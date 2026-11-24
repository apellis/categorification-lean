/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotAllBottomStandard
import Categorification.WeightedKLR.RedStrands.FiveSlotNearbyFlagInjection
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralKernelProjective
import Categorification.WeightedKLR.RedStrands.ProjectiveKernelDerived

/-!
# Derived braid concentration at the nearby five-slot loading

Webster, arXiv:1309.3796v2, Lemma 6.8 and (6.21).
The full balanced inclusion and a projective higher kernel give concentration
in degree zero for the braid of the nearby partial standard.
-/

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open KLR QuantumGroup KL3.Diagram
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
attribute [local instance 1200] Ring.toIntAlgebra

universe w

variable {k : Type} [Field k] (D : CartanDatum Unit) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "t" => TypeA.sadj (Multiset.card (stendhalWeight 3 ν₀)) 2 • fixedTopFourExitCut 0
local notation "oppositeWord" => ([0, 2, 1] : List (Fin 3))
local notation "T" => (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ (redWord t)).Corner
local notation "U" κ:arg => (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ κ).Corner

private theorem standardRouquier : IsRouquierQ D Qstd := by
  constructor <;> intro i j hij <;> exact (hij (Subsingleton.elim i j)).elim

private theorem standardSymm : KLRSymm Qstd :=
  fun i j hij => (hij (Subsingleton.elim i j)).elim

set_option backward.isDefEq.respectTransparency false in
/-- For any bottom red word, concentration of the actual nearby partial
standard follows once ordinary balanced injectivity has been proved. -/
theorem fiveSlotNearby_partialStandard_braid_homology_vanish_of_balanced_standard
    (κ : List (Fin 3))
    [HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [HasDerivedCategory.{w, 0} (U κ)ᵐᵒᵖ]
    (hbal : Function.Injective (blockKernelTensorInclusion Qstd Λ t 1 2 κ))
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := (U κ)ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Qstd Λ ν₀ (redWord t) κ).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd Λ t 1 2).X₃)))) := by
  have hP : Module.Projective Tᵐᵒᵖ (blockLoadingKernel Qstd Λ t 1 2) :=
    fiveSlotNearby_kernel_projective_standard (standardRouquier (k := k) D)
      (standardSymm (k := k) D) Λ
  exact blockPartialStandard_braid_homology_vanish_of_projective_kernel Qstd Λ t 1 2 κ hP hbal n hn

set_option backward.isDefEq.respectTransparency false in
/-- At standard Khovanov–Lauda parameters, the braid to the exchanged red
order has no nonzero-degree homology at the nearby two-black partial standard. -/
theorem fiveSlotNearby_partialStandard_braid_homology_vanish_standard
    [HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [HasDerivedCategory.{w, 0} (U oppositeWord)ᵐᵒᵖ]
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DG.DerivedCategory.homologyFunctor (A := (U oppositeWord)ᵐᵒᵖ) ℤ n).obj
      ((braidingFunctor k Qstd Λ ν₀ (redWord t) oppositeWord).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor Tᵐᵒᵖ).obj
          (blockLoadingShortComplex Qstd Λ t 1 2).X₃)))) := by
  have hR : IsRouquierQ D Qstd := standardRouquier (k := k) D
  have hQ : KLRSymm Qstd := standardSymm (k := k) D
  have hbal : Function.Injective (blockKernelTensorInclusion Qstd Λ t 1 2 oppositeWord) :=
    fiveSlot_blockKernelTensorInclusion_injective_standard_of_twoInterior D Λ hR hQ t (by decide)
      (fiveSlotNearby_blockKernelColumnInclusion_injective Λ Qstd hQ)
  exact fiveSlotNearby_partialStandard_braid_homology_vanish_of_balanced_standard
    D Λ oppositeWord hbal n hn

end Categorification.Stendhal.BraidedStendhalAlgebra
