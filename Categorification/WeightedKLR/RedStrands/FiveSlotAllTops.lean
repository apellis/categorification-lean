/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralFlagInjection
import Categorification.WeightedKLR.RedStrands.FiveSlotNearbyFlagInjection
import Categorification.WeightedKLR.RedStrands.FiveSlotAllBottomStandard
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedHomology

/-!
# The full five-slot kernel map

Webster, arXiv:1309.3796v2, Lemma 6.8 and (6.21). For two equal black strands
and three red strands, every top loading and the full exchanged bottom order
satisfy ordinary injectivity at standard parameters. This gives a monomorphism
on degree-zero derived homology over the full target corner.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR QuantumGroup KL3.Diagram CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

universe w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "κ" => ([0,2,1] : List (Fin 3))
local notation "leftNearby" => TypeA.sadj (Multiset.card μ₀) 2 • fixedTopFourExitCut 0

section Ring

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

private def FixedBottomInjective (t : Seq μ₀) : Prop :=
  Function.Injective (blockKernelColumnInclusion Q Λ t 1 2 fixedTopFourExitBottom).toFun

private theorem fiveSlot_fixedBottom_injective_of_nonviolated
    (hQ : KLRSymm Q) (t : Seq μ₀) (horder : redWord t = [0,1,2]) (hv : ¬ IsViolated t) :
    FixedBottomInjective Q Λ t := by
  have order : redWord t = redWord (fixedTopFourExitCut 0) := horder.trans (by decide)
  obtain ht | hmax | hmid | hleft := fiveSlot_nonviolated_tops t order hv
  · exact fiveSlotRightTop_blockKernelColumnInclusion_injective Q Λ t hQ ht
  · have hi : FixedBottomInjective Q Λ (fixedTopFourExitCut 0) :=
      fiveSlotLeftExtreme_blockKernelColumnInclusion_injective Q Λ fixedTopFourExitBottom
    exact hmax.symm ▸ hi
  · have hi : FixedBottomInjective Q Λ (fixedTopFourExitCut 1) :=
      fiveSlotCentral_blockKernelColumnInclusion_injective Q Λ hQ
    exact hmid.symm ▸ hi
  · have hi : FixedBottomInjective Q Λ leftNearby :=
      fiveSlotNearby_blockKernelColumnInclusion_injective Λ Q hQ
    exact hleft.symm ▸ hi

private def FullKernelInjective (t : Seq μ₀) : Prop :=
  Function.Injective (blockKernelTensorInclusion Q Λ t 1 2 κ).toFun

private theorem fiveSlot_full_injective_of_fixedBottom
    (hQ : KLRSymm Q) (t : Seq μ₀) (horder : redWord t = [0,1,2])
    (assemble : FixedBottomInjective Q Λ t → FullKernelInjective Q Λ t) :
    FullKernelInjective Q Λ t := by
  by_cases hv : IsViolated t
  · exact blockKernelTensorInclusion_injective_of_violated_top Q Λ t 1 2 κ hv
  · exact assemble (fiveSlot_fixedBottom_injective_of_nonviolated Q Λ hQ t horder hv)

end Ring

section Standard

variable {k : Type} [Field k] (C : CartanDatum Unit) (Λ : Fin 3 → Unit →₀ ℕ)
  (t : Seq μ₀)

attribute [local instance 1200] Ring.toIntAlgebra

local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ κ)

/-- At standard parameters, the five-slot kernel map is injective at every
top in the exchanged red order and over the full bottom red order. -/
theorem fiveSlot_blockKernelTensorInclusion_injective_standard_allTops
    (horder : redWord t = [0,1,2]) :
    Function.Injective (blockKernelTensorInclusion Qstd Λ t 1 2 κ).toFun := by
  change FullKernelInjective Qstd Λ t
  have hr : IsRouquierQ C Qstd :=
    ⟨fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim⟩
  have hq : KLRSymm Qstd := fun i j hij => (hij (Subsingleton.elim i j)).elim
  apply fiveSlot_full_injective_of_fixedBottom Qstd Λ hq t horder
  intro both
  exact fiveSlot_blockKernelTensorInclusion_injective_standard_of_twoInterior C Λ hr hq t horder both

set_option backward.isDefEq.respectTransparency false in
/-- The full degree-zero derived kernel map is monic at every five-slot
top in the exchanged red order at standard parameters. -/
theorem fiveSlot_blockKernelDerivedHomology_mono_standard_allTops
    (horder : redWord t = [0,1,2])
    [DG.HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} Uᵐᵒᵖ] :
    Mono ((homologyFunctor (A := Uᵐᵒᵖ) ℤ 0).map
      ((braidingFunctor (k := k) (Q := Qstd) (Λ := Λ) (ν := ν₀) (redWord t) κ).map
        (DG.DerivedCategory.Q.map (blockLoadingKernelInclusionDG Qstd Λ t 1 2)))) := by
  have hi : Function.Injective (blockKernelTensorInclusion Qstd Λ t 1 2 κ).toFun :=
    fiveSlot_blockKernelTensorInclusion_injective_standard_allTops C Λ t horder
  exact blockKernelDerivedHomology_mono Qstd Λ t 1 2 κ hi

end Standard

end Categorification.Stendhal.BraidedStendhalAlgebra
