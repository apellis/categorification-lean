/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotSpectatorWeight
import Categorification.WeightedKLR.RedStrands.FiveSlotAllBottomStandard
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralFlagInjection
import Categorification.WeightedKLR.RedStrands.FiveSlotNearbyFlagInjection
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedHomology

/-!
# The full five-slot map at all source loadings

Webster, arXiv:1309.3796v2, Lemma 6.8 and (6.21). The fixed two-interior
column tests give ordinary injectivity and a degree-zero derived monomorphism
for every source loading in the exchanged red order at standard parameters.
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

section Ring

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)

private def FullKernelInjective (t : Seq μ₀) : Prop :=
  Function.Injective (blockKernelTensorInclusion Q Λ t 1 2 κ).toFun

private theorem fiveSlot_fullKernelInjective_of_top_cases
    (t : Seq μ₀) (horder : redWord t = [0,1,2])
    (rightTop : FiveSlotRightTop t → FullKernelInjective Q Λ t)
    (central : t = fixedTopFourExitCut 1 → FullKernelInjective Q Λ t)
    (nearby : t = TypeA.sadj μ₀.card 2 • fixedTopFourExitCut 0 → FullKernelInjective Q Λ t) :
    FullKernelInjective Q Λ t := by
  by_cases hv : IsViolated t
  · exact blockKernelTensorInclusion_injective_of_violated_top Q Λ t 1 2 κ hv
  have order : redWord t = redWord (fixedTopFourExitCut 0) := by
    exact horder.trans (by decide)
  obtain ht | hmax | hmid | hleft := fiveSlot_nonviolated_tops t order hv
  · exact rightTop ht
  · have hi : FullKernelInjective Q Λ (fixedTopFourExitCut 0) :=
      blockKernelTensorInclusion_injective_of_columns Q Λ _ 1 2 κ
        (fun s _ => fiveSlotLeftExtreme_blockKernelColumnInclusion_injective Q Λ s)
    exact hmax.symm ▸ hi
  · exact central hmid
  · exact nearby hleft

end Ring

section Standard

variable {k : Type} [Field k] (C : CartanDatum Unit) (Λ : Fin 3 → Unit →₀ ℕ)
  (t : Seq μ₀)

attribute [local instance 1200] Ring.toIntAlgebra

local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ κ)

/-- At standard parameters and spectator multiplicity at most one, the
five-slot kernel map is injective at every top and over the full bottom order. -/
theorem fiveSlot_blockKernelTensorInclusion_injective_of_spectatorWeight_le_one
    (horder : redWord t = [0,1,2]) (small : Λ 0 () ≤ 1) :
    Function.Injective (blockKernelTensorInclusion Qstd Λ t 1 2 κ).toFun := by
  change FullKernelInjective Qstd Λ t
  apply fiveSlot_fullKernelInjective_of_top_cases Qstd Λ t horder
  · intro h
    have hr : IsRouquierQ C Qstd :=
      ⟨fun i j h => (h (Subsingleton.elim i j)).elim,
        fun i j h => (h (Subsingleton.elim i j)).elim,
        fun i j h => (h (Subsingleton.elim i j)).elim⟩
    have hq : KLRSymm Qstd := fun i j hij => (hij (Subsingleton.elim i j)).elim
    exact fiveSlot_blockKernelTensorInclusion_injective_standard_of_twoInterior C Λ hr hq t horder
      (fiveSlotRightTop_blockKernelColumnInclusion_injective Qstd Λ t hq h)
  · intro h
    exact blockKernelTensorInclusion_injective_of_columns Qstd Λ t 1 2 κ
      (fun s _ => fiveSlot_oneBlackBeforePair_columnInclusion_of_spectatorWeight_le_one
        Qstd Λ small t s (Or.inl h))
  · intro h
    exact blockKernelTensorInclusion_injective_of_columns Qstd Λ t 1 2 κ
      (fun s _ => fiveSlot_oneBlackBeforePair_columnInclusion_of_spectatorWeight_le_one
        Qstd Λ small t s (Or.inr h))

set_option backward.isDefEq.respectTransparency false in
/-- At standard parameters, the five-slot kernel inclusion is injective at
every source loading of the original red order, after tensoring with the
full exchanged red-order corner. -/
theorem fiveSlot_blockKernelTensorInclusion_injective_all_tops_standard
    (horder : redWord t = [0,1,2]) :
    Function.Injective (blockKernelTensorInclusion Qstd Λ t 1 2 κ).toFun := by
  change FullKernelInjective Qstd Λ t
  have hr : IsRouquierQ C Qstd :=
    ⟨fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim⟩
  have hq : KLRSymm Qstd := fun i j hij => (hij (Subsingleton.elim i j)).elim
  have assemble (both : Function.Injective (blockKernelColumnInclusion Qstd Λ t 1 2 fixedTopFourExitBottom)) :
      FullKernelInjective Qstd Λ t :=
    fiveSlot_blockKernelTensorInclusion_injective_standard_of_twoInterior C Λ hr hq t horder both
  apply fiveSlot_fullKernelInjective_of_top_cases Qstd Λ t horder
  · intro h
    exact assemble (fiveSlotRightTop_blockKernelColumnInclusion_injective Qstd Λ t hq h)
  · intro h
    subst t
    exact assemble (fiveSlotCentral_blockKernelColumnInclusion_injective Qstd Λ hq)
  · intro h
    subst t
    exact assemble (fiveSlotNearby_blockKernelColumnInclusion_injective Λ Qstd hq)

set_option backward.isDefEq.respectTransparency false in
/-- The corresponding degree-zero derived map is monic over the full
bottom red-order corner. -/
theorem fiveSlot_blockKernelDerivedHomology_mono_of_spectatorWeight_le_one
    (horder : redWord t = [0,1,2]) (small : Λ 0 () ≤ 1)
    [DG.HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} Uᵐᵒᵖ] :
    Mono ((homologyFunctor (A := Uᵐᵒᵖ) ℤ 0).map
      ((braidingFunctor (k := k) (Q := Qstd) (Λ := Λ) (ν := ν₀) (redWord t) κ).map
        (DG.DerivedCategory.Q.map (blockLoadingKernelInclusionDG Qstd Λ t 1 2)))) := by
  have hi : Function.Injective (blockKernelTensorInclusion Qstd Λ t 1 2 κ).toFun :=
    fiveSlot_blockKernelTensorInclusion_injective_of_spectatorWeight_le_one C Λ t horder small
  exact blockKernelDerivedHomology_mono Qstd Λ t 1 2 κ hi


set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero derived braid homology preserves the higher-kernel inclusion
at every five-slot source loading, with unrestricted spectator weight. -/
theorem fiveSlot_blockKernelDerivedHomology_mono_all_tops_standard
    (horder : redWord t = [0,1,2])
    [DG.HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} Uᵐᵒᵖ] :
    Mono ((homologyFunctor (A := Uᵐᵒᵖ) ℤ 0).map
      ((braidingFunctor (k := k) (Q := Qstd) (Λ := Λ) (ν := ν₀) (redWord t) κ).map
        (DG.DerivedCategory.Q.map (blockLoadingKernelInclusionDG Qstd Λ t 1 2)))) :=
  blockKernelDerivedHomology_mono Qstd Λ t 1 2 κ
    (fiveSlot_blockKernelTensorInclusion_injective_all_tops_standard C Λ t horder)

end Standard

end Categorification.Stendhal.BraidedStendhalAlgebra
