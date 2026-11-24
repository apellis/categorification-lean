/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedHomology
import Categorification.WeightedKLR.RedStrands.FiveSlotAllBottomStandard

/-!
# Degree-zero injectivity for the five-slot braid

Webster, arXiv:1309.3796v2, Lemma 6.8 and (6.21). Standard-parameter
column injectivity controls the degree-zero map for the full target red order.
-/

open CategoryTheory DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR QuantumGroup KL3.Diagram

universe w

attribute [local instance 1200] Ring.toIntAlgebra

variable {k : Type} [Field k] (C : CartanDatum Unit) (Λ : Fin 3 → Unit →₀ ℕ)

local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "t" => fixedTopFourExitCut 2
local notation "κ" => ([0,2,1] : List (Fin 3))
local notation "T" => IsIdempotentElem.Corner
  (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ (redWord t))
local notation "U" => IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Qstd Λ ν₀ κ)

/-- At standard Cartan parameters, the degree-zero map of the full five-slot
braid tensor is monic at the fixed right-extreme top. -/
theorem fiveSlot_blockKernelDerivedHomology_mono_standard
    [DG.HasDerivedCategory.{w, 0} Tᵐᵒᵖ] [DG.HasDerivedCategory.{w, 0} Uᵐᵒᵖ] :
    Mono ((homologyFunctor (A := Uᵐᵒᵖ) ℤ 0).map
      ((braidingFunctor (k := k) (Q := Qstd) (Λ := Λ) (ν := ν₀) (redWord t) κ).map
        (DG.DerivedCategory.Q.map (blockLoadingKernelInclusionDG Qstd Λ t 1 2)))) :=
  blockKernelDerivedHomology_mono Qstd Λ t 1 2 κ
    (fiveSlot_blockKernelTensorInclusion_injective_standard C Λ
      (by constructor <;> intro i j hij <;> exact (hij (Subsingleton.elim i j)).elim)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim))

end Categorification.Stendhal.BraidedStendhalAlgebra
