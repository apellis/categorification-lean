/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotAllBottom
import Categorification.WeightedKLR.RedStrands.InterleavedMarkedColumnStandard

/-!
# Five-slot injectivity at standard parameters

Standard one-interior injectivity supplies the two remaining bottom columns
for the fixed top loading `[0,1,2,i,i]`.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra QuantumGroup KL3.Diagram
local notation "n" => Multiset.card (stendhalWeight 3 ({()} + {()} : Multiset Unit))
local notation "top" => fixedTopFourExitCut 2

/-- At standard parameters, the two-interior bottom column is the only
column that needs a separate injectivity proof. -/
theorem fiveSlot_blockKernelTensorInclusion_injective_standard_of_twoInterior {k : Type} [Field k]
    (C : CartanDatum Unit) (Λ : Fin 3 → Unit →₀ ℕ)
    (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    (hQ : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    (t : Seq (stendhalWeight 3 ({()} + {()} : Multiset Unit)))
    (ht : redWord t = [0,1,2])
    (both : Function.Injective (blockKernelColumnInclusion
      (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ t 1 2 fixedTopFourExitBottom)) :
    Function.Injective (blockKernelTensorInclusion
      (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Λ t 1 2 [0,2,1]) := by
  refine fiveSlot_blockKernelTensorInclusion_injective_of_interleaved _ Λ t ht hQ ?_ ?_ both
  · exact interleaved_markedColumn_injective_standard C Λ hR hQ t
      fiveSlotOneBlackInteriorRight 1 2 1 (by decide) (i := ()) (Lr := [0]) (Mr := [])
      ht rfl rfl rfl ((by decide : redWord (TypeA.wordProd n [1,2,1] • fiveSlotOneBlackInteriorRight)
        = [0,1,2]).trans ht.symm)
  · exact interleaved_markedColumn_injective_standard C Λ hR hQ t
      fiveSlotOneBlackInteriorLeft 1 2 2 (by decide) (i := ()) (Lr := [0]) (Mr := [])
      ht rfl rfl rfl ((by decide : redWord (TypeA.wordProd n [2,3,2] • fiveSlotOneBlackInteriorLeft)
        = [0,1,2]).trans ht.symm)

/-- At standard parameters over a field, every bottom loading with the
opposite pair order contributes injectively to the fixed five-slot top. -/
theorem fiveSlot_blockKernelTensorInclusion_injective_standard {k : Type} [Field k]
    (C : CartanDatum Unit) (Λ : Fin 3 → Unit →₀ ℕ)
    (hR : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)))
    (hQ : KLRSymm (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) :
    Function.Injective
      (blockKernelTensorInclusion (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))
        Λ top 1 2 [0,2,1]) :=
  fiveSlot_blockKernelTensorInclusion_injective_standard_of_twoInterior C Λ hR hQ top (by decide)
    (fiveSlot_blockKernelColumnInclusion_injective _ Λ hQ)

end Categorification.Stendhal.BraidedStendhalAlgebra
