/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.FiveSlotKernelColumn
import Categorification.KLR.PolNu


/-!
# The full bottom red order at the five-slot top

For the top loading `[0,1,2,i,i]` and bottom red order `[0,2,1]`, the
loading columns assemble to the map in Webster v2, (6.21). There are six
nonviolated bottom loadings. The three consecutive cases use the general
consecutive-column proof and the two-interior case uses the marked four-exit
proof. At standard parameters the one-interior proof covers the other two.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀
local notation "top" => fixedTopFourExitCut 2

/-- The single-interior bottom cut with the other black strand to the right. -/
def fiveSlotOneBlackInteriorRight : Seq μ₀ :=
  Seq.ofList [.inr 0,.inr 2,.inl (),.inr 1,.inl ()] (by decide)

/-- The single-interior bottom cut with the other black strand to the left. -/
def fiveSlotOneBlackInteriorLeft : Seq μ₀ :=
  Seq.ofList [.inr 0,.inl (),.inr 2,.inl (),.inr 1] (by decide)

private def consecutive₁ : Seq μ₀ :=
  Seq.ofList [.inr 0,.inr 2,.inr 1,.inl (),.inl ()] (by decide)
private def consecutive₂ : Seq μ₀ :=
  Seq.ofList [.inr 0,.inl (),.inr 2,.inr 1,.inl ()] (by decide)
private def consecutive₃ : Seq μ₀ :=
  Seq.ofList [.inr 0,.inl (),.inl (),.inr 2,.inr 1] (by decide)

private theorem bottom_cases (u : Seq μ₀) (hu : redWord u=[0,2,1]) :
    IsViolated u ∨ u=consecutive₁ ∨ u=fiveSlotOneBlackInteriorRight ∨
      u=fixedTopFourExitBottom ∨ u=consecutive₂ ∨ u=fiveSlotOneBlackInteriorLeft ∨ u=consecutive₃ := by
  have check : ∀ w : Perm (Fin n₀),
      redWord (w • fixedTopFourExitBottom)=[0,2,1] →
        ((w • fixedTopFourExitBottom).lbl ⟨0,by decide⟩).isLeft ∨
        w • fixedTopFourExitBottom=consecutive₁ ∨
        w • fixedTopFourExitBottom=fiveSlotOneBlackInteriorRight ∨
        w • fixedTopFourExitBottom=fixedTopFourExitBottom ∨
        w • fixedTopFourExitBottom=consecutive₂ ∨
        w • fixedTopFourExitBottom=fiveSlotOneBlackInteriorLeft ∨
        w • fixedTopFourExitBottom=consecutive₃ := by decide +kernel
  obtain ⟨w,rfl⟩ := Seq.exists_smul_eq fixedTopFourExitBottom u
  exact (check w hu).imp_left (fun h => ⟨by decide,h⟩)

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
  (t : Seq μ₀)
local notation "inc" => fun z => blockKernelColumnInclusion Q Λ t 1 2 z

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- For the five-slot bottom red order `[0,2,1]`, it suffices to check the
two one-interior bottom columns and the two-interior bottom column. The top
loading may be any loading of the same black content and red order `[0,1,2]`. -/
theorem fiveSlot_blockKernelTensorInclusion_injective_of_interleaved
    (ht : redWord t = [0,1,2]) (hQ : KLRSymm Q)
    (right : Function.Injective (inc fiveSlotOneBlackInteriorRight))
    (left : Function.Injective (inc fiveSlotOneBlackInteriorLeft))
    (both : Function.Injective (inc fixedTopFourExitBottom)) :
    Function.Injective (blockKernelTensorInclusion Q Λ t 1 2 [0,2,1]) := by
  apply blockKernelTensorInclusion_injective_of_columns
  intro u hu
  have ho (v : Seq μ₀) (hv : redWord v = [0,1,2]) : redWord v = redWord t :=
    hv.trans ht.symm
  let inj := fun u : Seq μ₀ => Function.Injective (inc u)
  have inj₁ : inj consecutive₁ := blockKernelColumnInclusion_injective Q Λ t 1 2
    consecutive₁ hQ [0] [] ht (sadj n₀ 1 • consecutive₁) (ho _ (by decide)) 1
    (by decide) rfl rfl (sadj_smul_smul ..)
  have inj₂ : inj consecutive₂ := blockKernelColumnInclusion_injective Q Λ t 1 2
    consecutive₂ hQ [0] [] ht (sadj n₀ 2 • consecutive₂) (ho _ (by decide)) 2
    (by decide) rfl rfl (sadj_smul_smul ..)
  have inj₃ : inj consecutive₃ := blockKernelColumnInclusion_injective Q Λ t 1 2
    consecutive₃ hQ [0] [] ht (sadj n₀ 3 • consecutive₃) (ho _ (by decide)) 3
    (by decide) rfl rfl (sadj_smul_smul ..)
  change inj u
  rcases bottom_cases u hu with hv | h | h | h | h | h | h
  · exact blockKernelColumnInclusion_injective_of_violated_bottom Q Λ t 1 2 u hv
  · exact (congrArg inj h).mpr inj₁
  · exact (congrArg inj h).mpr right
  · exact (congrArg inj h).mpr both
  · exact (congrArg inj h).mpr inj₂
  · exact (congrArg inj h).mpr left
  · exact (congrArg inj h).mpr inj₃

/-- At the rightmost-black top, the two-interior bottom column is already
injective. The full map reduces to the two one-interior columns. -/
theorem fiveSlot_blockKernelTensorInclusion_injective_of_oneInterior (hQ : KLRSymm Q)
    (right : Function.Injective (blockKernelColumnInclusion Q Λ top 1 2 fiveSlotOneBlackInteriorRight))
    (left : Function.Injective (blockKernelColumnInclusion Q Λ top 1 2 fiveSlotOneBlackInteriorLeft)) :
    Function.Injective (blockKernelTensorInclusion Q Λ top 1 2 [0,2,1]) :=
  fiveSlot_blockKernelTensorInclusion_injective_of_interleaved Q Λ top (by decide) hQ right left
    (fiveSlot_blockKernelColumnInclusion_injective Q Λ hQ)

end Categorification.Stendhal.BraidedStendhalAlgebra
