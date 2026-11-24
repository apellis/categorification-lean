/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelColumn
import Categorification.WeightedKLR.RedStrands.InterleavedMarkedColumnStandard
import Categorification.KLR.PolNu


/-!
# Bottom column reduction for the first exchanged red pair

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
Only the bottom column with both black strands between the exchanged
reds requires a separate cancellation argument at standard parameters.
-/

noncomputable section
namespace Categorification.Stendhal.BraidedStendhalAlgebra
open KLR KLRAlgebra TypeA Equiv

local notation "ν₀" => ({()} + {()} : Multiset Unit)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "n₀" => Multiset.card μ₀


section Ring

/-- The single-interior bottom cut with the other black strand to the right. -/
def firstPairBottomOneInteriorRight : Seq μ₀ :=
  Seq.ofList [.inr 1,.inl (),.inr 0,.inr 2,.inl ()] (by decide)

/-- The single-interior bottom cut with the other black strand to the left. -/
def firstPairBottomOneInteriorLeft : Seq μ₀ :=
  Seq.ofList [.inr 1,.inl (),.inr 0,.inl (),.inr 2] (by decide)

/-- The remaining bottom column has two black strands between the exchanged reds. -/
def firstPairBottomTwoInterior : Seq μ₀ :=
  Seq.ofList [.inr 1, .inl (), .inl (), .inr 0, .inr 2] (by decide)

private def consecutive₁ : Seq μ₀ :=
  Seq.ofList [.inr 1,.inr 0,.inr 2,.inl (),.inl ()] (by decide)
private def consecutive₂ : Seq μ₀ :=
  Seq.ofList [.inr 1,.inr 0,.inl (),.inr 2,.inl ()] (by decide)
private def consecutive₃ : Seq μ₀ :=
  Seq.ofList [.inr 1,.inr 0,.inl (),.inl (),.inr 2] (by decide)

private theorem bottom_cases (u : Seq μ₀) (hu : redWord u=[1,0,2]) :
    IsViolated u ∨ u=consecutive₁ ∨ u=firstPairBottomOneInteriorRight ∨
      u=firstPairBottomTwoInterior ∨ u=consecutive₂ ∨ u=firstPairBottomOneInteriorLeft ∨ u=consecutive₃ := by
  have check : ∀ w : Perm (Fin n₀),
      redWord (w • firstPairBottomTwoInterior)=[1,0,2] →
        ((w • firstPairBottomTwoInterior).lbl ⟨0,by decide⟩).isLeft ∨
        w • firstPairBottomTwoInterior=consecutive₁ ∨
        w • firstPairBottomTwoInterior=firstPairBottomOneInteriorRight ∨
        w • firstPairBottomTwoInterior=firstPairBottomTwoInterior ∨
        w • firstPairBottomTwoInterior=consecutive₂ ∨
        w • firstPairBottomTwoInterior=firstPairBottomOneInteriorLeft ∨
        w • firstPairBottomTwoInterior=consecutive₃ := by decide +kernel
  obtain ⟨w,rfl⟩ := Seq.exists_smul_eq firstPairBottomTwoInterior u
  exact (check w hu).imp_left (fun h => ⟨by decide,h⟩)

variable {k : Type} [CommRing k]
  (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
  (t : Seq μ₀)
local notation "inc" => fun z => blockKernelColumnInclusion Q Λ t 0 1 z

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

/-- For the five-slot bottom red order `[1,0,2]`, it suffices to check the
two one-interior bottom columns and the two-interior bottom column. The top
loading may be any loading of the same black content and red order `[0,1,2]`. -/
theorem firstPair_blockKernelTensorInclusion_injective_of_interleaved
    (ht : redWord t = [0,1,2]) (hQ : KLRSymm Q)
    (right : Function.Injective (inc firstPairBottomOneInteriorRight))
    (left : Function.Injective (inc firstPairBottomOneInteriorLeft))
    (both : Function.Injective (inc firstPairBottomTwoInterior)) :
    Function.Injective (blockKernelTensorInclusion Q Λ t 0 1 [1,0,2]) := by
  apply blockKernelTensorInclusion_injective_of_columns
  intro u hu
  have ho (v : Seq μ₀) (hv : redWord v = [0,1,2]) : redWord v = redWord t :=
    hv.trans ht.symm
  let inj := fun u : Seq μ₀ => Function.Injective (inc u)
  have inj₁ : inj consecutive₁ := blockKernelColumnInclusion_injective Q Λ t 0 1
    consecutive₁ hQ [] [2] ht (sadj n₀ 0 • consecutive₁) (ho _ (by decide)) 0
    (by decide) rfl rfl (sadj_smul_smul ..)
  have inj₂ : inj consecutive₂ := blockKernelColumnInclusion_injective Q Λ t 0 1
    consecutive₂ hQ [] [2] ht (sadj n₀ 0 • consecutive₂) (ho _ (by decide)) 0
    (by decide) rfl rfl (sadj_smul_smul ..)
  have inj₃ : inj consecutive₃ := blockKernelColumnInclusion_injective Q Λ t 0 1
    consecutive₃ hQ [] [2] ht (sadj n₀ 0 • consecutive₃) (ho _ (by decide)) 0
    (by decide) rfl rfl (sadj_smul_smul ..)
  change inj u
  rcases bottom_cases u hu with hv | h | h | h | h | h | h
  · exact blockKernelColumnInclusion_injective_of_violated_bottom Q Λ t 0 1 u hv
  · exact (congrArg inj h).mpr inj₁
  · exact (congrArg inj h).mpr right
  · exact (congrArg inj h).mpr both
  · exact (congrArg inj h).mpr inj₂
  · exact (congrArg inj h).mpr left
  · exact (congrArg inj h).mpr inj₃

end Ring

section Standard

open QuantumGroup KL3.Diagram

variable {k : Type} [Field k] (C : CartanDatum Unit) (Λ : Fin 3 → Unit →₀ ℕ)
  (t : Seq μ₀)

local notation "Qstd" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)

/-- At standard parameters all bottom columns of the first-pair exchange
are injective once the actual two-interior column is injective. -/
theorem firstPair_blockKernelTensorInclusion_injective_standard_of_twoInterior
    (ht : redWord t = [0, 1, 2])
    (both : Function.Injective (blockKernelColumnInclusion Qstd Λ t 0 1 firstPairBottomTwoInterior)) :
    Function.Injective (blockKernelTensorInclusion Qstd Λ t 0 1 [1, 0, 2]) := by
  have hR : IsRouquierQ C Qstd :=
    ⟨fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim,
      fun i j h => (h (Subsingleton.elim i j)).elim⟩
  have hQ : KLRSymm Qstd := fun i j h => (h (Subsingleton.elim i j)).elim
  refine firstPair_blockKernelTensorInclusion_injective_of_interleaved Qstd Λ t ht hQ ?_ ?_ both
  · exact interleaved_markedColumn_injective_standard C Λ hR hQ t
      firstPairBottomOneInteriorRight 0 1 0 (by decide) (i := ()) (Lr := []) (Mr := [2])
      ht rfl rfl rfl ((by decide : redWord (wordProd n₀ [0, 1, 0] • firstPairBottomOneInteriorRight)
        = [0, 1, 2]).trans ht.symm)
  · exact interleaved_markedColumn_injective_standard C Λ hR hQ t
      firstPairBottomOneInteriorLeft 0 1 0 (by decide) (i := ()) (Lr := []) (Mr := [2])
      ht rfl rfl rfl ((by decide : redWord (wordProd n₀ [0, 1, 0] • firstPairBottomOneInteriorLeft)
        = [0, 1, 2]).trans ht.symm)

end Standard

end Categorification.Stendhal.BraidedStendhalAlgebra
