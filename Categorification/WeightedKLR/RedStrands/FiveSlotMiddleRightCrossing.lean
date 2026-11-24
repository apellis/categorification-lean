/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AppendRedCrossingSuffix
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralKernelProjective
import Categorification.WeightedKLR.RedStrands.TwoRedCrossingInjectivity

/-!
# The higher crossing at the middle right five-slot loading

Webster, arXiv:1309.3796v2, Lemma 6.8 and (6.21).
Append the unchanged final red and black strands to the terminal crossing
in the first black weight. This gives the crossing from the central loading
into the actual higher kernel of the middle right loading.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA QuantumGroup KL3.Diagram
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "θ" => (Singleton.singleton () : Multiset Unit)
local notation "ν₀" => (θ + θ)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "N" => Multiset.card μ₀
local notation "s" => sadj N 2 • fixedTopFourExitCut 2
local notation "t" => fixedTopFourExitCut 1

private def middleRightPrefix : Seq (stendhalWeight 1 ((0 : Multiset Unit) + 0)) :=
  Seq.ofList [.inr 0] (by decide)

private theorem middleRightPrefix_ordered : IsRedOrdered middleRightPrefix :=
  (redWord_eq_finRange_iff _).1 (by decide)

private def middleRightTest : OrderedCrossingTest 3 θ :=
  (OrderedCrossingTest.rightmost () 0 middleRightPrefix middleRightPrefix_ordered).appendReds 1

private theorem middleRightTest_top : appendBlackLoading () θ middleRightTest.top = t := by decide +kernel
private theorem middleRightTest_bottom : appendBlackLoading () θ middleRightTest.bottom = s := by decide +kernel
private theorem middleRightTest_index : middleRightTest.index = 1 := by decide +kernel

private theorem middleRightOrdered : redWord s = List.finRange 3 := by decide
private theorem middleRightNext_order : redWord t = redWord s := by decide
private theorem middleRightNext_crossing : sadj N 1 • s = t := by decide +kernel

private theorem middleRightNext_strict : adjacentBlockRoot 1 2 s < adjacentBlockRoot 1 2 t := by
  apply lt_of_le_not_ge
  · intro r i
    fin_cases r <;> cases i <;> decide
  · intro h
    exact (by decide : ¬ adjacentBlockRoot 1 2 t 1 () ≤ adjacentBlockRoot 1 2 s 1 ()) (h 1 ())

variable {k : Type} [Field k] {D : CartanDatum Unit}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)

private theorem middleRightTest_appendBlack
    (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
    (hR : IsRouquierQ D Q) (test : middleRightTest.InjectiveAt Q Λ) :
    OrdinaryCutCrossingTest Q Λ s t 1 := by
  have h := eq_zero_of_mul_crossing_appendBlack (C := D) Q hR Λ () θ middleRightTest.index
    middleRightTest.index_valid middleRightTest.top middleRightTest.bottom middleRightTest.top_ordered test
  simpa only [OrdinaryCutCrossingTest, middleRightTest_top, middleRightTest_bottom,
    middleRightTest_index] using h

/-- Ordinary cancellation at the middle right top holds with arbitrary
red weights at standard parameters. -/
theorem fiveSlotMiddleRight_ordinaryCrossingTest_standard
    (hR : IsRouquierQ D QL) (hQ : KLRSymm QL) (Λ : Fin 3 → Unit →₀ ℕ) :
    OrdinaryCutCrossingTest QL Λ s t 1 := by
  have test : middleRightTest.InjectiveAt QL Λ :=
    OrderedCrossingTest.rightmost_appendReds_standard (ℓ := 1) hR hQ () 0
      middleRightPrefix middleRightPrefix_ordered 1 Λ
  exact middleRightTest_appendBlack QL Λ hR test

/-- The central loading projective embeds into the actual higher kernel at
`[0,1,i,2,i]` by the red-black crossing. -/
theorem fiveSlotMiddleRight_higherCrossingMap_injective_standard
    (hR : IsRouquierQ D QL) (hQ : KLRSymm QL) (Λ : Fin 3 → Unit →₀ ℕ) :
    Function.Injective (crossingIntoKernelMap QL Λ 1 2 middleRightNext_order middleRightNext_strict 1) :=
  crossingIntoKernelMap_injective_of_ordinary_test QL Λ middleRightOrdered middleRightNext_order
    1 middleRightNext_crossing 1 2 middleRightNext_strict hQ
    (fiveSlotMiddleRight_ordinaryCrossingTest_standard hR hQ Λ)

end Categorification.Stendhal.BraidedStendhalAlgebra
