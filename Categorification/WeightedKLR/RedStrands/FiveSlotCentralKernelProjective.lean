/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AppendRedCrossingSuffix
import Categorification.WeightedKLR.RedStrands.FiveSlotCentralHigher

/-!
# Projectivity of the central five-slot higher kernel

Webster, arXiv:1309.3796v2, proof of Lemma 6.8 at (6.21).
The two crossings from the left extreme to the central loading have, respectively,
one and zero uncrossed red strands on their right. The ordinary terminal tests
therefore provide cancellation in the unchanged source corner.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR KLRAlgebra TypeA
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "θ" => (Singleton.singleton () : Multiset Unit)
local notation "ν₀" => (θ + θ)
local notation "μ₀" => stendhalWeight 3 ν₀
local notation "v₀" => fixedTopFourExitCut 0
local notation "v₁" => fixedTopFourExitCut 1
local notation "jA" => sadj (Multiset.card μ₀) 2 • v₀

private def centralLongPrefix : Seq (stendhalWeight 2 (θ + 0)) :=
  Seq.ofList [.inr 0, .inl (), .inr 1] (by decide)

private def centralShortPrefix : Seq (stendhalWeight 1 (θ + 0)) :=
  Seq.ofList [.inr 0, .inl ()] (by decide)

private theorem centralLongPrefix_ordered : IsRedOrdered centralLongPrefix :=
  (redWord_eq_finRange_iff _).1 (by decide)

private theorem centralShortPrefix_ordered : IsRedOrdered centralShortPrefix :=
  (redWord_eq_finRange_iff _).1 (by decide)

private def centralFirstTest : OrderedCrossingTest 3 ν₀ :=
  OrderedCrossingTest.rightmost () θ centralLongPrefix centralLongPrefix_ordered

private def centralSecondTest : OrderedCrossingTest 3 ν₀ :=
  (OrderedCrossingTest.rightmost () θ centralShortPrefix centralShortPrefix_ordered).appendReds 1

private theorem centralFirstTest_top : centralFirstTest.top = jA := by decide +kernel
private theorem centralFirstTest_bottom : centralFirstTest.bottom = v₁ := by decide +kernel
private theorem centralFirstTest_index : centralFirstTest.index = 3 := by decide +kernel
private theorem centralSecondTest_top : centralSecondTest.top = v₀ := by decide +kernel
private theorem centralSecondTest_bottom : centralSecondTest.bottom = jA := by decide +kernel
private theorem centralSecondTest_index : centralSecondTest.index = 2 := by decide +kernel

variable {k : Type} [Field k]

private theorem centralFirstTest_transfer
    (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
    (test : centralFirstTest.InjectiveAt Q Λ) : OrdinaryCutCrossingTest Q Λ v₁ jA 3 := by
  unfold OrderedCrossingTest.InjectiveAt at test
  simpa only [OrdinaryCutCrossingTest, centralFirstTest_top, centralFirstTest_bottom, centralFirstTest_index] using test

private theorem centralSecondTest_transfer
    (Q : Unit → Unit → MvPolynomial (Fin 2) k) (Λ : Fin 3 → Unit →₀ ℕ)
    (test : centralSecondTest.InjectiveAt Q Λ) : OrdinaryCutCrossingTest Q Λ jA v₀ 2 := by
  unfold OrderedCrossingTest.InjectiveAt at test
  simpa only [OrdinaryCutCrossingTest, centralSecondTest_top, centralSecondTest_bottom, centralSecondTest_index] using test

open QuantumGroup KL3.Diagram
variable {D : CartanDatum Unit}
local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars D k)

/-- At standard Khovanov–Lauda parameters the actual central five-slot higher
kernel is projective for every choice of the three red weights. -/
theorem fiveSlotCentral_kernel_projective_standard
    (hR : IsRouquierQ D QL) (hQ : KLRSymm QL) (Λ : Fin 3 → Unit →₀ ℕ) :
    Module.Projective
      (isIdempotentElem_violMk_redProj k QL Λ ν₀ (redWord v₁)).Cornerᵐᵒᵖ
      (blockLoadingKernel QL Λ v₁ 1 2) := by
  have test₁ : centralFirstTest.InjectiveAt QL Λ :=
    OrderedCrossingTest.rightmost_appendReds_standard (ℓ := 2) hR hQ () θ
      centralLongPrefix centralLongPrefix_ordered 0 Λ
  have test₂ : centralSecondTest.InjectiveAt QL Λ :=
    OrderedCrossingTest.rightmost_appendReds_standard (ℓ := 1) hR hQ () θ
      centralShortPrefix centralShortPrefix_ordered 1 Λ
  exact fiveSlotCentral_kernel_projective_of_tests QL Λ hQ
    (centralFirstTest_transfer QL Λ test₁) (centralSecondTest_transfer QL Λ test₂)

end Categorification.Stendhal.BraidedStendhalAlgebra
