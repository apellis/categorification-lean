/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLVacuumEvaluation
import Categorification.WeightedKLR.RedStrands.DoubleCLDownwardBlock
import Categorification.WeightedKLR.RedStrands.DoubleAllDownBoundary
import Categorification.WeightedKLR.RedStrands.DoubleViolatingQuotient

/-!
# The vacuum evaluation functor of the downward block

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The all-down boundary words of black
content `ν` act from the cyclotomic vacuum of the extended datum to its Stendhal block. This
file fixes the regions: with the cover right region at the vacuum weight, the cover left
region of every all-down word is the Stendhal block (`blockWeight_stendhalWeight`).
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep CyclotomicAction
  DoubleDiagram KL3.Diagram

universe u v w

section Regions

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  {X Y : Type v} [AddCommGroup X] [AddCommGroup Y] (W : WeightDatum C' X Y)
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) (o : X)

/-- **Regions of a reflected boundary.** The reflection of a double boundary with left weight
zero and right weight `right` is a KL word from the region `o - right` to the region `o`. -/
theorem cond_cover {right : X} {w : List (DoubleStrand I ℓ)}
    (hw : endWeight (blackDatum W hC) (redWeight W) 0 w = right) :
    Diagrams.BicatInterp.Cond (o - right) o ((coverColourMap W hC o).obj
      ((coverMirror W hC o).obj (obj (blackDatum W hC) (redWeight W) 0 w))) := by
  have hword : ((coverColourMap W hC o).obj ((coverMirror W hC o).obj
      (obj (blackDatum W hC) (redWeight W) 0 w))).word = wd W (o - 0) (coverWord w) := by
    change ((colours (blackDatum W hC) (redWeight W) 0 w).map (coverColour o)).reverse = _
    exact coverColours W hC o 0 w
  have hwt : wt W (o - 0) (coverWord w) = o - right := by
    rw [wt_coverWord W hC o, hw]
  refine ⟨?_, ?_, ?_⟩
  · rw [hword, ← hwt]; exact ok_wd W _ _
  · rw [hword, ← hwt, endR_wd, sub_zero]
  · exact congrArg (fun x : X => o - x) ((colours_endR _ _ _ _).trans hw)

end Regions

variable {I : Type u} {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)

/-- **The Stendhal block is the left region of the all-down words.** In coordinates, the
block weight of the Stendhal weight of `ν` is the vacuum block weight minus the common right
weight of the all-down words of black content `ν`. -/
theorem blockWeight_stendhalWeight (ν : Multiset I) :
    blockWeight Wgt L (stendhalWeight ℓ ν) =
      blockWeight Wgt L 0 - downRightWeight (coordinateDatum Λ C) (coordinateRedWeights Λ C) ν := by
  simp only [blockWeight, downRightWeight, stendhalWeight, Multiset.map_add, Multiset.map_map,
    Multiset.sum_add, Multiset.map_zero, Multiset.sum_zero, List.sum_ofFn, Function.comp_def,
    coordinateRedWeights, redWeight, Finset.sum_neg_distrib]
  change _ = _ - (_ - (ν.map fun j => WeightDatum.iX Wgt (Sum.inl j)).sum)
  rw [show (Multiset.map (fun x => WeightDatum.iX Wgt (Sum.inr x)) Finset.univ.val).sum =
      ∑ r, WeightDatum.iX Wgt (Sum.inr r) from rfl]
  abel

end Categorification.Stendhal
