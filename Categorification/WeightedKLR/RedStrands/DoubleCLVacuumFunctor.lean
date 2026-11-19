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
  DoubleDiagram KL3.Diagram Diagrams.BicatInterp InductionAlong

universe u v w

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

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

section Evaluation

variable [DecidableEq I] {k : Type v} [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  (hQ : IsRouquierQ C Q) (hc : CoverDotCentral Λ C Q) (ν : Multiset I)

local notation "S" => cyclotomicCoverQ C Λ Q
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "p" => cyclotomicCoverPolynomial (I := I) (ℓ := ℓ) (k := k)
local notation "monic" => cyclotomicCoverPolynomial_monic (k := k)
local notation "topDeg" => cyclotomicCoverPolynomial_natDegree (k := k) Λ C
local notation "wt₀" => (blockWeight Wgt L 0 : I ⊕ Fin ℓ → ℤ)
local notation "π" => cyclotomicCoverToTensor (Q := Q) Λ ν C
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead monic Wgt L topDeg deg
local notation "PCL" => KL3.Diagram.CL.presCL Wgt k Sc
set_option quotPrecheck false in
set_option hygiene false in
local notation "V" => regularObj.{u,v,w} (Q := S) (a := p) (RD := Wgt) (Λ := L)

/-- The cyclotomic vacuum of the extended datum, as an object of its weight space. -/
abbrev coverVacuum := familyObj sym lead monic topDeg deg V

/-- **Projected vacuum evaluation.** A morphism of the Cautis–Lauda presentation of the
extended datum acts on the cyclotomic vacuum; its component at the Stendhal block of `ν` is
projected to the tensor-product algebra by extension of scalars. -/
def vacuumEval {s : I ⊕ Fin ℓ → ℤ} (hν : blockWeight Wgt L (stendhalWeight ℓ ν) = s)
    {c d : Obj (psig Wgt)} (ha : Cond s wt₀ c) (hb : Cond s wt₀ d)
    (φ : (PCL).obj c ⟶ (PCL).obj d) :=
  (functor (RingHom.toNonUnitalRingHom (AlgHom.toRingHom π))).map
    (((admissibleQuotientMap (RouqFamily.genImg Fam Sc) PCL (presCL_cover_rel Λ C hQ)
      Signature.IsEven.odd_eq_false ha hb φ).hom.app
        (coverVacuum.{u, v, w} Λ C hQ)) ⟨stendhalWeight ℓ ν, hν⟩)

end Evaluation

end Categorification.Stendhal
