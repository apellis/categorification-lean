/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoublePitchforkCoefficients
import Categorification.WeightedKLR.RedStrands.DoubleNormalizationCounterexample
import Categorification.WeightedKLR.RedStrands.DoubleAllDownBoundary
import Categorification.WeightedKLR.RedStrands.DoubleBubbleRelations
import Categorification.WeightedKLR.RedStrands.FirstWeightBoundary
import Categorification.Diagrams.KL3.SlideCalculus

/-!
# The printed pitchfork obstruction

Webster, arXiv:1309.3796v3, Definition 2.4, (2.2a), (2.3a), (2.5a–b),
and (2.6e), and Definition 4.24. Compose the vertical reflection of the first
cup pitchfork with the second, cap pitchfork. The raw diagrams below use CL
word order, opposite to the physical order in the source. Each pitchfork
multiplies a downward crossing by `tⱼᵢ`. The other path uses a sideways
crossing with no coefficient. In disconnected type A₁ × A₁, for `tᵢⱼ = 2`,
both the ordinary downward bigon and sideways bigon have coefficient `2`.
At coroot coordinate `1`, the two bare bubbles in the composite are degree
zero, so the relation forces `8 • 𝟙 = 2 • 𝟙` on the one-black boundary.

Only the displayed downward KLR bigon and the opposite-orientation bigon
are used. The inverse-series bubble relation never enters the calculation.
-/

noncomputable section

namespace Categorification.Stendhal.DoubleDiagram

open CategoryTheory StringDiagrams QuantumGroup QuantumGroup.UDot KL3.Diagram
open DisconnectedCounterexample (weightDatum)
open scoped Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

set_option backward.isDefEq.respectTransparency false

private abbrev redWeight : Fin 1 → Bool → ℤ := Subtype.val ∘ DisconnectedCounterexample.redWeights
private abbrev redPrefix : List (DoubleStrand Bool 1) := [.inr 0]
private abbrev pSig := signature weightDatum redWeight
private abbrev region : Bool → ℤ := endWeight weightDatum redWeight 0 redPrefix

private abbrev aWord : List (Letter Bool) := [dn true]
private abbrev bWord : List (Letter Bool) := [up false, dn false, dn true]
private abbrev cWord : List (Letter Bool) := [dn true, up false, dn false]
private abbrev dWord : List (Letter Bool) := [up false, dn true, dn false]

local notation "A" => ob weightDatum region aWord
local notation "B" => ob weightDatum region bWord
local notation "C" => ob weightDatum region cWord
local notation "D" => ob weightDatum region dWord

private def cupB : A ⟶ B :=
  mkD weightDatum region [([], .cup (up false), [dn true])] (by schain)

private def capB : B ⟶ A :=
  mkD weightDatum region [([], .cap (dn false), [dn true])] (by schain)

private def cupC : A ⟶ C :=
  mkD weightDatum region [([dn true], .cup (up false), [])] (by schain)

private def capC : C ⟶ A :=
  mkD weightDatum region [([dn true], .cap (dn false), [])] (by schain)

private def downForward : B ⟶ D :=
  mkD weightDatum region [([up false], .cross false false true, [])] (by schain)

private def downBackward : D ⟶ B :=
  mkD weightDatum region [([up false], .cross false true false, [])] (by schain)

private def mixedForward : C ⟶ D :=
  mkD weightDatum region ((crossrL false true).map (whL [] [dn false])) (by
    simp only [crossrL, List.map_cons, List.map_nil, whL]; schain)

private def mixedBackward : D ⟶ C :=
  mkD weightDatum region ((crosslL false true).map (whL [] [dn false])) (by
    simp only [crosslL, List.map_cons, List.map_nil, whL]; schain)

/-- The two bubbles have coroot coordinate 1. The disconnected through
strand does not change the coordinate of the bubble colour. -/
theorem printedPitchfork_bubble_coordinates :
    ip weightDatum false region = 1 ∧ ip weightDatum false (wt weightDatum region [dn true]) = 1 := by
  constructor
  · exact DisconnectedCounterexample.pair_highest false
  · exact DisconnectedCounterexample.pair_other_root

/-- The bare clockwise bubbles in CL word order reflect to the degree-zero
counterclockwise bubbles of Webster v3, (2.3a). -/
theorem printedPitchfork_degree_zero :
    BubbleOrientation.counterclockwise.degreeZeroDots (ip weightDatum false region) = 0 ∧
      BubbleOrientation.counterclockwise.degreeZeroDots
        (ip weightDatum false (wt weightDatum region [dn true])) = 0 := by
  rw [printedPitchfork_bubble_coordinates.1, printedPitchfork_bubble_coordinates.2]
  decide

/-- Composing the cup and cap pitchforks at disconnected leading coefficient 2
forces the through-strand identity to vanish. Both paths have unit bubble closure. -/
theorem id_eq_zero_of_two_pitchforks {Cat : Type*} [Category* Cat] [Preadditive Cat] [Linear ℚ Cat]
    {x a b z : Cat} (ac : x ⟶ a) (dc : a ⟶ z) (dc' : z ⟶ a) (ac' : a ⟶ x)
    (bc : x ⟶ b) (mc : b ⟶ z) (mc' : z ⟶ b) (bc' : b ⟶ x)
    (hCup : (2 : ℚ) • (ac ≫ dc) = bc ≫ mc)
    (hCap : (2 : ℚ) • (dc' ≫ ac') = mc' ≫ bc')
    (hAA : ac ≫ ac' = 𝟙 x) (hBB : bc ≫ bc' = 𝟙 x)
    (hDD : dc ≫ dc' = (2 : ℚ) • 𝟙 a) (hMM : mc ≫ mc' = (2 : ℚ) • 𝟙 b) :
    𝟙 x = 0 := by
  by_contra hid
  have h := pitchforkCoefficients_mul_eq_one ac dc dc' ac' bc mc mc' bc' hid
    (by norm_num : (2 : ℚ) ≠ 0) hCup hCap hAA hBB hDD hMM
  norm_num at h

section Fragment

private abbrev objAt (w : List (Letter Bool)) :=
  obj weightDatum redWeight 0 (redPrefix ++ blackWord w ++ [])

private abbrev blackAt {s t : List (Letter Bool)}
    (f : ob weightDatum region s ⟶ ob weightDatum region t) :
    LinDiagram ℚ (objAt s) (objAt t) :=
  LinDiagram.of (blackDiagram weightDatum redWeight 0 redPrefix [] f)

/-- The individual local relations in the one-red disconnected example. -/
inductive PrintedPitchforkRelation
  | cup | cap | downBigon | mixedBigon | leftBubble | rightBubble

private def PrintedPitchforkRelation.dom : PrintedPitchforkRelation → Obj pSig
  | .cup | .leftBubble | .rightBubble => objAt aWord
  | .cap => objAt dWord
  | .downBigon => objAt bWord
  | .mixedBigon => objAt cWord

private def PrintedPitchforkRelation.cod : PrintedPitchforkRelation → Obj pSig
  | .cup => objAt dWord
  | .cap | .leftBubble | .rightBubble => objAt aWord
  | .downBigon => objAt bWord
  | .mixedBigon => objAt cWord

/-- Reflected first (2.2a), original second (2.2a), the two indicated bigons and
the two degree-zero bubble relations, in their actual surrounding words. -/
private def printedPitchforkRelation :
    (a : PrintedPitchforkRelation) → LinDiagram ℚ a.dom a.cod
  | .cup => (2 : ℚ) • blackAt (cupB ≫ downForward) - blackAt (cupC ≫ mixedForward)
  | .cap => (2 : ℚ) • blackAt (downBackward ≫ capB) - blackAt (mixedBackward ≫ capC)
  | .downBigon => blackAt (downForward ≫ downBackward) - (2 : ℚ) • blackAt (𝟙 B)
  | .mixedBigon => blackAt (mixedForward ≫ mixedBackward) - (2 : ℚ) • blackAt (𝟙 C)
  | .leftBubble => blackAt (cupC ≫ capC) - blackAt (𝟙 A)
  | .rightBubble => blackAt (cupB ≫ capB) - blackAt (𝟙 A)

/-- Adjoin only the stated pitchfork, bigon and degree-zero relations to any
signed presentation. This fragment annihilates the one-black boundary
independently of any other relations. -/
def addPrintedPitchforkFragment (P : Presentation pSig ℚ) : Presentation pSig ℚ :=
  P.addRels _ PrintedPitchforkRelation.dom PrintedPitchforkRelation.cod printedPitchforkRelation

variable (P : Presentation pSig ℚ)

local notation "P₁" => addPrintedPitchforkFragment P

private abbrev image {s t : List (Letter Bool)}
    (f : ob weightDatum region s ⟶ ob weightDatum region t) :=
  (P₁).diag (blackDiagram weightDatum redWeight 0 redPrefix [] f)

private theorem lin_blackAt {s t : List (Letter Bool)}
    (f : ob weightDatum region s ⟶ ob weightDatum region t) :
    (P₁).lin (blackAt f) = image P f := rfl

private theorem image_comp {s t z : List (Letter Bool)}
    (f : ob weightDatum region s ⟶ ob weightDatum region t)
    (g : ob weightDatum region t ⟶ ob weightDatum region z) :
    image P (f ≫ g) = image P f ≫ image P g := by
  simp only [image, blackDiagram_comp, Presentation.diag_comp]

private theorem image_id (s : List (Letter Bool)) :
    image P (𝟙 (ob weightDatum region s)) = 𝟙 _ := by
  simp only [image, blackDiagram_id, Presentation.diag_id]

private theorem cupEquation :
    (2 : ℚ) • (image P cupB ≫ image P downForward) = image P cupC ≫ image P mixedForward := by
  have h := (P₁).lin_rel_self (.inr .cup)
  change (P₁).lin ((2 : ℚ) • blackAt (cupB ≫ downForward) -
    blackAt (cupC ≫ mixedForward)) = 0 at h
  simpa only [Presentation.lin_sub, Presentation.lin_smul, lin_blackAt,
    sub_eq_zero, image_comp] using h

private theorem capEquation :
    (2 : ℚ) • (image P downBackward ≫ image P capB) = image P mixedBackward ≫ image P capC := by
  have h := (P₁).lin_rel_self (.inr .cap)
  change (P₁).lin ((2 : ℚ) • blackAt (downBackward ≫ capB) -
    blackAt (mixedBackward ≫ capC)) = 0 at h
  simpa only [Presentation.lin_sub, Presentation.lin_smul, lin_blackAt,
    sub_eq_zero, image_comp] using h

private theorem downBigon :
    image P downForward ≫ image P downBackward = (2 : ℚ) • 𝟙 _ := by
  have h := (P₁).lin_rel_self (.inr .downBigon)
  change (P₁).lin (blackAt (downForward ≫ downBackward) - (2 : ℚ) • blackAt (𝟙 B)) = 0 at h
  simpa only [Presentation.lin_sub, Presentation.lin_smul, lin_blackAt,
    sub_eq_zero, image_comp, image_id] using h

private theorem mixedBigon :
    image P mixedForward ≫ image P mixedBackward = (2 : ℚ) • 𝟙 _ := by
  have h := (P₁).lin_rel_self (.inr .mixedBigon)
  change (P₁).lin (blackAt (mixedForward ≫ mixedBackward) - (2 : ℚ) • blackAt (𝟙 C)) = 0 at h
  simpa only [Presentation.lin_sub, Presentation.lin_smul, lin_blackAt,
    sub_eq_zero, image_comp, image_id] using h

private theorem bubbleB : image P cupB ≫ image P capB = 𝟙 _ := by
  have h := (P₁).lin_rel_self (.inr .rightBubble)
  change (P₁).lin (blackAt (cupB ≫ capB) - blackAt (𝟙 A)) = 0 at h
  simpa only [Presentation.lin_sub, lin_blackAt, sub_eq_zero, image_comp, image_id] using h

private theorem bubbleC : image P cupC ≫ image P capC = 𝟙 _ := by
  have h := (P₁).lin_rel_self (.inr .leftBubble)
  change (P₁).lin (blackAt (cupC ≫ capC) - blackAt (𝟙 A)) = 0 at h
  simpa only [Presentation.lin_sub, lin_blackAt, sub_eq_zero, image_comp, image_id] using h

/-- The surviving ordinary one-black boundary has zero identity in any
presentation extending the printed fragment. -/
theorem printedPitchfork_id_eq_zero : 𝟙 ((P₁).obj (objAt aWord)) = 0 := by
  exact id_eq_zero_of_two_pitchforks (image P cupB) (image P downForward)
    (image P downBackward) (image P capB) (image P cupC) (image P mixedForward)
    (image P mixedBackward) (image P capC) (cupEquation P) (capEquation P)
    (bubbleB P) (bubbleC P) (downBigon P) (mixedBigon P)

end Fragment

section OrdinaryCorner

open DisconnectedCounterexample (content exponents parameters redWeights affine_idem_ne_zero)

variable (P : Presentation pSig ℚ)
local notation "P₁" => addPrintedPitchforkFragment P
local notation "Ord" => {s : KLR.Seq (stendhalWeight 1 content) // IsRedOrdered s}

private theorem surviving_word (s : Ord) (h : ¬ IsViolated s.val) :
    (downTriple weightDatum redWeights s).val.word = redPrefix ++ blackWord aWord ++ [] := by
  obtain ⟨r, hr⟩ := (FirstWeight.boundaryEquiv true 1).surjective ⟨s.val, s.property, h⟩
  have hs : s = ⟨(FirstWeight.boundaryEquiv true 1 r).val,
      (FirstWeight.boundaryEquiv true 1 r).property.1⟩ :=
    Subtype.ext (congrArg Subtype.val hr).symm
  rw [hs, Fin.fin_one_eq_zero r]
  rfl

/-- In the one-black fibre, the ordinary left violation kills one loading
and the printed pitchfork fragment kills the other. -/
theorem printedPitchfork_downwardMatrix_subsingleton :
    Subsingleton (downwardMatrix (Λ := redWeights) P₁ content) := by
  constructor
  intro f g
  apply KLR.Diagram.MatEnd.ext
  intro s t
  have hz : 𝟙 (downObj (RD := weightDatum) (Λ := redWeights) P₁ s) = 0 := by
    by_cases hv : IsViolated s.val
    · exact downObj_id_eq_zero (RD := weightDatum) (Λ := redWeights) P₁ s hv
    · let a : BoundaryCategory (RD := weightDatum) (Λ := redWeights) P₁
        (downRightWeight weightDatum redWeights content) :=
        downTriple weightDatum redWeights s
      have he : 𝟙 (tripleObj (RD := weightDatum) (Λ := redWeights) P₁ a) = 0 := by
        change 𝟙 ((P₁).obj (obj weightDatum redWeight 0 a.val.word)) = 0
        rw [surviving_word s hv]
        exact printedPitchfork_id_eq_zero P
      have hpre : 𝟙 a = 0 := InducedCategory.hom_ext he
      let π := violatingFunctor (RD := weightDatum) (Λ := redWeights) P₁
        (downRightWeight weightDatum redWeights content)
      exact (π.map_id a).symm.trans ((congrArg π.map hpre).trans (π.map_zero _ _))
  have hzero (m : downObj (RD := weightDatum) (Λ := redWeights) P₁ s ⟶
      downObj (RD := weightDatum) (Λ := redWeights) P₁ t) : m = 0 := by
    rw [← Category.id_comp m, hz, Limits.zero_comp]
  exact (hzero _).trans (hzero _).symm

/-- Webster v3, Lemma 4.29, cannot hold with the literal pitchfork and bigon
coefficients at these disconnected parameters. The obstruction uses no
instance of the inverse-bubble relation. -/
theorem printedPitchfork_no_injection :
    ¬ ∃ f : TensorProductAlgebra ℚ parameters exponents content →ₐ[ℚ]
      downwardMatrix (Λ := redWeights) P₁ content, Function.Injective f := by
  have hs := printedPitchfork_downwardMatrix_subsingleton P
  rintro ⟨f, hf⟩
  exact affine_idem_ne_zero (hf (hs.elim _ _))

end OrdinaryCorner

end Categorification.Stendhal.DoubleDiagram
