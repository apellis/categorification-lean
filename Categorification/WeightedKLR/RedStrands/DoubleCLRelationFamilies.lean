/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLDownKLRUp
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackNegligible
import Categorification.WeightedKLR.RedStrands.DoubleCLRedUpEvaluation
import Categorification.WeightedKLR.RedStrands.DoubleCLRedCap
import Categorification.WeightedKLR.RedStrands.DoubleCLRedUpSlide
import Categorification.WeightedKLR.RedStrands.DoublePresentationUnion

/-!
# Families of relations whose reflected images are red-negligible

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The presentation of the downward
matrix algebra is built from a base presentation by adjoining families of relations
(`Presentation.addRels`). This file records the predicate that every relation of a presentation
has a cover red-negligible reflected image (`CoverRelsNegligible`), shows that it is preserved
by adjoining a family whose members have this property, and verifies it for the families of
downward KLR relations (at the Cautis–Lauda dual of the standard Khovanov–Lauda scalars), the
red/upward bigons, the mixed black relations and the black KL III relations.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w v₁

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q)

local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "RDc" => coordinateDatum Λ C

variable (o : I ⊕ Fin ℓ → ℤ)

/-- Every relation of `P` has a cover red-negligible reflected image. -/
def CoverRelsNegligible (P : Presentation.{v, v₁} (signature (RDc) (redWeight Wgt)) k) : Prop :=
  ∀ i, CoverRedNegligible.{u, v, w} Λ C hQ hc (coverCL Λ C hQ o (P.rel i))

variable {Λ C hQ hc o}

/-- Adjoining a family of relations with cover red-negligible images preserves
`CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addRels {P : Presentation.{v, v₁} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) {ι : Type v₁}
    {dom cod : ι → Obj (signature (RDc) (redWeight Wgt))} {rel : ∀ i, LinDiagram k (dom i) (cod i)}
    (h : ∀ i, CoverRedNegligible.{u, v, w} Λ C hQ hc (coverCL Λ C hQ o (rel i))) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (P.addRels ι dom cod rel)
  | .inl i => hP i
  | .inr i => h i

/-- The union of two presentations whose relations have cover red-negligible images has the
same property. -/
theorem CoverRelsNegligible.union
    {P P' : Presentation.{v, v₁} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P)
    (hP' : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P') :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (P.union P') :=
  hP.addRels hP'

/-- A presentation all of whose relations have cover red-negligible images sends its whole
tensor ideal to cover red-negligible maps. -/
theorem CoverRelsNegligible.mem_ideal
    {P : Presentation.{v, v₁} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) (hwf : P.WFDom)
    {a b : Obj (signature (RDc) (redWeight Wgt))} {f : LinDiagram k a b} (hf : f ∈ P.ideal a b) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc (coverCL Λ C hQ o f) :=
  coverRedNegligible_of_mem_ideal Λ C hQ hc o P hwf (fun i _ => hP i) hf

/-- **Downward KLR relations at the standard scalars.** Adjoining the downward translations
of the KLR relations of the affine cover of the Cautis–Lauda dual of the standard
Khovanov–Lauda scalars preserves `CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addDownRelations_kl
    (hstd : ∀ i j, i ≠ j → Q i j = CL.qCL (CL.CLScalars.kl : CL.CLScalars C k) i j)
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (addDownRelations (RDc) (redWeight Wgt)
      (affineCoverQ (DoubleDiagram.clDownwardQ (CL.CLScalars.kl : CL.CLScalars C k)) Λ) P) :=
  hP.addRels fun _ =>
    coverRedNegligible_downRelation_of_empty Λ C hQ hc o _
      (coverRedNegligible_downRelation_kl Λ C hQ hc o hstd) _ _ _ _ _ _ _

/-- Adjoining the red/upward bigons preserves `CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addRedUpRelations
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (addRedUpRelations (RDc) (redWeight Wgt) k P) :=
  hP.addRels fun a => by
    rw [coverCL_redUpRel Λ C hQ o a]
    apply CoverRedNegligible.zero

/-- Adjoining the red cup relations preserves `CoverRelsNegligible`: their reflected images
vanish by the zigzag identities of the Cautis–Lauda presentation. -/
theorem CoverRelsNegligible.addRedCupRelations
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (addRedCupRelations (RDc) (redWeight Wgt) P) :=
  hP.addRels fun a => by
    rw [show coverCL Λ C hQ o
        (LinDiagram.of (redCupLeft (RDc) (redWeight Wgt) a.leftWeight a.left a.black a.red
            a.right) -
          LinDiagram.of (redCupRight (RDc) (redWeight Wgt) a.leftWeight a.left a.black a.red
            a.right)) = 0 from
      coverLin_redCupRel Wgt (extendedCartanDatum_dot_inl Λ C) o _ (CL.zigzags _ k _) a]
    apply CoverRedNegligible.zero

/-- Adjoining the red cap relations preserves `CoverRelsNegligible`: their reflected images
vanish by the zigzag identities of the Cautis–Lauda presentation. -/
theorem CoverRelsNegligible.addRedCapRelations
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (addRedCapRelations (RDc) (redWeight Wgt) P) :=
  hP.addRels fun a => by
    rw [show coverCL Λ C hQ o
        (LinDiagram.of (redCapLeft (RDc) (redWeight Wgt) a.leftWeight a.left a.black a.red
            a.right) -
          LinDiagram.of (redCapRight (RDc) (redWeight Wgt) a.leftWeight a.left a.black a.red
            a.right)) = 0 from
      coverLin_redCapRel Wgt (extendedCartanDatum_dot_inl Λ C) o _ (CL.zigzags _ k _) a]
    apply CoverRedNegligible.zero

/-- Adjoining the red/upward slide relations (4.4c,d) and their mirrors preserves
`CoverRelsNegligible`: their reflected images vanish by the dot and crossing slides through the
sideways crossings of the Cautis–Lauda presentation. -/
theorem CoverRelsNegligible.addRedUpSlideRelations
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (addRedUpSlideRelations (RDc) (redWeight Wgt) P) :=
  hP.addRels fun ⟨μ, u, r, g, v, mirror⟩ => by
    cases mirror
    · rw [show coverCL Λ C hQ o
          (LinDiagram.of (redUpSlide (RDc) (redWeight Wgt) μ u r g v false) -
            LinDiagram.of (redUpSlide (RDc) (redWeight Wgt) μ u r g v true)) = 0 from
        coverLin_redUpSlideRel Wgt (extendedCartanDatum_dot_inl Λ C) o _
          (presCL_cover_klr Λ C hQ) μ u r g v]
      apply CoverRedNegligible.zero
    · rw [show coverCL Λ C hQ o
          (LinDiagram.of (redUpSlideMirror (RDc) (redWeight Wgt) μ u r g v false) -
            LinDiagram.of (redUpSlideMirror (RDc) (redWeight Wgt) μ u r g v true)) = 0 from
        coverLin_redUpSlideMirrorRel Wgt (extendedCartanDatum_dot_inl Λ C) o _
          (presCL_cover_klr Λ C hQ) μ u r g v]
      apply CoverRedNegligible.zero

section Black

variable (ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
    ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) o = 0)
  (ht : ∀ i j : I, (cyclotomicScalars (IsRouquierQ.klrSymm (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (IsRouquierQ.polyInY_leading (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (cyclotomicCoverWeightDatum Λ C) (IsRouquierQ.polyInY_degree_pair
      (isRouquierQ_cyclotomicCoverQ C Λ Q hQ) (cyclotomicCoverWeightDatum Λ C))).t
      (Sum.inl i) (Sum.inl j) = 1)
  (hs : ∀ (i j : I) (p q : ℕ), (cyclotomicScalars
    (IsRouquierQ.klrSymm (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (IsRouquierQ.polyInY_leading (isRouquierQ_cyclotomicCoverQ C Λ Q hQ))
    (cyclotomicCoverWeightDatum Λ C) (IsRouquierQ.polyInY_degree_pair
      (isRouquierQ_cyclotomicCoverQ C Λ Q hQ) (cyclotomicCoverWeightDatum Λ C))).s
      (Sum.inl i) (Sum.inl j) p q = 0)

include ho ht hs

/-- Adjoining the mixed black relations (2.4a), (2.3c) at the standard scalars preserves
`CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addMixedBlackRelations_kl
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (addMixedBlackRelations (RDc) (redWeight Wgt) k
      (CL.CLScalars.kl : CL.CLScalars C k).t P) :=
  hP.addRels fun a => coverRedNegligible_mixedBlackRelation Λ C hQ hc o ho ht hs a

/-- Adjoining the black KL III relations preserves `CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addBlackKLRelations
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o (addBlackKLRelations (RDc) (redWeight Wgt) P) :=
  hP.addRels fun r => coverRedNegligible_blackRel Λ C hQ hc o ho ht hs r

/-- Adjoining the black biadjunction and dot cyclicity relations preserves
`CoverRelsNegligible`. -/
theorem CoverRelsNegligible.addBlackAdjunctionRelations
    {P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k}
    (hP : CoverRelsNegligible.{u, v, w} Λ C hQ hc o P) :
    CoverRelsNegligible.{u, v, w} Λ C hQ hc o
      (addBlackAdjunctionRelations (RDc) (redWeight Wgt) P) :=
  hP.addRels fun r => coverRedNegligible_blackAdjunction Λ C hQ hc o ho ht hs P r

end Black

end Categorification.Stendhal
