/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLKernelTransfer
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackContext

/-!
# Black and mixed black relations are cover red-negligible

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29. The reflected black KL III relations
(`coverRedNegligible_blackRel`), their placements between signed words
(`coverRedNegligible_blackLinear`), and the mixed black relations (2.4a) and (2.3c)
(`coverRedNegligible_mixedBlackRelation`) are cover red-negligible.

The double diagrams carry the black relations of Khovanov–Lauda III, so the black Cautis–Lauda
scalars of `Q` are assumed to be those of Khovanov–Lauda (`t = 1`, `s = 0` on black vertices).
This is the parameter scope of the comparison map of Lemma 4.29 (see `clToDownwardMatrix`); it
is not an extra hypothesis of the route.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w

variable {I : Type u} {k : Type v} [Field k] {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (C : CartanDatum I)
  [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k} (hQ : IsRouquierQ C Q)
  (hc : CoverDotCentral Λ C Q)

local notation "D" => I ⊕ Fin ℓ
local notation "Wgt" => cyclotomicCoverWeightDatum Λ C
local notation "hS" => isRouquierQ_cyclotomicCoverQ C Λ Q hQ
local notation "sym" => IsRouquierQ.klrSymm hS
local notation "lead" => IsRouquierQ.polyInY_leading hS
local notation "deg" => IsRouquierQ.polyInY_degree_pair hS Wgt
local notation "Sc" => cyclotomicScalars sym lead Wgt deg
local notation "hC" => extendedCartanDatum_dot_inl Λ C
local notation "L" => cyclotomicCoverHighest (I := I) (ℓ := ℓ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "Fam" => cyclotomicFamily.{u, v, w} sym lead
  (cyclotomicCoverPolynomial_monic (k := k)) Wgt L (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg
local notation "RDc" => coordinateDatum Λ C

include hQ in
/-- Brundan's upward relations for the cyclotomic family of the extended datum. -/
theorem cover_brundanUpKLR : BrundanUpKLR (Fam) (Sc) :=
  cyclotomicFamily_brundanUpKLR sym lead (cyclotomicCoverPolynomial_monic (k := k)) Wgt L
    (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg fun i j h =>
      coeff_eq_zero_of_lt_of_hom _ (IsRouquierQ.homogeneous hS i j h)

include hQ in
/-- Brundan's mixed inversion for the cyclotomic family of the extended datum. -/
theorem cover_mixedInversion : BrundanMixedInversion (Fam) :=
  cyclotomicFamily_mixedInversion Wgt L sym lead (cyclotomicCoverPolynomial_monic (k := k))
    (cyclotomicCoverPolynomial_natDegree (k := k) Λ C) deg

variable (o : I ⊕ Fin ℓ → ℤ)
  (ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
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

/-- **The reflected black KL III relations are cover red-negligible.** -/
theorem coverRedNegligible_blackRel (r : (pres (RDc) k).Rel) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (blackMirrorLinear (RDc) (redWeight Wgt) ((pres (RDc) k).rel r))) :=
  coverRedNegligible_of_coverLin_admissibleKernel Λ C hQ hc o _
    (coverLin_blackRel Wgt hC o ho (Fam) (Sc) ht hs (cover_brundanUpKLR Λ C hQ)
      (cover_mixedInversion Λ C hQ) r)

/-- **Black KL III relations between signed words are cover red-negligible.** -/
theorem coverRedNegligible_blackLinear (μ : I ⊕ Fin ℓ → ℤ) (u' v' : List (DoubleStrand I ℓ))
    {τ : I ⊕ Fin ℓ → ℤ} (s t : List (Letter I))
    (hst : endWeight (RDc) (redWeight Wgt) μ (u' ++ blackWord s) = τ)
    (htt : endWeight (RDc) (redWeight Wgt) μ (u' ++ blackWord t) = τ)
    (f : LinDiagram k (ob (RDc) (endWeight (RDc) (redWeight Wgt) μ u') s)
      (ob (RDc) (endWeight (RDc) (redWeight Wgt) μ u') t))
    (hf : (pres (RDc) k).lin f = 0) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (blackLinear (RDc) (redWeight Wgt) k μ u' v' f)) :=
  coverRedNegligible_of_coverLin_admissibleKernel Λ C hQ hc o _
    (coverLin_blackLinear_eq_zero Wgt hC o ho (Fam) (Sc) ht hs (cover_brundanUpKLR Λ C hQ)
      (cover_mixedInversion Λ C hQ) μ u' v' s t hst htt f hf)

/-- **The mixed black relations (2.4a) and (2.3c) are cover red-negligible.** -/
theorem coverRedNegligible_mixedBlackRelation (a : MixedBlackRelation (I ⊕ Fin ℓ → ℤ) I ℓ) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (mixedBlackRelation (RDc) (redWeight Wgt) k
        (CL.CLScalars.kl : CL.CLScalars C k).t a)) :=
  coverRedNegligible_of_coverLin_admissibleKernel Λ C hQ hc o _
    (coverLin_mixedBlackRelation_eq_zero Wgt hC o ho (Fam) (Sc) ht hs
      (cover_brundanUpKLR Λ C hQ) (cover_mixedInversion Λ C hQ) a)

end Categorification.Stendhal
