/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackNegligible
import Categorification.WeightedKLR.RedStrands.DoubleCLBlackContextQ

/-!
# Black relations with general parameters are cover red-negligible

Webster, arXiv:1309.3796v3, §4.6, proof of Lemma 4.29, for every Kang–Kashiwara family `Q`.
The black strands of the double diagrams carry the relations of Cautis–Lauda's `U_Q(g)`
(arXiv:1111.1431v3, Definition 1.1, `r = 1`) for the reflected scalars `Sb = (Sc|_I)^θ`, where
`Sc` are the Cautis–Lauda scalars of the cover parameters and `Sc|_I` their restriction to the
black colours (`coverBlackScalars`). This is the convention of the 2-category `𝒯` for general
`Q` (`tensorTwoCatPresentationQ`, `regionTensorPseudofunctorQ`): reflecting the black strands
turns `U_{Sb}` into `U_{Sb^θ} = U_{Sc|_I}`, which acts through the cyclotomic family.

The reflected black relations (`coverRedNegligible_blackRelQ`), their placements between signed
words (`coverRedNegligible_blackLinearQ`), the mixed black relations (2.4a) and (2.3c) at the
scalars `Sb.t` (`coverRedNegligible_mixedBlackRelationQ`) and the black biadjunction relations
(`coverRedNegligible_blackAdjunctionQ`) are cover red-negligible, with no hypothesis on `Q`.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory Bicategory QuantumGroup QuantumGroup.UDot StringDiagrams KLR TwoRep
  CyclotomicAction Diagrams.BicatInterp DoubleDiagram KL3.Diagram

universe u v w

section Scalars

variable {I : Type u} {ℓ : ℕ} {C : CartanDatum I} {C' : CartanDatum (I ⊕ Fin ℓ)}
  (hC : ∀ i j, C'.dot (.inl i) (.inl j) = C.dot i j) {k : Type*} [CommRing k]

/-- The Cautis–Lauda scalars of `C'` on the black colours `I ⊂ I ⊕ Fin ℓ`. -/
def coverBlackScalars (Sc : CL.CLScalars C' k) : CL.CLScalars C k where
  t i j := Sc.t (.inl i) (.inl j)
  s i j := Sc.s (.inl i) (.inl j)
  r i := Sc.r (.inl i)
  t_self _ := Sc.t_self _
  t_symm i j h := Sc.t_symm _ _ (by rw [hC]; exact h)
  s_symm _ _ := Sc.s_symm _ _

include hC in
theorem dij_inl (i j : I) : C'.dij (.inl i) (.inl j) = C.dij i j := by
  simp only [CartanDatum.dij, hC]

end Scalars

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

/-- **The black scalars of the double diagrams for a Kang–Kashiwara family `Q`**: the reflection
`(Sc|_I)^θ` of the Cautis–Lauda scalars of the cover parameters on the black colours. -/
abbrev blackScalarsQ : CL.CLScalars C k :=
  CLQ.thetaScalars (RDc) (coverBlackScalars hC (Sc))

/-- The black scalars have `r = 1`. -/
theorem blackScalarsQ_r (i : I) : (blackScalarsQ Λ C hQ).r i = 1 :=
  CLQ.thetaScalars_r _ i

/-- The reflection of the black scalars is the restriction of the cover scalars. -/
theorem thetaScalars_blackScalarsQ (o : D → ℤ)
    (ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
      ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) o = 0) :
    CLQ.thetaScalars (blackDatum Wgt hC) (blackScalarsQ Λ C hQ) =
      (coverRestrict Wgt hC o ho).scalars hC (Sc) :=
  CLQ.thetaScalars_thetaScalars _ fun _ => rfl

/-- Outside the extremal degrees, the cover scalars vanish on the black colours off the line of
degree `-2 (i · j)`. -/
theorem cover_s_eq_zero (i j : I) (p q : ℕ) (hp : p < C.dij i j) (hq : q < C.dij j i)
    (h : C.dot i i * p + C.dot j j * q ≠ -2 * C.dot i j) :
    (Sc).s (.inl i) (.inl j) p q = 0 :=
  kkScalars_s_eq_zero _ sym _ (IsRouquierQ.homogeneous hS) (.inl i) (.inl j) p q
    (by rwa [dij_inl hC]) (by rwa [dij_inl hC]) (by simpa only [hC] using h)

variable (o : I ⊕ Fin ℓ → ℤ)
  (ho : ∀ i : I, (cyclotomicCoverWeightDatum Λ C).pair
    ((cyclotomicCoverWeightDatum Λ C).iY (Sum.inl i)) o = 0)

include ho

/-- **The reflected black relations with general parameters are cover red-negligible.** -/
theorem coverRedNegligible_blackRelQ (r : (CLQ.pres (RDc) k (blackScalarsQ Λ C hQ)).Rel) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (blackMirrorLinear (RDc) (redWeight Wgt)
        ((CLQ.pres (RDc) k (blackScalarsQ Λ C hQ)).rel r))) :=
  coverRedNegligible_of_coverLin_admissibleKernel Λ C hQ hc o _
    (coverLin_blackRelQ Wgt hC o ho (Fam) (Sc) _ (thetaScalars_blackScalarsQ Λ C hQ o ho)
      (cover_s_eq_zero Λ C hQ) (cover_brundanUpKLR Λ C hQ) (cover_mixedInversion Λ C hQ) r)

/-- **Black relations with general parameters between signed words are cover red-negligible.** -/
theorem coverRedNegligible_blackLinearQ (μ : I ⊕ Fin ℓ → ℤ) (u' v' : List (DoubleStrand I ℓ))
    {τ : I ⊕ Fin ℓ → ℤ} (s t : List (Letter I))
    (hst : endWeight (RDc) (redWeight Wgt) μ (u' ++ blackWord s) = τ)
    (htt : endWeight (RDc) (redWeight Wgt) μ (u' ++ blackWord t) = τ)
    (f : LinDiagram k (ob (RDc) (endWeight (RDc) (redWeight Wgt) μ u') s)
      (ob (RDc) (endWeight (RDc) (redWeight Wgt) μ u') t))
    (hf : (CLQ.pres (RDc) k (blackScalarsQ Λ C hQ)).lin f = 0) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (blackLinear (RDc) (redWeight Wgt) k μ u' v' f)) :=
  coverRedNegligible_of_coverLin_admissibleKernel Λ C hQ hc o _
    (coverLin_blackLinear_eq_zeroQ Wgt hC o ho (Fam) (Sc) _
      (thetaScalars_blackScalarsQ Λ C hQ o ho) (cover_s_eq_zero Λ C hQ)
      (cover_brundanUpKLR Λ C hQ) (cover_mixedInversion Λ C hQ) μ u' v' s t hst htt f hf)

/-- **The mixed black relations (2.4a) and (2.3c) at the black scalars are cover
red-negligible.** -/
theorem coverRedNegligible_mixedBlackRelationQ
    (a : MixedBlackRelation (I ⊕ Fin ℓ → ℤ) I ℓ) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o (mixedBlackRelation (RDc) (redWeight Wgt) k
        (blackScalarsQ Λ C hQ).t a)) :=
  coverRedNegligible_of_coverLin_admissibleKernel Λ C hQ hc o _
    (coverLin_mixedBlackRelation_eq_zeroQ Wgt hC o ho (Fam) (Sc) _
      (thetaScalars_blackScalarsQ Λ C hQ o ho) (cover_s_eq_zero Λ C hQ)
      (cover_brundanUpKLR Λ C hQ) (cover_mixedInversion Λ C hQ) (blackScalarsQ_r Λ C hQ) a)

/-- **The black biadjunction and dot cyclicity relations are cover red-negligible** (general
parameters). -/
theorem coverRedNegligible_blackAdjunctionQ
    (P : Presentation.{v, u} (signature (RDc) (redWeight Wgt)) k)
    (r : BlackAdjunctionRelation (I ⊕ Fin ℓ → ℤ) I ℓ) :
    CoverRedNegligible.{u, v, w} Λ C hQ hc
      (coverCL Λ C hQ o ((addBlackAdjunctionRelations (RDc) (redWeight Wgt) P).rel (.inr r))) :=
  coverRedNegligible_of_coverLin_admissibleKernel Λ C hQ hc o _
    (coverLin_blackAdjunction_eq_zeroQ Wgt hC o ho (Fam) (Sc) _
      (thetaScalars_blackScalarsQ Λ C hQ o ho) (cover_s_eq_zero Λ C hQ)
      (cover_brundanUpKLR Λ C hQ) (cover_mixedInversion Λ C hQ) P r)

end Categorification.Stendhal
