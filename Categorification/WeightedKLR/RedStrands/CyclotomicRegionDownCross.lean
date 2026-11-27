/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.InductionAlongBaseChange
import Categorification.TwoRep.BlockSumCrossingGen
import Categorification.WeightedKLR.RedStrands.CyclotomicRegionDotSlide

/-!
# The quotient crossings of a red line are natural for downward crossings

Webster, arXiv:1309.3796v3, (4.4d), in the proof of Theorem 4.25. The quotient crossing
`z ⊗ n ↦ π(z) ⊗ n` of a downward black strand with a red line is the base change of induction
along the cyclotomic projections (`cyclotomicRedDownQuotient_eq_baseChange`). Base change is
compatible with composites of inductions and with the crossing `ψ`, which the projection sends
to `ψ`; so a red line passes through a downward crossing (`cyclotomicRedDownQuotient_cross`,
`cyclotomicRedDownQuotient_signedCross`). Assembling through the weight-space blocks
(`globalRedDownQuotient_cross`) and the region factors gives the hypothesis
`DownQuotCrossNatural` for the region model (`regionDownQuotCrossNatural`).
-/

noncomputable section

namespace Categorification.Stendhal

open CategoryTheory KLR CyclotomicAction TwoRep QuantumGroup Polynomial InductionAlong

universe u v w u₁

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) {a b : I → k[X]} (hab : ∀ i, a i ∣ b i)

set_option backward.isDefEq.respectTransparency false in
/-- **The quotient crossing is base change of induction** along the cyclotomic projections. -/
theorem cyclotomicRedDownQuotient_eq_baseChange (i : I) {β γ : Multiset I} (h : {i} + β = γ) :
    cyclotomicRedDownQuotient.{u, v, w} Q hab i h =
      baseChange.{max u v, w} (cyclotomicRedProjection Q hab β).toRingHom
        (cyclotomicRedProjection Q hab γ).toRingHom
        (cyclotomicRedProjection_lastEmb Q hab i h) := by
  refine NatTrans.ext (funext fun M => ModuleCat.hom_ext (Ind.ext fun z n => ?_))
  change (cyclotomicRedDownQuotient Q hab i h).app M (Ind.tmul z n) = _
  rw [cyclotomicRedDownQuotient_tmul]
  rfl

variable (i j : I) {γ β β' δ : Multiset I} (h₁ : {j} + γ = β) (h₂ : {i} + β = δ)
  (h₃ : {i} + γ = β') (h₄ : {j} + β' = δ)

set_option backward.isDefEq.respectTransparency false in
/-- **A red line passes through a downward crossing** on blocks: the two ways of moving the
quotient crossings through `ψ` agree. -/
theorem cyclotomicRedDownQuotient_cross :
    Functor.whiskerRight (cyclotomicRedDownQuotient.{u, v, w} Q hab j h₁) (ind Q b i h₂) ≫
        Functor.whiskerLeft (ind Q a j h₁) (cyclotomicRedDownQuotient Q hab i h₂) ≫
        Functor.whiskerRight (cross Q a i j h₁ h₂ h₃ h₄) (cyclotomicRedPullback Q hab δ) =
      Functor.whiskerLeft (cyclotomicRedPullback Q hab γ) (cross Q b i j h₁ h₂ h₃ h₄) ≫
        Functor.whiskerRight (cyclotomicRedDownQuotient Q hab i h₃) (ind Q b j h₄) ≫
        Functor.whiskerLeft (ind Q a i h₃) (cyclotomicRedDownQuotient Q hab j h₄) := by
  simp only [cyclotomicRedDownQuotient_eq_baseChange]
  have C1 := baseChange_comp.{max u v, w} (cyclotomicRedProjection Q hab γ).toRingHom
    (cyclotomicRedProjection Q hab β).toRingHom (cyclotomicRedProjection Q hab δ).toRingHom
    (cyclotomicRedProjection_lastEmb Q hab j h₁) (cyclotomicRedProjection_lastEmb Q hab i h₂)
  have C2 := baseChange_comp.{max u v, w} (cyclotomicRedProjection Q hab γ).toRingHom
    (cyclotomicRedProjection Q hab β').toRingHom (cyclotomicRedProjection Q hab δ).toRingHom
    (cyclotomicRedProjection_lastEmb Q hab i h₃) (cyclotomicRedProjection_lastEmb Q hab j h₄)
  have N := baseChange_natTrans.{max u v, w} (cyclotomicRedProjection Q hab γ).toRingHom
    (cyclotomicRedProjection Q hab δ).toRingHom
    (fun x => (cyclotomicRedProjection_lastEmb Q hab i h₂ _).trans
      (congrArg _ (cyclotomicRedProjection_lastEmb Q hab j h₁ x)))
    (fun x => (cyclotomicRedProjection_lastEmb Q hab j h₄ _).trans
      (congrArg _ (cyclotomicRedProjection_lastEmb Q hab i h₃ x)))
    (intertwines_crossElt Q b i j h₁ h₂ h₃ h₄)
    (intertwines_crossElt Q a i j h₁ h₂ h₃ h₄)
    (by simp only [crossElt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      cyclotomicRedProjection_mk])
  simp only [cross, Functor.whiskerRight_comp, Functor.whiskerLeft_comp, Category.assoc]
  rw [reassoc_of% C1, ← reassoc_of% N]
  congr 2
  rw [← Functor.isoWhiskerLeft_inv, Iso.eq_inv_comp, Functor.isoWhiskerLeft_hom,
    ← Category.assoc, ← C2]
  simp only [Category.assoc, ← Functor.whiskerRight_comp, Iso.hom_inv_id,
    Functor.whiskerRight_id']
  erw [Category.comp_id]

/-- **A red line passes through a downward crossing** on blocks, for the signed crossing of the
cyclotomic family. -/
theorem cyclotomicRedDownQuotient_signedCross :
    Functor.whiskerRight (cyclotomicRedDownQuotient.{u, v, w} Q hab j h₁) (ind Q b i h₂) ≫
        Functor.whiskerLeft (ind Q a j h₁) (cyclotomicRedDownQuotient Q hab i h₂) ≫
        Functor.whiskerRight (signedCross Q a i j h₁ h₂ h₃ h₄) (cyclotomicRedPullback Q hab δ) =
      Functor.whiskerLeft (cyclotomicRedPullback Q hab γ) (signedCross Q b i j h₁ h₂ h₃ h₄) ≫
        Functor.whiskerRight (cyclotomicRedDownQuotient Q hab i h₃) (ind Q b j h₄) ≫
        Functor.whiskerLeft (ind Q a i h₃) (cyclotomicRedDownQuotient Q hab j h₄) := by
  have key := cyclotomicRedDownQuotient_cross Q hab i j h₁ h₂ h₃ h₄
  by_cases hij : i = j
  · unfold signedCross
    rw [ite_eq_left_of_eq_true _ _ (eq_true hij), ite_eq_left_of_eq_true _ _ (eq_true hij)]
    have hR : Functor.whiskerRight (-cross Q a i j h₁ h₂ h₃ h₄) (cyclotomicRedPullback Q hab δ) =
        -Functor.whiskerRight (cross Q a i j h₁ h₂ h₃ h₄) (cyclotomicRedPullback Q hab δ) := by
      ext M : 2
      exact (cyclotomicRedPullback Q hab δ).map_neg
    have hL : Functor.whiskerLeft (cyclotomicRedPullback Q hab γ) (-cross Q b i j h₁ h₂ h₃ h₄) =
        -Functor.whiskerLeft (cyclotomicRedPullback Q hab γ) (cross Q b i j h₁ h₂ h₃ h₄) := by
      ext M : 2
      rfl
    rw [hR, hL, Preadditive.comp_neg, Preadditive.comp_neg, Preadditive.neg_comp, key]
  · unfold signedCross
    rw [ite_eq_right_of_eq_false _ _ (eq_false hij), ite_eq_right_of_eq_false _ _ (eq_false hij)]
    exact key
