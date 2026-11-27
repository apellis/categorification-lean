/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidModule
import Categorification.WeightedKLR.Rigidity.CupCapMidRelIsotopy
import Categorification.WeightedKLR.Rigidity.CupCapMidRelSquare

/-!
# The KLR relations on the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. Every defining relation of the KLR algebra
of `λ` holds on the model with the maximum before `λ_{j+1}`, given the braid relation
(`CupCap.midKLRRel_of_braid`); the quadratic relation uses the loops (max2), so this needs
`PullOff L`, `PullOffLeft L` and invertible cup scalars.

## Main results

* `CupCap.midKLRRel_of_braid`: `MidKLRRel` from the braid relation on the model.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)

variable {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "φ" => midFree j hj Q Λ Λc ν ν₀
local notation "Fe" => midIdem j hj Q Λ Λc ν ν₀
local notation "Fx" => midDot j hj Q Λ Λc ν ν₀
local notation "Fψ" => midCross j hj Q Λ Λc ν ν₀

/-- The braid relation of the KLR algebra of `λ` on the model. -/
def MidBraidRel : Prop :=
  ∀ (p : ℕ) (h : p + 2 < m) (i : Seq (stendhalWeight ℓ ν)),
    MidRel j hj Q Λ Λc ν ν₀ L hL
      ((Fψ p * Fψ (p + 1) * Fψ p - Fψ (p + 1) * Fψ p * Fψ (p + 1)) * Fe i)
      (if i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 2, h⟩ ∧
          i.lbl ⟨p, by omega⟩ ≠ i.lbl ⟨p + 1, by omega⟩ then
        ncEval ![Fx ⟨p, by omega⟩, Fx ⟨p + 1, by omega⟩, Fx ⟨p + 2, h⟩]
          (qbar (stendhalQ Q Λ (i.lbl ⟨p, by omega⟩) (i.lbl ⟨p + 1, by omega⟩))) * Fe i
      else 0)

theorem midFree_ncEval_two (a b : Fin m) (P : MvPolynomial (Fin 2) k) :
    (φ (ncEval ![fx k _ a, fx k _ b] P)).val = ncEval ![Fx a, Fx b] P := by
  rw [midFree_ncEval]
  congr 1
  funext c
  fin_cases c <;> simp [midFree_fx]

theorem midFree_ncEval_three (a b c : Fin m) (P : MvPolynomial (Fin 3) k) :
    (φ (ncEval ![fx k _ a, fx k _ b, fx k _ c] P)).val = ncEval ![Fx a, Fx b, Fx c] P := by
  rw [midFree_ncEval]
  congr 1
  funext d
  fin_cases d <;> simp [midFree_fx]

/-- **The KLR relations of `λ` on the model**, given the braid relation. The quadratic relation
uses the loops (max2), hence the route hypotheses `PullOff L`, `PullOffLeft L` (Lemma 7.16 and
its mirror) and invertible cup scalars. -/
theorem midKLRRel_of_braid (hκ : ∀ i, IsUnit (cupScalar Q ν₀ i)) (hP : PullOff k Q Λc ν₀ L)
    (hPL : PullOffLeft k Q Λc ν₀ L) (hB : MidBraidRel (j := j) (hj := hj) (Q := Q) (Λ := Λ)
      (Λc := Λc) (ν := ν) (ν₀ := ν₀) (L := L) (hL := hL)) :
    MidKLRRel j hj Q Λ Λc ν ν₀ L hL := by
  intro a b hab
  induction hab with
  | idem_mul s t =>
    refine MidRel.of_eq ?_
    by_cases h : s = t <;> simp [h, midFree_fe, midIdem_mul_midIdem]
  | idem_sum =>
    simpa [map_sum, midFree_fe] using midRel_sum_midIdem
  | dot_idem a i =>
    refine MidRel.of_eq ?_
    simp [midFree_fe, midFree_fx, midDot_mul_midIdem]
  | cross_idem p i =>
    refine MidRel.of_eq ?_
    simp [midFree_fe, midFree_fψ, midCross_mul_midIdem]
  | cross_zero p h =>
    refine MidRel.of_eq ?_
    simp [midFree_fψ, midCross_eq_zero p h]
  | dot_dot a b =>
    refine MidRel.of_eq ?_
    simp [midFree_fx, midDot_mul_midDot]
  | cross_cross p q h =>
    simpa [midFree_fψ] using midRel_cross_cross p q h
  | dot_cross a p h₁ h₂ =>
    simpa [midFree_fψ, midFree_fx] using midRel_dot_cross a p h₁ h₂
  | dot_cross_left p h i =>
    have := midRel_dot_cross_left (j := j) (hj := hj) (Λ := Λ) (L := L) (hL := hL) p h i
    by_cases hi : i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 1, h⟩ <;>
      simpa [hi, midFree_fψ, midFree_fx, midFree_fe] using this
  | dot_cross_right p h i =>
    have := midRel_dot_cross_right (j := j) (hj := hj) (Λ := Λ) (L := L) (hL := hL) p h i
    by_cases hi : i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 1, h⟩ <;>
      simpa [hi, midFree_fψ, midFree_fx, midFree_fe] using this
  | cross_sq p h i =>
    have := midRel_cross_sq (j := j) (hj := hj) (Λ := Λ) (hL := hL) hκ hP hPL p h i
    by_cases hi : i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 1, h⟩
    · simpa [hi, midFree_fψ, midFree_fe] using this
    · simpa [hi, midFree_fψ, midFree_fe, midFree_ncEval_two] using this
  | braid p h i =>
    have := hB p h i
    by_cases hi : i.lbl ⟨p, by omega⟩ = i.lbl ⟨p + 2, h⟩ ∧
        i.lbl ⟨p, by omega⟩ ≠ i.lbl ⟨p + 1, by omega⟩
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hi)] at this ⊢
      simpa only [map_mul, Subalgebra.coe_mul, midFree_fe, midFree_ncEval_three, map_sub,
        Subalgebra.coe_sub, midFree_fψ] using this
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hi)] at this ⊢
      simpa only [map_mul, Subalgebra.coe_mul, midFree_fe, map_zero, ZeroMemClass.coe_zero,
        map_sub, Subalgebra.coe_sub, midFree_fψ] using this

end Categorification.Stendhal.CupCap
