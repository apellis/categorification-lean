/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGradedRestriction
import Categorification.KLR.CyclotomicGradedCharacter
import Categorification.KLR.CyclotomicInductionDotted

/-!
# Degrees of the cyclotomic commutator maps

Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.2. On the actual lower
corner the crossing has degree −deg(xᵢ) and the r-th dotted unit and
counit have degree r deg(xᵢ) before the shifts in the source and target.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour KLRAlgebra.AbsentColour.InductionCalculus
open Categorification.Graded CategoryTheory
open scoped ModuleCat.Algebra

variable {k I : Type*} [CommRing k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I) (β : Multiset I)
local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "B" => (Si + β)
local notation "U" => (Si + B)
local notation "Rl" => CycKLR k Q aΛ β
local notation "Su" => CycKLR k Q aΛ B
local notation "Tu" => CycKLR k Q aΛ U

/-- The crossing cut by the last two i-strands has degree −deg(xᵢ). -/
theorem crossingElement_mem_grade :
    crossingElement Q i aΛ β ∈ grade G Λ U (- G.degX i) := by
  rw [crossingElement, neg_mul]
  apply Submodule.neg_mem
  rw [doubleIdem, ← map_one (mk k Q aΛ β), AbsentColour.cyclotomicLast_mk, AbsentColour.cyclotomicLast_mk, ← map_mul]
  apply Graded.mem_map_of_mem
  rw [← sum_e (k := k) (Q := Q) (ν := β)]
  change _ * ((cLLinear (Q := Q) i B).comp (cLLinear i β)) (∑ s : Seq β, e s) ∈ _
  rw [map_sum, Finset.mul_sum]
  apply Submodule.sum_mem
  intro s _
  change _ * cL Q i B (cL Q i β (e s)) ∈ _
  rw [cL_e, cL_e]
  let t := Seq.cast (add_comm B Si) ((Seq.cast (add_comm β Si) (s.append default)).append default)
  have he : t.lbl ⟨β.card + 1, by simp⟩ = i := by
    simp only [t, Seq.cast_apply]
    rw [Seq.append_apply_ge _ _ _ (by change Multiset.card B ≤ β.card + 1; simp)]
    exact Multiset.mem_singleton.mp (Seq.mem _ _)
  have hf : t.lbl ⟨β.card, by simp⟩ = i := (doubleLast_labels i β s).trans he
  simpa only [hf, he, G.degΨ_self] using
    (G.ψ_mul_e_mem_grade (j := β.card) (by simp) t)

/-- The degree of the dotted generator of the induction corner. -/
theorem dotPowCorner_generator_mem_grade (d : ℕ) :
    (dotPowCorner Q i aΛ β d (indGenerator Q i aΛ β)).1 ∈ grade G Λ B (d • G.degX i) := by
  have H := dotUnitTerm_mem_grade G Λ i β d (x := 1) SetLike.GradedOne.one_mem
  rw [zero_add] at H
  change lastIdem Q i aΛ β * dotElement Q i aΛ β ^ d * lastIdem Q i aΛ β ∈ _ at H
  have hc : Commute (dotElement Q i aΛ β ^ d) (lastIdem Q i aΛ β) := (dot_commute Q i aΛ β 1).pow_left d
  rw [mul_assoc, hc.eq, ← mul_assoc,
    lastIdem_mul] at H
  exact H
/-- The crossing coefficient in the present-colour EF–FE comparison. -/
theorem sigma_insert_mem_grade {j : ℤ} {x : IndCorner Q i aΛ β}
    (hx : x.1 ∈ grade G Λ B j) :
    (cyclotomicSigma Q i β aΛ (PresentColour.insertIdem Q i β aΛ x) : Tu) ∈
      grade G Λ U (j - G.degX i) := by
  have he : (cyclotomicSigma Q i β aΛ (PresentColour.insertIdem Q i β aΛ x) : Tu) =
      AbsentColour.cyclotomicLast Q i aΛ B x.1 * crossingElement Q i aΛ β := by
    unfold PresentColour.insertIdem
    change (cyclotomicSigma Q i β aΛ (BalancedTensor.tmul _ _) : Tu) = _
    rw [cyclotomicSigma_tmul_canonical, map_neg, mul_assoc]
    rfl
  rw [he, sub_eq_add_neg]
  exact SetLike.GradedMul.mul_mem (A := grade G Λ U)
    (cyclotomicLast_mem_grade G Λ i B hx) (crossingElement_mem_grade G Λ i β)

/-- The dotted counit coefficient in the nonpositive-weight comparison. -/
theorem counit_insert_mem_grade {j : ℤ} {x : IndCorner Q i aΛ β}
    (hx : x.1 ∈ grade G Λ B j) (r : ℕ) :
    cyclotomicDotCounit Q i β aΛ r (PresentColour.insertIdem Q i β aΛ x) ∈
      grade G Λ B (j + r • G.degX i) := by
  have he : cyclotomicDotCounit Q i β aΛ r (PresentColour.insertIdem Q i β aΛ x) =
      x.1 * (dotPowCorner Q i aΛ β r (indGenerator Q i aΛ β)).1 := by
    change cyclotomicDotCounit Q i β aΛ r (BalancedTensor.tmul _ _) = _
    rw [cyclotomicDotCounit_tmul, map_pow]
    change x.1 * dotElement Q i aΛ β ^ r * lastIdem Q i aΛ β =
      x.1 * (lastIdem Q i aΛ β * dotElement Q i aΛ β ^ r)
    rw [mul_assoc]
    exact congrArg (x.1 * ·) ((dot_commute Q i aΛ β 1).pow_left r).eq
  rw [he]
  exact SetLike.GradedMul.mul_mem (A := grade G Λ B) hx (dotPowCorner_generator_mem_grade G Λ i β r)

end Categorification.KLR.CycKLR
