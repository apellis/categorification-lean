/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleExteriorMap
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorMiddleRows
import Categorification.WeightedKLR.RedStrands.LoadingCutPBW

import Mathlib.Algebra.Homology.ShortComplex.Basic
/-!
# The exterior-to-middle crossing for the label-two unknot

Webster, arXiv:1309.3796v2, §8.2, printed page 80. The two return words
are killed in the middle dot-sum quotient by the mixed braid correction.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] (param : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "ν" => Multiset.replicate 2 ()
local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "S" => stendhalQ param wt
local notation "H" => KLRAlgebra k S μ
local notation "π" => tensorOfKLR param wt ν
local notation "B" => labelTwoMiddleLoading
local notation "C" => labelTwoExteriorLeftLoading
local notation "X₁" => (x (⟨1, by decide⟩ : Fin (Multiset.card μ)) : H)
local notation "X₃" => (x (⟨3, by decide⟩ : Fin (Multiset.card μ)) : H)

private theorem orderedB : IsRedOrdered B := by unfold IsRedOrdered; decide +kernel
private theorem orderedC : IsRedOrdered C := by unfold IsRedOrdered; decide +kernel
local notation "M" => leftStandard param wt B orderedB
local notation "g" => leftStandardUnit param wt B orderedB

private theorem proj_mul_edge (u v : H) : π (u * v) = π u * π v := by
  simp only [tensorOfKLR, map_mul]

private theorem proj_loading_edge (s : KLR.Seq μ) (h : IsRedOrdered s) :
    π (e s) = seqIdem param wt s h := by
  apply congrArg (TensorProductAlgebra.mk param wt ν)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left h)

private theorem middle_gen_fixed : π (e B) • (g : M) = g := by
  rw [proj_loading_edge param _ orderedB, leftStandardUnit, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (seqIdem_mul_self param wt _ _)

private theorem middle_left_cross_zero : π (ψ 2) • (g : M) = 0 := by
  have hs : StendhalLT B C := by unfold StendhalLT StendhalLE; decide +kernel
  have h := seqIdem_smul_leftStandard_eq_zero param wt orderedB orderedC hs (π (ψ 2) • (g : M))
  rw [← middle_gen_fixed param, ← mul_smul] at h
  rw [← proj_loading_edge param _ orderedC, ← mul_smul, ← proj_mul_edge, ← proj_mul_edge] at h
  have hc : sadj (Multiset.card μ) 2 • B = C := by decide
  have ha : (e C * ψ 2 * e B : H) = ψ 2 * e B := by
    rw [mul_assoc, ψ_mul_e, hc, ← mul_assoc, e_mul_self]
  rw [ha, proj_mul_edge, mul_smul, middle_gen_fixed] at h
  exact h

/-- The two equal-black mixed braid words differ by the dot sum on the middle generator. -/
theorem labelTwo_otherExterior_middleBraid :
    π (ψ 1 * ψ 2 * ψ 1 : H) • (g : M) = π (X₁ + X₃) • g := by
  have hb := StendhalAlgebraAllOrders.braid_black_red_black
    (k := k) (Q := param) (Λ := wt) («ν» := ν) 1 (by decide) B () 1 rfl rfl rfl
  let proj := (TensorProductAlgebra.mk param wt ν).comp (orderProjection param wt ν)
  have hp := congrArg (fun a => proj a) hb
  simp only [Finsupp.single_eq_same, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub,
    pow_zero, pow_one, mul_one, one_mul, zero_add, proj, map_sub, map_mul,
    map_add] at hp
  have he : (π (ψ 1 * ψ 2 * ψ 1 : H) - π (ψ 2 * ψ 1 * ψ 2 : H)) * π (e B) =
      (π X₃ + π X₁) * π (e B) := by
    simpa only [AlgHom.comp_apply, tensorOfKLR, map_sub, map_mul, StendhalAlgebraAllOrders.x,
      StendhalAlgebraAllOrders.ψ, StendhalAlgebraAllOrders.e] using hp
  have hz : π (ψ 2 * ψ 1 * ψ 2 : H) • (g : M) = 0 := by
    simp only [proj_mul_edge, mul_smul, middle_left_cross_zero, smul_zero]
  have actEq := congrArg (· • (g : M)) he
  rw [mul_smul, mul_smul, middle_gen_fixed, sub_smul, hz, sub_zero] at actEq
  have hsum : π (X₁ + X₃) = π X₃ + π X₁ := by
    rw [add_comm X₁ X₃]
    simp only [tensorOfKLR, map_add]
  rw [hsum]
  exact actEq

local notation "SPlus" => labelTwoMiddleDotSumEnd param
local notation "middleQuotient" => M ⧸ LinearMap.range SPlus
local notation "gbar" => (Submodule.Quotient.mk g : middleQuotient)

/-- The braid return is zero in the actual middle dot-sum quotient. -/
theorem labelTwo_otherExterior_triple_quotient_zero :
    π (ψ 1 * (ψ 2 * (ψ 1 * e B)) : H) • gbar = 0 := by
  have hw : (ψ 1 * (ψ 2 * (ψ 1 * e B)) : H) = (ψ 1 * ψ 2 * ψ 1) * e B := by
    simp only [mul_assoc]
  have hg : π (ψ 1 * (ψ 2 * (ψ 1 * e B)) : H) • (g : M) = SPlus g := by
    rw [hw, proj_mul_edge, mul_smul, middle_gen_fixed, labelTwo_otherExterior_middleBraid]
    exact (labelTwoMiddleDotSumEnd_generator param).symm
  have hq := congrArg ((LinearMap.range SPlus).mkQ) hg
  rw [map_smul] at hq
  refine hq.trans ?_
  change (Submodule.Quotient.mk (SPlus g) : middleQuotient) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨g, rfl⟩


local notation "A" => labelTwoExteriorRightLoading
local notation "T" => TensorProductAlgebra k param wt ν
local notation "m" => Multiset.card μ
local notation "X₂" => (x (⟨2, by decide⟩ : Fin m) : H)
local notation "pa" => (X₂ * ψ 2 * e A : H)
local notation "J" => (ψ 1 * (ψ 2 * (ψ 1 * e B)) : H)
local notation "W" => (ψ 2 * (ψ 1 * e B) : H)

private theorem orderedA : IsRedOrdered A := by unfold IsRedOrdered; decide +kernel

private theorem rightProjector_support :
    (e A * pa : H) = pa := by
  have hc : IsConstOn A 2 2 := by unfold IsConstOn; decide
  have hcomm := blockElt_mul_e (Q := S) hc
  rw [blockElt_two (by decide : 2 + 1 < m)] at hcomm
  rw [hcomm, ← mul_assoc, e_mul_self, ← hcomm]

private def rightExteriorImage : middleQuotient :=
  π (pa * (ψ 1 * e B)) • gbar

private theorem rightExteriorImage_fixed :
    seqIdem param wt A orderedA • rightExteriorImage param = rightExteriorImage param := by
  rw [rightExteriorImage, ← mul_smul, ← proj_loading_edge param _ orderedA,
    ← proj_mul_edge, ← mul_assoc, rightProjector_support]

private theorem otherReturn_transporters (w : Equiv.Perm (Fin m)) (hw : w • A = B) :
    w = wordProd m [1] ∨ w = wordProd m [1,2] := by
  have h : ∀ v : Equiv.Perm (Fin m), v • A = B →
      v = wordProd m [1] ∨ v = wordProd m [1,2] := by decide +kernel
  exact h w hw

private def otherReturnChoice (w : Equiv.Perm (Fin m)) : List ℕ :=
  if w = wordProd m [1] then [1]
  else if w = wordProd m [1,2] then [1,2]
  else canWord m w

private theorem otherReturnChoice_spec (w : Equiv.Perm (Fin m)) :
    IsReduced m (otherReturnChoice w) ∧ wordProd m (otherReturnChoice w) = w := by
  unfold otherReturnChoice
  split_ifs with h₁ h₂
  · subst w
    refine ⟨⟨?_,?_⟩,rfl⟩
    · intro j hj
      simp only [List.mem_singleton] at hj
      subst j
      decide
    · rw [length_eq_invCount]
      decide +kernel
  · subst w
    refine ⟨⟨?_,?_⟩,rfl⟩
    · intro j hj
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hj
      rcases hj with h | h <;> subst j <;> decide
    · rw [length_eq_invCount]
      decide +kernel
  · exact ⟨isReduced_canWord _ _,wordProd_canWord _ _⟩

private theorem polynomial_triple_quotient_zero (p : MvPolynomial (Fin m) k) :
    π (pol p * J) • gbar = 0 := by
  calc
    _ = π (pol p) • (π J • gbar) := by rw [proj_mul_edge, mul_smul]
    _ = π (pol p) • (0 : middleQuotient) :=
      congrArg (π (pol p) • ·) (labelTwo_otherExterior_triple_quotient_zero param)
    _ = 0 := smul_zero _

private theorem otherExterior_word_annihilates (w : Equiv.Perm (Fin m))
    (hw : w • A = B) (p : MvPolynomial (Fin m) k) :
    π ((ψw (otherReturnChoice w) * pol p * e A) * W) • gbar = 0 := by
  rcases otherReturn_transporters w hw with h | h
  · have hword : (ψw (otherReturnChoice w) : H) = ψ 1 := by
      rw [h, otherReturnChoice, ite_eq_left rfl, ψw_cons, ψw_nil, mul_one]
    have eword : ((ψw (otherReturnChoice w) * pol p * e A) * W : H) =
        (ψ 1 * pol p * e A) * W :=
      congrArg (fun v : H => (v * pol p * e A) * W) hword
    have hs := (congrArg (fun v : H => π v • gbar)
      (eword.trans (labelTwo_otherExterior_firstRow S p)))
    exact hs.trans (polynomial_triple_quotient_zero param _)
  · have hword : (ψw (otherReturnChoice w) : H) = ψ 1 * ψ 2 := by
      rw [h, otherReturnChoice, ite_eq_right (by decide +kernel), ite_eq_left rfl]
      simp only [ψw_cons, ψw_nil, mul_one]
    have eword : ((ψw (otherReturnChoice w) * pol p * e A) * W : H) =
        (ψ 1 * (ψ 2 * pol p * e A)) * W := by
      simp only [hword, mul_assoc]
    have hs := (congrArg (fun v : H => π v • gbar)
      (eword.trans (labelTwo_otherExterior_secondRow S p)))
    exact hs.trans (polynomial_triple_quotient_zero param _)

private theorem smul_smul_eq_zero_of_mapped_product
    {D R N : Type*} [Mul D] [Monoid R] [MulAction R N] [Zero N]
    (F : D → R) (mulF : ∀ a b : D, F (a * b) = F a * F b)
    (a b c : D) (v : N) (h : a * b = c) (hz : F c • v = 0) :
    F a • (F b • v) = 0 := by
  rw [← mul_smul, ← mulF, h, hz]

private theorem rightExteriorImage_row_annihilates
    (w : Equiv.Perm (Fin m)) (hw : w • A = B) (f : MvPolynomial (Fin m) k) :
    π (ψw (otherReturnChoice w) * pol f * e A) • rightExteriorImage param = 0 :=
  smul_smul_eq_zero_of_mapped_product (D := H) (R := T) (N := middleQuotient)
    π (proj_mul_edge param) (ψw (otherReturnChoice w) * pol f * e A)
    (pa * (ψ 1 * e B)) _ gbar
    (labelTwo_otherExterior_projectorRow S (ψw (otherReturnChoice w)) f)
    (otherExterior_word_annihilates param w hw _)

set_option maxHeartbeats 500000 in
private theorem rightExteriorImage_middle_annihilation (z : T) :
    (seqIdem param wt B orderedB * z) • rightExteriorImage param = 0 := by
  exact loading_mul_smul_eq_zero_of_projected_PBW («M» := middleQuotient) param wt
    otherReturnChoice_spec orderedA orderedB (rightExteriorImage param)
    (rightExteriorImage_fixed param) (rightExteriorImage_row_annihilates param) z

private theorem above_rightExterior (s : KLR.Seq μ) (ho : IsRedOrdered s)
    (hv : ¬ IsViolated s) (h : StendhalLT A s) : s = B ∨ s = C := by
  have firstRed : (s.lbl ⟨0, by decide⟩).isLeft = false := by
    cases he : (s.lbl ⟨0, by decide⟩).isLeft
    · rfl
    · exact (hv ⟨by decide, he⟩).elim
  obtain ⟨w, rfl⟩ := KLR.Seq.exists_smul_eq A s
  have cases : ∀ v : Equiv.Perm (Fin m), ((v • A).lbl ⟨0, by decide⟩).isLeft = false →
      IsRedOrdered (v • A) → StendhalLT A (v • A) → v • A = B ∨ v • A = C := by
    unfold IsRedOrdered StendhalLT StendhalLE
    decide +kernel
  exact cases w firstRed ho h

private theorem upper_rightExterior_kills (s : KLR.Seq μ) (hs : IsRedOrdered s)
    (z : T) (h : StendhalLT A s) :
    (seqIdem param wt s hs * z) • rightExteriorImage param = 0 := by
  by_cases hv : IsViolated s
  · have hzero : seqIdem param wt s hs = 0 := by
      change (StendhalAlgebra.violatedIdeal k param wt ν).ringCon.mk' _ = 0
      rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
      exact TwoSidedIdeal.subset_span ⟨s, hs, hv, rfl⟩
    rw [hzero, zero_mul, zero_smul]
  · rcases above_rightExterior s hs hv h with rfl | rfl
    · exact rightExteriorImage_middle_annihilation param z
    · have hc : StendhalLT B C := by unfold StendhalLT StendhalLE; decide +kernel
      rw [mul_smul]
      obtain ⟨u, hu⟩ := (LinearMap.range SPlus).mkQ_surjective (z • rightExteriorImage param)
      rw [← hu, ← map_smul, seqIdem_smul_leftStandard_eq_zero param wt orderedB hs hc, map_zero]

/-- The exterior-to-middle crossing sends the exterior generator to the
terminal nilHecke projection of the crossing on the middle generator. -/
def labelTwoExteriorToMiddle :
    leftStandard param wt A orderedA →ₗ[T] middleQuotient :=
  leftStandardLift A orderedA (rightExteriorImage param) (upper_rightExterior_kills param)

theorem labelTwoExteriorToMiddle_unit :
    labelTwoExteriorToMiddle param (leftStandardUnit param wt A orderedA) =
      rightExteriorImage param :=
  leftStandardLift_unit A orderedA _ (rightExteriorImage_fixed param) (upper_rightExterior_kills param)

/-- The two crossing maps have zero composite on the full exterior standard. -/
theorem labelTwoExterior_crossing_composite_zero :
    (labelTwoMiddleExteriorDifferential param).comp (labelTwoExteriorToMiddle param) = 0 := by
  apply leftStandard_hom_ext A orderedA
  rw [LinearMap.comp_apply, labelTwoExteriorToMiddle_unit, rightExteriorImage, map_smul]
  apply Subtype.ext
  have hg : (labelTwoMiddleExteriorDifferential param gbar).val =
      π (ψ 2 * e C) * labelTwoLeftExteriorProjector param := by
    unfold labelTwoMiddleExteriorDifferential
    rw [labelTwoMiddleDotSumToExterior_mk, labelTwoMiddleToExterior_unit]
    rfl
  change π (pa * (ψ 1 * e B)) * (labelTwoMiddleExteriorDifferential param gbar).val = 0
  rw [hg, ← mul_assoc, ← proj_mul_edge, labelTwoLeftExteriorProjector, ← proj_mul_edge]
  have hjoin : ((pa * (ψ 1 * e B)) * (ψ 2 * e C) : H) = pa * (ψ 1 * (ψ 2 * e C)) := by
    simp only [mul_assoc, labelTwo_middleCut_ψ]
  rw [hjoin, labelTwo_otherExterior_slide_complement]
  simp only [tensorOfKLR, map_zero]

local notation "startStandard" => leftStandard param wt A orderedA
local notation "startGen" => leftStandardUnit param wt A orderedA

/-- Projection to the right exterior divided-power standard. -/
def labelTwoRightExteriorProjection : Module.End T startStandard :=
  leftStandardLift A orderedA (π pa • startGen) fun t ht z hlt => by
    rw [mul_smul]
    exact seqIdem_smul_leftStandard_eq_zero param wt orderedA ht hlt _

theorem labelTwoRightExteriorProjection_generator :
    labelTwoRightExteriorProjection param startGen = π pa • startGen := by
  apply leftStandardLift_unit
  have hmul : seqIdem param wt A orderedA * π pa = π pa := by
    rw [← proj_loading_edge param _ orderedA, ← proj_mul_edge, rightProjector_support]
  rw [← mul_smul, hmul]

theorem isIdempotentElem_labelTwoRightExteriorProjection :
    IsIdempotentElem (labelTwoRightExteriorProjection param) := by
  have hc : IsConstOn A 2 2 := by unfold IsConstOn; decide
  have hp := isIdempotentElem_blockIdem (Q := S) (by decide : 2 + 2 ≤ m) hc
  rw [blockIdem, blockElt_two (by decide : 2 + 1 < m)] at hp
  have hproj : π pa * π pa = π pa := by rw [← proj_mul_edge, hp.eq]
  change (labelTwoRightExteriorProjection param).comp (labelTwoRightExteriorProjection param) =
    labelTwoRightExteriorProjection param
  apply leftStandard_hom_ext A orderedA
  rw [LinearMap.comp_apply, labelTwoRightExteriorProjection_generator, map_smul,
    labelTwoRightExteriorProjection_generator, ← mul_smul, hproj]

/-- The actual divided-power summand at the right exterior loading. -/
def labelTwoRightExteriorDividedStandard : Submodule T startStandard :=
  LinearMap.range (labelTwoRightExteriorProjection param)

/-- The exterior-to-middle differential on the divided-power summand. -/
def labelTwoExteriorMiddleDifferential :
    labelTwoRightExteriorDividedStandard param →ₗ[T] middleQuotient :=
  (labelTwoExteriorToMiddle param).comp (labelTwoRightExteriorDividedStandard param).subtype

/-- The two adjacent crossing differentials form a complex. -/
theorem labelTwoExteriorMiddleDifferential_comp_zero :
    (labelTwoMiddleExteriorDifferential param).comp (labelTwoExteriorMiddleDifferential param) = 0 := by
  unfold labelTwoExteriorMiddleDifferential
  rw [← LinearMap.comp_assoc, labelTwoExterior_crossing_composite_zero, LinearMap.zero_comp]

/-- The three standard terms with their actual crossing maps, before a
grading shift or an exactness statement. -/
def labelTwoExteriorStandardComplex : CategoryTheory.ShortComplex (ModuleCat T) :=
  CategoryTheory.ShortComplex.mk
    (ModuleCat.ofHom (labelTwoExteriorMiddleDifferential param))
    (ModuleCat.ofHom (labelTwoMiddleExteriorDifferential param))
    (ModuleCat.hom_ext (labelTwoExteriorMiddleDifferential_comp_zero param))

end
end Categorification.Stendhal
