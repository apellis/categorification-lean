/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorSlide
import Categorification.KLR.CyclotomicTerminal
import Categorification.WeightedKLR.RedStrands.BlackIdempotent
import Categorification.WeightedKLR.RedStrands.LeftStandardModule
import Categorification.WeightedKLR.RedStrands.QuotientBasis

/-!
# The middle-to-exterior crossing in the label-two standard resolution

Webster, arXiv:1309.3796v2, §8.2, page 80. The return vector is killed by
the higher loading and by the middle dot sum. The corresponding map
descends to the middle dot-sum quotient.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] (param : Unit → Unit → MvPolynomial (Fin 2) k)

local notation "ν" => Multiset.replicate 2 ()
local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "leftLoad" => labelTwoExteriorLeftLoading
local notation "middleLoad" => labelTwoMiddleLoading
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "S" => stendhalQ param wt
local notation "T" => TensorProductAlgebra k param wt ν
local notation "H'" => KLRAlgebra k S μ
local notation "π" => tensorOfKLR param wt ν
local notation "E" => π (e leftLoad)
local notation "X₁" => (x (⟨1, by decide⟩ : Fin (Multiset.card μ)) : H')
local notation "X₂" => (x (⟨2, by decide⟩ : Fin (Multiset.card μ)) : H')

private theorem proj_mul (u v : H') : π (u * v) = π u * π v := by
  simp only [tensorOfKLR, map_mul]

private theorem proj_zero : π (0 : H') = 0 := by simp only [tensorOfKLR, map_zero]

private theorem leftExteriorIdem : IsIdempotentElem (E) := by
  change π (e leftLoad) * π (e leftLoad) = π (e leftLoad)
  rw [← proj_mul, e_mul_self]

private theorem projected_loading (s : KLR.Seq μ) (hs : IsRedOrdered s) :
    π (e s) = seqIdem param wt s hs := by
  apply congrArg (TensorProductAlgebra.mk param wt ν)
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs)

private theorem leftExterior_first_square_zero :
    π (X₁ * X₁ * e leftLoad) = 0 := by
  let bad := sadj (Multiset.card μ) 0 • leftLoad
  have ho : IsRedOrdered bad := by unfold IsRedOrdered; decide +kernel
  have hv : IsViolated bad := ⟨by decide, rfl⟩
  have hbad : π (e bad) = 0 := by
    rw [projected_loading param bad ho]
    change (StendhalAlgebra.violatedIdeal k param wt ν).ringCon.mk' _ = 0
    rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
    exact TwoSidedIdeal.subset_span ⟨bad, ho, hv, rfl⟩
  have hs := ψ_sq (Q := S) 0 (by decide : 1 < Multiset.card μ) leftLoad
  have hl : (leftLoad).lbl ⟨0, by decide⟩ = .inr 0 := rfl
  have hr : (leftLoad).lbl ⟨1, by decide⟩ = .inl () := rfl
  simp only [hl, hr, reduceCtorEq, ↓reduceIte, stendhalQ_inr_inl, Finsupp.single_eq_same] at hs
  have hsq : (ψ 0 * ψ 0 * e leftLoad : H') = X₁ * X₁ * e leftLoad := by
    simpa only [ncEval_x2, pow_two, map_mul, MvPolynomial.rename_X, Matrix.cons_val_one,
      Matrix.cons_val_zero, pol_X] using hs
  rw [← hsq, ← e_mul_ψ_mul_ψ, ← mul_assoc, e_mul_ψ]
  change π ((ψ 0 * e bad) * ψ 0) = 0
  rw [proj_mul, proj_mul, hbad, mul_zero, zero_mul]

private theorem leftExterior_affineCut_product {u v : H'}
    (hv : v * e leftLoad = e leftLoad * v) :
    (u * e leftLoad) * (v * e leftLoad) = u * v * e leftLoad := by
  rw [mul_assoc, ← mul_assoc (e leftLoad), ← hv, mul_assoc, e_mul_self, mul_assoc]

private theorem leftExterior_cross_commutes :
    (ψ 1 * e leftLoad : H') = e leftLoad * ψ 1 := by
  have h : sadj (Multiset.card μ) 1 • leftLoad = leftLoad := by decide
  rw [ψ_mul_e, h]

private def leftExteriorCutElem (z : H') (hz : z * e leftLoad = e leftLoad * z) :
    (leftExteriorIdem param).Corner := by
  refine ⟨π (z * e leftLoad), (Subsemigroup.mem_corner_iff (leftExteriorIdem param)).mpr ⟨?_,?_⟩⟩
  · rw [← proj_mul, ← mul_assoc, ← hz, mul_assoc, e_mul_self]
  · rw [← proj_mul, mul_assoc, e_mul_self]

/-- Both exterior black dots square to zero and their sum vanishes on the
left exterior cut in the actual two-red diagram algebra. -/
theorem labelTwo_leftExterior_dot_relations :
    π ((X₁ + X₂) * e leftLoad) = 0 ∧ π (X₂ * X₂ * e leftLoad) = 0 := by
  let fst := leftExteriorCutElem param X₁ (x_mul_e _ _)
  let snd := leftExteriorCutElem param X₂ (x_mul_e _ _)
  let nh := leftExteriorCutElem param (ψ 1) (leftExterior_cross_commutes param)
  have pp : fst * fst = 0 := Subtype.ext (by
    change π (X₁ * e leftLoad) * π (X₁ * e leftLoad) = 0
    rw [← proj_mul, leftExterior_affineCut_product param (x_mul_e _ _)]
    exact leftExterior_first_square_zero param)
  have dd : nh * nh = 0 := Subtype.ext (by
    change π (ψ 1 * e leftLoad) * π (ψ 1 * e leftLoad) = 0
    rw [← proj_mul, leftExterior_affineCut_product param (leftExterior_cross_commutes param)]
    have h := ψ_sq (Q := S) 1 (by decide : 2 < Multiset.card μ) leftLoad
    have he : (leftLoad).lbl ⟨1, by decide⟩ = (leftLoad).lbl ⟨2, by decide⟩ := rfl
    simp only [he, ↓reduceIte] at h
    rw [h, proj_zero])
  have right : nh * fst - snd * nh = 1 := Subtype.ext (by
    change π (ψ 1 * e leftLoad) * π (X₁ * e leftLoad) - π (X₂ * e leftLoad) * π (ψ 1 * e leftLoad) = π (e leftLoad)
    rw [← proj_mul, ← proj_mul, leftExterior_affineCut_product param (x_mul_e _ _),
      leftExterior_affineCut_product param (leftExterior_cross_commutes param)]
    have h := dot_cross_right (Q := S) 1 (by decide : 2 < Multiset.card μ) leftLoad
    have he : (leftLoad).lbl ⟨1, by decide⟩ = (leftLoad).lbl ⟨2, by decide⟩ := rfl
    simp only [he, ↓reduceIte, sub_mul] at h
    simpa only [tensorOfKLR, map_sub] using congrArg (π) h)
  have commute : fst * snd = snd * fst := Subtype.ext (by
    change π (X₁ * e leftLoad) * π (X₂ * e leftLoad) = π (X₂ * e leftLoad) * π (X₁ * e leftLoad)
    rw [← proj_mul, ← proj_mul, leftExterior_affineCut_product param (x_mul_e _ _),
      leftExterior_affineCut_product param (x_mul_e _ _), x_mul_x])
  obtain ⟨sum, sq, _⟩ := CycKLR.terminalTwoBlack_relations_of_first_dot_sq_zero fst snd nh pp dd right commute
  refine ⟨?_,?_⟩
  · change π ((X₁ + X₂) * e leftLoad) = 0
    rw [add_mul]
    have hs : π (X₁ * e leftLoad) + π (X₂ * e leftLoad) = 0 := congrArg Subtype.val sum
    simpa only [tensorOfKLR, map_add] using hs
  · have hv : π (X₂ * e leftLoad) * π (X₂ * e leftLoad) = 0 := congrArg Subtype.val sq
    rwa [← proj_mul, leftExterior_affineCut_product param (x_mul_e _ _)] at hv

/-- The mixed square on the left exterior cut vanishes in the actual tensor
product algebra by the terminal weight-two cyclotomic relation. -/
theorem labelTwo_leftExterior_return_square_zero :
    π ((ψ 2 * ψ 2 * e leftLoad : H')) = 0 := by
  have h := ψ_sq (Q := S) 2 (by decide : 3 < Multiset.card μ) leftLoad
  have hl : (leftLoad).lbl ⟨2, by decide⟩ = .inl () := rfl
  have hr : (leftLoad).lbl ⟨3, by decide⟩ = .inr 1 := rfl
  simp only [hl, hr, reduceCtorEq, ↓reduceIte, stendhalQ_inl_inr, Finsupp.single_eq_same] at h
  have hsq : (ψ 2 * ψ 2 * e leftLoad : H') = X₂ * X₂ * e leftLoad := by
    simpa only [ncEval_x2, pow_two, map_mul, MvPolynomial.rename_X,
      Matrix.cons_val_zero, pol_X] using h
  rw [hsq]
  exact (labelTwo_leftExterior_dot_relations param).2

local notation "n" => Multiset.card μ

private def returnChoice (w : Equiv.Perm (Fin n)) : List ℕ :=
  if w = wordProd n [2] then [2]
  else if w = wordProd n [1, 2] then [1, 2]
  else canWord n w

private theorem returnChoice_spec (w : Equiv.Perm (Fin n)) :
    IsReduced n (returnChoice w) ∧ wordProd n (returnChoice w) = w := by
  unfold returnChoice
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

private def projectAffine : H' →ₐ[k] T :=
  (TensorProductAlgebra.mk param wt ν).comp
    ((orderProjection param wt ν).comp (StendhalAlgebraAllOrders.ofKLR k param wt ν))

/-- The middle cut vector on the left exterior projective is killed by
every return to the left exterior loading. -/
theorem labelTwo_middleVector_annihilated_by_exterior (z : T) :
    E * z * π (ψ 2 * e leftLoad) = 0 := by
  classical
  let V := π (ψ 2 * e leftLoad)
  have hfix : π (e middleLoad) * V = V := by
    rw [← proj_mul, labelTwo_middleCut_ψ]
  have hz : z ∈ Submodule.span k (Set.range (tensorProductTerm returnChoice_spec param wt)) := by
    rw [span_tensorProductTerm returnChoice_spec param wt]
    trivial
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨term,rfl⟩ := hy
    let d := tensorProductTerm returnChoice_spec param wt term
    have hc : IsRedOrdered leftLoad := by unfold IsRedOrdered; decide +kernel
    have hb : IsRedOrdered middleLoad := by unfold IsRedOrdered; decide +kernel
    have hL : E * d = if term.1.2.1 • term.1.1 = leftLoad then d else 0 := by
      unfold d tensorProductTerm
      rw [projected_loading param _ hc, ← map_mul, e_mul_stendhalTerm]
      split_ifs <;> simp only [map_zero]
    have hR : d * π (e middleLoad) = if term.1.1 = middleLoad then d else 0 := by
      unfold d tensorProductTerm
      rw [projected_loading param _ hb, ← map_mul, stendhalTerm_mul_e]
      split_ifs <;> simp only [map_zero]
    change (E * d) * V = 0
    rw [hL]
    split_ifs with ht
    · rw [← hfix, ← mul_assoc, hR]
      split_ifs with hb'
      · have hw : term.1.2.1 • middleLoad = leftLoad := hb' ▸ ht
        have hd : d = π (KLRAlgebra.stdElt returnChoice term.1) := by
          apply congrArg (TensorProductAlgebra.mk param wt ν)
          apply Subtype.ext
          exact ((Subsemigroup.mem_corner_iff StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).mp
            (stendhalTerm param wt (fun w => (returnChoice_spec w).2) term).2).2.symm
        rw [hd,KLRAlgebra.stdElt,hb']
        have rows := labelTwo_middleReturn_rows_eq_zero S (projectAffine param).toRingHom
          (labelTwo_leftExterior_return_square_zero param) (MvPolynomial.monomial term.1.2.2 1)
        rcases labelTwo_middleToLeftExterior_transporters _ hw with ha | ha
        · rw [ha,returnChoice,ite_eq_left rfl]
          simpa only [projectAffine,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AlgHom.comp_apply,
            proj_mul,ψw_cons,ψw_nil,mul_one,V] using rows.1
        · rw [ha,returnChoice,ite_eq_right (by decide +kernel),ite_eq_left rfl]
          simpa only [projectAffine,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AlgHom.comp_apply,
            proj_mul,ψw_cons,ψw_nil,mul_one,mul_assoc,V] using rows.2
      · exact zero_mul _
    · exact zero_mul _
  | zero => rw [mul_zero, zero_mul]
  | add u v _ _ ha hb => rw [mul_add,add_mul,ha,hb,add_zero]
  | smul t a _ ha => rw [mul_smul_comm,smul_mul_assoc,ha,smul_zero]

private theorem middleRedOrdered : IsRedOrdered middleLoad := by
  unfold IsRedOrdered
  decide +kernel

private theorem higher_than_middle (s : KLR.Seq μ) (hs : IsRedOrdered s)
    (hv : ¬ IsViolated s) (hle : StendhalLT middleLoad s) : s = leftLoad := by
  have hfirst : (s.lbl ⟨0, by decide⟩).isLeft = false := by
    cases h : (s.lbl ⟨0, by decide⟩).isLeft
    · rfl
    · exact (hv ⟨by decide, h⟩).elim
  obtain ⟨w, rfl⟩ := KLR.Seq.exists_smul_eq leftLoad s
  have classify : ∀ v : Equiv.Perm (Fin n), ((v • leftLoad).lbl ⟨0, by decide⟩).isLeft = false →
      IsRedOrdered (v • leftLoad) → StendhalLT middleLoad (v • leftLoad) → v • leftLoad = leftLoad := by
    unfold IsRedOrdered StendhalLT StendhalLE
    decide +kernel
  exact classify w hfirst hs hle

/-- The complementary primitive projector in the left exterior loading. Its
first-dot action supplies the second middle coordinate of the return map. -/
def labelTwoLeftExteriorProjector : T := π (e leftLoad - X₁ * ψ 1 * e leftLoad)

local notation "P" => labelTwoLeftExteriorProjector param

theorem isIdempotentElem_labelTwoLeftExteriorProjector : IsIdempotentElem (P) := by
  have hc : IsConstOn leftLoad 1 2 := by unfold IsConstOn; decide
  have hp := isIdempotentElem_blockIdem (Q := S) (by decide : 1 + 2 ≤ Multiset.card μ) hc
  have hcomm := blockElt_mul_e (Q := S) hc
  rw [blockElt_two (by decide : 1 + 1 < Multiset.card μ)] at hcomm
  rw [blockIdem, blockElt_two (by decide : 1 + 1 < Multiset.card μ)] at hp
  let p := (X₁ * ψ 1 * e leftLoad : H')
  have hpR : p * e leftLoad = p := by
    change (X₁ * ψ 1 * e leftLoad) * e leftLoad = _
    rw [mul_assoc, e_mul_self]
  have hpL : e leftLoad * p = p := by
    change e leftLoad * (X₁ * ψ 1 * e leftLoad) = _
    rw [hcomm, ← mul_assoc, e_mul_self, ← hcomm]
  have h : IsIdempotentElem (e leftLoad - p) := by
    change (_ - _) * (_ - _) = _
    rw [sub_mul, mul_sub, mul_sub, e_mul_self, hpR, hpL, hp.eq, sub_self, sub_zero]
  exact h.map (projectAffine param)

private def middleReturnVector : lIdeal (P) :=
  ⟨π (ψ 2 * e leftLoad) * P, by
    apply mem_lIdeal.mpr
    rw [mul_assoc, (isIdempotentElem_labelTwoLeftExteriorProjector param).eq]⟩

/-- The red-black return crossing defines a map from the middle standard
to the actual left-exterior divided projective. -/
def labelTwoMiddleToExterior :
    leftStandard param wt middleLoad middleRedOrdered →ₗ[T] lIdeal (P) :=
  leftStandardLift middleLoad middleRedOrdered (middleReturnVector param) fun s hs z hle => by
    apply Subtype.ext
    change (seqIdem param wt s hs * z) * (π (ψ 2 * e leftLoad) * P) = 0
    by_cases hv : IsViolated s
    · have hzero : seqIdem param wt s hs = 0 := by
        change (StendhalAlgebra.violatedIdeal k param wt ν).ringCon.mk' _ = 0
        rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
        exact TwoSidedIdeal.subset_span ⟨s, hs, hv, rfl⟩
      rw [hzero, zero_mul, zero_mul]
    · obtain rfl := higher_than_middle s hs hv hle
      rw [← projected_loading param _ hs, ← mul_assoc,
        labelTwo_middleVector_annihilated_by_exterior param, zero_mul]

theorem labelTwoMiddleToExterior_unit :
    labelTwoMiddleToExterior param (leftStandardUnit param wt middleLoad middleRedOrdered) =
      middleReturnVector param := by
  apply leftStandardLift_unit
  apply Subtype.ext
  change seqIdem param wt middleLoad middleRedOrdered * (π (ψ 2 * e leftLoad) * P) = π (ψ 2 * e leftLoad) * P
  rw [← projected_loading param _ middleRedOrdered, ← mul_assoc, ← proj_mul, labelTwo_middleCut_ψ]

/-- The diagrammatic dot sum kills the middle return vector in the exterior
projective, so the middle-to-exterior map factors through the dot-sum quotient. -/
theorem labelTwoMiddleToExterior_dotSum :
    let X₃ : H' := x ⟨3, by decide⟩
    labelTwoMiddleToExterior param
      (π (X₁ + X₃) • leftStandardUnit param wt middleLoad middleRedOrdered) = 0 := by
  intro X₃
  rw [map_smul, labelTwoMiddleToExterior_unit]
  apply Subtype.ext
  change π (X₁ + X₃) * (π (ψ 2 * e leftLoad) * P) = 0
  rw [← mul_assoc, ← proj_mul]
  have h₁ : (X₁ * (ψ 2 * e leftLoad) : H') = ψ 2 * (X₁ * e leftLoad) := by
    rw [← mul_assoc, x_mul_ψ _ _ (by decide) (by decide), mul_assoc]
  have h₃ := dot_cross_right (Q := S) 2 (by decide : 3 < Multiset.card μ) leftLoad
  have hne : (leftLoad).lbl ⟨2, by decide⟩ ≠ (leftLoad).lbl ⟨3, by decide⟩ := by decide
  simp only [hne, ↓reduceIte, sub_mul, sub_eq_zero, mul_assoc] at h₃
  rw [add_mul, h₁, ← h₃, ← mul_add, ← add_mul, proj_mul,
    (labelTwo_leftExterior_dot_relations param).1, mul_zero, zero_mul]

local notation "M" => leftStandard param wt middleLoad middleRedOrdered
local notation "g" => leftStandardUnit param wt middleLoad middleRedOrdered

/-- The crossing map descends through the image of the diagrammatic dot-sum
endomorphism, which is determined by its value on the middle generator. -/
def labelTwoMiddleDotSumToExterior (dotSum : Module.End T M)
    (hsum : dotSum g = π (X₁ + x ⟨3, by decide⟩) • g) :
    (M ⧸ LinearMap.range dotSum) →ₗ[T] lIdeal (P) :=
  (LinearMap.range dotSum).liftQ (labelTwoMiddleToExterior param) <|
    LinearMap.range_le_ker_iff.mpr (by
      apply leftStandard_hom_ext middleLoad middleRedOrdered
      change labelTwoMiddleToExterior param (dotSum g) = 0
      rw [hsum]
      exact labelTwoMiddleToExterior_dotSum param)

/-- On a representative of the dot-sum quotient the descended map uses the
original middle-to-exterior crossing. -/
theorem labelTwoMiddleDotSumToExterior_mk (dotSum : Module.End T M)
    (hsum : dotSum g = π (X₁ + x ⟨3, by decide⟩) • g) (z : M) :
    labelTwoMiddleDotSumToExterior param dotSum hsum (Submodule.Quotient.mk z) =
      labelTwoMiddleToExterior param z := rfl

local notation "dotSumElt" => π (X₁ + x ⟨3, by decide⟩)

/-- The right dot sum on the middle standard, specified on its generator. -/
def labelTwoMiddleDotSumEnd : Module.End T M :=
  leftStandardLift middleLoad middleRedOrdered (dotSumElt • g) fun t ht z hlt => by
    rw [mul_smul]
    exact seqIdem_smul_leftStandard_eq_zero param wt middleRedOrdered ht hlt _

theorem labelTwoMiddleDotSumEnd_generator :
    labelTwoMiddleDotSumEnd param g = dotSumElt • g := by
  apply leftStandardLift_unit
  have hfixed : seqIdem param wt middleLoad middleRedOrdered • g = g := by
    rw [leftStandardUnit, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (seqIdem_mul_self param wt _ _)
  have hcomm : seqIdem param wt middleLoad middleRedOrdered * dotSumElt =
      dotSumElt * seqIdem param wt middleLoad middleRedOrdered := by
    rw [← projected_loading param _ middleRedOrdered, ← proj_mul, ← proj_mul]
    apply congrArg (π)
    rw [mul_add, add_mul, x_mul_e, x_mul_e]
  rw [← mul_smul, hcomm, mul_smul, hfixed]

/-- The actual middle dot-sum quotient maps to the left exterior divided
projective by the red-black crossing. -/
def labelTwoMiddleExteriorDifferential :
    (M ⧸ LinearMap.range (labelTwoMiddleDotSumEnd param)) →ₗ[T] lIdeal (P) :=
  labelTwoMiddleDotSumToExterior param (labelTwoMiddleDotSumEnd param)
    (labelTwoMiddleDotSumEnd_generator param)

end

end Categorification.Stendhal
