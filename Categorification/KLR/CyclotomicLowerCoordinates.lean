/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicLowerCrossing
import Categorification.KLR.CyclotomicPsi

/-!
# Multiplication and the existing cyclotomic coordinates

Comparison of the actual maps `F(x ⊗ y) = x τ_n y` and `E(x ⊗ y) = xy`
with the free coordinates in Kang–Kashiwara, arXiv:1102.4677v4, §5.2.
This is a compatibility statement, not a proof that the lower-rank tensor
exhausts the coordinate kernel, nor the subsequent snake comparison.
-/
noncomputable section
namespace Categorification.KLR.KLRAlgebra
open scoped TensorProduct
variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Rb" => KLRAlgebra k Q β
local notation "L" => CornerTensor.Left (lowerLast Q i γ)

private theorem doubleLast_eqIdem :
    cL Q i β (cL Q i γ 1) * eqIdem (Multiset.card γ) (by simp) =
      cL Q i β (cL Q i γ 1) := by
  rw [← sum_e (k := k) (Q := Q) (ν := γ)]
  change ((cLLinear (Q := Q) i β).comp (cLLinear i γ)) (∑ s : Seq γ, e s) * _ =
    ((cLLinear (Q := Q) i β).comp (cLLinear i γ)) (∑ s : Seq γ, e s)
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  change cL Q i β (cL Q i γ (e s)) * _ = cL Q i β (cL Q i γ (e s))
  rw [cL_e, cL_e]
  have ht : (Seq.cast (add_comm β Si) ((Seq.cast (add_comm γ Si) (s.append default)).append default)).1
      ⟨Multiset.card γ, by simp⟩ =
    (Seq.cast (add_comm β Si) ((Seq.cast (add_comm γ Si) (s.append default)).append default)).1
      ⟨Multiset.card γ + 1, by simp⟩ := by
    simp only [Seq.cast_apply]
    rw [Seq.append_apply_lt _ _ _ (by change Multiset.card γ < Multiset.card β; simp), Seq.cast_apply,
      Seq.append_apply_ge _ _ _ (by change Multiset.card γ ≤ Multiset.card γ; rfl),
      Seq.append_apply_ge _ _ _ (by change Multiset.card β ≤ Multiset.card γ + 1; simp)]
    exact (Multiset.mem_singleton.1 (Seq.mem _ _)).trans
      (Multiset.mem_singleton.1 (Seq.mem _ _)).symm
  generalize Seq.cast (add_comm β Si) ((Seq.cast (add_comm γ Si) (s.append default)).append default) = t at ht ⊢
  rw [eqIdem, Finset.mul_sum, Finset.sum_eq_single t]
  · rw [ite_eq_left ht, e_mul_self]
  · intro v _ hv
    split_ifs
    · rw [e_mul_e, ite_eq_right (Ne.symm hv)]
    · exact mul_zero _
  · intro h
    exact (h (Finset.mem_univ t)).elim

private theorem lowerLeft_eqIdem (u : L) :
    cL Q i β (u : Rb) * eqIdem (Multiset.card γ) (by simp) = cL Q i β (u : Rb) := by
  have hu : (u : Rb) * cL Q i γ 1 = u := CornerTensor.left_mem (lowerLast Q i γ) u
  have hcut : cL Q i β (u : Rb) * cL Q i β (cL Q i γ 1) = cL Q i β (u : Rb) := by
    rw [← cL_mul, hu]
  calc
    _ = (cL Q i β (u : Rb) * cL Q i β (cL Q i γ 1)) * _ := by rw [hcut]
    _ = cL Q i β (u : Rb) := by rw [mul_assoc, doubleLast_eqIdem, hcut]

/-- The source's equal-colour dot-slide, on representatives of the genuine tensor. -/
theorem lower_crossing_last_dot (u : L) (b : Rb) :
    (cL Q i β (u : Rb) * -ψ (Multiset.card γ) * cL Q i β b) *
      x ⟨Multiset.card β, lastPos_lt i β⟩ =
    cL Q i β ((u : Rb) * x ⟨Multiset.card γ, by simp⟩) * -ψ (Multiset.card γ) * cL Q i β b +
      cL Q i β ((u : Rb) * b) := by
  let xp : R := x ⟨Multiset.card γ, by simp⟩
  let xl : R := x ⟨Multiset.card β, lastPos_lt i β⟩
  have hd : xp * ψ (Multiset.card γ) = ψ (Multiset.card γ) * xl +
      eqIdem (Multiset.card γ) (by simp) := by
    simpa only [xp, xl, Multiset.card_add, Multiset.card_singleton, add_comm 1] using
      x_mul_ψ_self (Q := Q) (ν := Si + β) (Multiset.card γ) (by simp)
  have hp : cL Q i β ((u : Rb) * x ⟨Multiset.card γ, by simp⟩) = cL Q i β (u : Rb) * xp := by
    rw [cL_mul, cL_x]
    change cL Q i β (u : Rb) * (xp * cL Q i β 1) = _
    have hc : xp * cL Q i β 1 = cL Q i β 1 * xp := by
      rw [cL_one, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun s _ => x_mul_e _ _)
    rw [hc, ← mul_assoc, ← cL_mul, mul_one]
  have he := lowerLeft_eqIdem Q i γ u
  have hc := (commute_x_last_cL (Q := Q) i β b).eq
  rw [hp, cL_mul]
  change (cL Q i β (u : Rb) * -ψ (Multiset.card γ) * cL Q i β b) * xl = _
  calc
    _ = cL Q i β (u : Rb) * -(ψ (Multiset.card γ) * xl) * cL Q i β b := by
      rw [mul_assoc _ _ xl, ← hc]
      simp only [xl, mul_assoc, neg_mul, mul_neg]
    _ = _ := by rw [eq_sub_iff_add_eq.mpr hd.symm]; noncomm_ring [he]

variable (a : I → Polynomial k)
  (hsym : KLRSymm Q)
local notation "Rl" => CycKLR k Q a β

/-- The constant coordinate of the last dot on the genuine crossing is multiplication. -/
theorem cMap_lastDot_lowerF (t : KZeroPrime Q i γ a) :
    cMap i β hsym a (zero_lt_card_single_add i γ)
      (lastDot0 i β a (lowerFCoordinates Q i γ a t)) = Polynomial.C (lowerE Q i γ a t) := by
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul u y =>
    obtain ⟨b, hb⟩ := CycKLR.mk_surjective (y : Rl)
    rw [lowerFCoordinates_tmul Q i γ a u y b hb.symm, lastDot0_mk, lower_crossing_last_dot,
      Submodule.Quotient.mk_add, map_add]
    have hn : Multiset.card β - 1 = Multiset.card γ := by simp
    have hz := cMap_cL_crossing i β (zero_lt_card_single_add i γ) hsym a
      ((u : Rb) * x ⟨Multiset.card γ, by simp⟩) b
    rw [hn] at hz
    rw [mul_neg, neg_mul, Submodule.Quotient.mk_neg, map_neg, hz, neg_zero, zero_add,
      cMap_mk, cPoly_cL, lowerE_tmul, ← hb, ← map_mul]

/-- Existing `F` coordinates reconstruct the genuine crossing map exactly. This does not
assert that every free coordinate belongs to the lower-rank source. -/
theorem fSection_lowerF (t : KZeroPrime Q i γ a) :
    fSection i β a (zero_lt_card_single_add i γ)
      (fCoords i β a hsym (zero_lt_card_single_add i γ) (lowerFCoordinates Q i γ a t)) =
      lowerFCoordinates Q i γ a t := by
  have h := fSection_add_cSection i β a hsym (zero_lt_card_single_add i γ)
    (lowerFCoordinates Q i γ a t)
  rw [cMap_lowerF, map_zero, add_zero] at h
  rw [h]
  clear h
  induction t using BalancedTensor.induction_on with
  | zero => simp only [map_zero]
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul u y =>
    obtain ⟨b, hb⟩ := CycKLR.mk_surjective (y : Rl)
    rw [lowerFCoordinates_tmul Q i γ a u y b hb.symm, act0_mk,
      mul_assoc _ (cL Q i β b), ← cL_mul, mul_one]

/-- The source's actual multiplication map agrees with the previously defined constant-error
coordinate on the actual crossing image, with `ψ = -τ` already incorporated in `lowerF`. -/
theorem eCoords_lowerF (t : KZeroPrime Q i γ a) :
    eCoords i β a hsym (zero_lt_card_single_add i γ)
      (fCoords i β a hsym (zero_lt_card_single_add i γ) (lowerFCoordinates Q i γ a t)) =
      lowerE Q i γ a t := by
  change (cMap i β hsym a (zero_lt_card_single_add i γ)
    (lastDot0 i β a (fSection i β a (zero_lt_card_single_add i γ) _))).coeff 0 = _
  rw [fSection_lowerF, cMap_lastDot_lowerF, Polynomial.coeff_C_zero]

end Categorification.KLR.KLRAlgebra
