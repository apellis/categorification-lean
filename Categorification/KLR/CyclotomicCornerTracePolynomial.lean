/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicCornerTrace
import Categorification.KLR.CyclotomicRelativePolynomialTrace

/-!
# Polynomial formula for the positive-weight whole-corner trace

The essential factor is the actual polynomial `sPoly`: on a polynomial
representative `p`, the positive corner trace is the `aMonicL` remainder
trace of `sPoly * p`. The unweighted polynomial trace is not substituted for
this expression. The formula kills the actual horizontal relation `eiA`
and the entire crossing summand, so it is independent of every representative.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.CornerTrace
open Polynomial

private theorem weighted_quotient_trace_zero {R : Type*} [Ring R]
    (f s : Polynomial R) (hf : f.Monic) (hs : s.Monic)
    (hc : ∀ p, Commute p f) (hd : s.natDegree < f.natDegree) (p : Polynomial R) :
    MonicTrace.trace f (s * ((p * f) /ₘ s)) = 0 := by
  nontriviality R
  have he : (s * ((p * f) /ₘ s)) %ₘ f = (-(p * f %ₘ s)) %ₘ f := by
    apply MonicTrace.remainder_eq_of_sub f hf
    refine ⟨p, ?_⟩
    have h := modByMonic_add_div (p * f) s
    rw [sub_neg_eq_add, add_comm, h, (hc p).eq]
  have hr : (-(p * f %ₘ s)).degree < f.degree := by
    rw [degree_neg, degree_eq_natDegree hf.ne_zero]
    exact (degree_modByMonic_lt _ hs).trans (by
      rw [degree_eq_natDegree hs.ne_zero]
      exact_mod_cast hd)
  unfold MonicTrace.trace
  rw [he, (modByMonic_eq_self_iff hf).2 hr, coeff_neg]
  have hz : (p * f %ₘ s).coeff (f.natDegree - 1) = 0 :=
    coeff_eq_zero_of_degree_lt ((degree_modByMonic_lt _ hs).trans_le (by
      rw [degree_eq_natDegree hs.ne_zero]
      exact_mod_cast (show s.natDegree ≤ f.natDegree - 1 by omega)))
  rw [hz, neg_zero]

private theorem weighted_small_trace {R : Type*} [Ring R]
    (f s : Polynomial R) (hf : f.Monic) (hs : s.Monic)
    (hd : s.natDegree < f.natDegree) (p : Polynomial R)
    (hp : p.degree < (f.natDegree - s.natDegree : ℕ)) :
    MonicTrace.trace f (s * p) = p.coeff (f.natDegree - s.natDegree - 1) := by
  nontriviality R
  have hp' : p.natDegree ≤ f.natDegree - s.natDegree - 1 := by
    by_cases hz : p = 0
    · subst p; simp
    · rw [degree_eq_natDegree hz] at hp
      have hp0 : p.natDegree < f.natDegree - s.natDegree := by exact_mod_cast hp
      omega
  have he : f.natDegree - 1 = s.natDegree + (f.natDegree - s.natDegree - 1) := by omega
  have hr : (s * p).degree < f.degree := by
    rw [degree_eq_natDegree hf.ne_zero]
    apply (degree_mul_le _ _).trans_lt
    apply lt_of_le_of_lt (add_le_add (degree_le_natDegree (p := s)) (degree_le_natDegree (p := p)))
    rw [← Nat.cast_add]
    exact_mod_cast (show s.natDegree + p.natDegree < f.natDegree by omega)
  unfold MonicTrace.trace
  rw [(modByMonic_eq_self_iff hf).2 hr, he,
    coeff_mul_add_eq_of_natDegree_le le_rfl hp', hs.coeff_natDegree, one_mul]

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
  (a : I → Polynomial k)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β" => (Si + γ)
local notation "R" => CycKLR k Q a β
local notation "F" => aMonicL Q i β a
local notation "S" => sPoly (Q := Q) i β a
variable (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = Polynomial.C c)
  (ha : ∀ j, (a j).Monic)
  {C : QuantumGroup.CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X Y) (Λ : X)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) =
    -RD.pair (RD.iY i) (RD.iX j))
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))
local notation "Amap" => aMap i β a (by simp) (zero_lt_card_single_add i γ) hsym
local notation "trP" => positive Q i γ a hsym hQ ha RD Λ hΛ hdeg

include hQ ha hΛ hdeg

/-- Multiplication by `sPoly` is essential for annihilating the actual polynomial relation. -/
theorem weighted_trace_aMap (hw : 0 < wt) (p : Polynomial R) :
    MonicTrace.trace F (S * Amap p) = 0 := by
  rcases subsingleton_or_nontrivial (CycKLR k Q a (Si + γ)) with h | h
  · exact Subsingleton.elim _ _
  have hf := monic_aMonicL (Q := Q) i β a hsym hQ (ha i)
  have hc := aMonicL_comm hsym i β a
  have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, mul_add, MonicTrace.trace_add _ hf, hp, hq, add_zero]
  | monomial d r =>
    rw [← C_mul_X_pow_eq_monomial, ← X_pow_mul_C, aMap_mul_C,
      ← mul_assoc, MonicTrace.trace_mul_C _ hf]
    rw [aMap_X_pow_eq_div i β a hsym (zero_lt_card_single_add i γ) hQ ha (by simp)]
    rw [mul_smul_comm, smul_eq_mul_C_algebraMap, MonicTrace.trace_mul_C _ hf]
    rw [weighted_quotient_trace_zero F S hf (sPoly_monic i β a) hc (by omega), zero_mul, zero_mul]

/-- The signed actual relation is killed as well. -/
theorem weighted_trace_eiA (hw : 0 < wt) (p : Polynomial R) :
    MonicTrace.trace F (S * eiA Q i γ a hsym p) = 0 := by
  have hf := monic_aMonicL (Q := Q) i β a hsym hQ (ha i)
  change MonicTrace.trace F (S * (((-1 : k)^Multiset.card β) • Amap p)) = 0
  rw [mul_smul_comm, smul_eq_mul_C_algebraMap, MonicTrace.trace_mul_C _ hf,
    weighted_trace_aMap Q i γ a hsym hQ ha RD Λ hΛ hdeg hw, zero_mul]

/-- The actual positive inverse on any middle representative has a weighted polynomial formula. -/
theorem positive_representative (hw : 0 < wt) (z : EIKZero Q i β a) :
    trP hw (middleCyclotomicProj Q i γ a z) =
      RelativePolynomialTrace.trace i β a (S * eiC Q i γ a hsym z) := by
  rcases subsingleton_or_nontrivial (CycKLR k Q a (Si + γ)) with h | h
  · exact Subsingleton.elim _ _
  have hf := monic_aMonicL (Q := Q) i β a hsym hQ (ha i)
  have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
  obtain ⟨p,hp⟩ := eiA_exists_small_remainder Q i γ a hsym hQ ha RD Λ hΛ hdeg hw.le
    (eiC Q i γ a hsym z)
  have he := cyclotomicCommutator_inverse_remainder Q i γ a hsym hQ ha RD Λ hΛ hdeg hw.le z p hp
  change (((cyclotomicCommutatorFinEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hw.le).symm
    (middleCyclotomicProj Q i γ a z)).2 _) = _
  change (((cyclotomicCorrectionEquiv Q i γ a (wt).toNat)
    ((cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hw.le).symm
      (middleCyclotomicProj Q i γ a z)).2) _) = _
  rw [he]
  change (eiC Q i γ a hsym z - eiA Q i γ a hsym p).coeff ((wt).toNat - 1) = _
  have hgap : (F).natDegree - (S).natDegree = (wt).toNat := by omega
  have hs := weighted_small_trace F S hf (sPoly_monic i β a) (by omega)
    (eiC Q i γ a hsym z - eiA Q i γ a hsym p) (by simpa only [hgap] using hp)
  rw [hgap] at hs
  rw [← hs]
  change MonicTrace.trace F (S * _) = MonicTrace.trace F (S * _)
  have ht := MonicTrace.trace_add F hf
    (S * (eiC Q i γ a hsym z - eiA Q i γ a hsym p))
    (S * eiA Q i γ a hsym p)
  rw [← mul_add, sub_add_cancel,
    weighted_trace_eiA Q i γ a hsym hQ ha RD Λ hΛ hdeg hw, add_zero] at ht
  exact ht.symm

/-- In particular the polynomial inclusion uses the weighted, not unweighted, trace. -/
theorem positive_polynomial (hw : 0 < wt) (p : Polynomial R) :
    trP hw (cyclotomicDotUnit Q i γ a p) =
      RelativePolynomialTrace.trace i β a (S * p) := by
  rw [cyclotomicDotUnit, LinearMap.comp_apply, positive_representative,
    eiC_eiCSection]

end Categorification.KLR.KLRAlgebra.CornerTrace
