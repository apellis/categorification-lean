/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicDottedTraceCoordinates

/-!
# Remainder formula for the opposite cap at any coroot weight

Brundan, arXiv:1501.00350v1, (1.15), (1.17), and Kang–Kashiwara,
arXiv:1102.4677v4, Theorem 5.2. Evaluating the dotted polynomial coordinate
with modulus `X^N A` recovers the actual cap whenever the shifted degree gap
is positive. At nonpositive weight it reads the first surviving dotted counit
of the normalized negative lift.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.CornerTrace

open Polynomial
variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (γ : Multiset I)
  (a : I → Polynomial k) (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = C c)
  (ha : ∀ j, (a j).Monic)
  {C₀ : QuantumGroup.CartanDatum I} {W Z : Type*} [AddCommGroup W] [AddCommGroup Z]
  (RD : QuantumGroup.UDot.WeightDatum C₀ W Z) (Λ : W)
  (hΛ : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) Λ)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
local notation "β" => ((Singleton.singleton i : Multiset I) + γ)
local notation "R" => CycKLR k Q a β
local notation "F" => aMonicL Q i β a
local notation "S" => sPoly (Q := Q) i β a
local notation "H" => zero_lt_card_single_add i γ
local notation "wt" => RD.pair (RD.iY i) (Λ - Multiset.sum (Multiset.map RD.iX β))
local notation "Amap" => aMap i β a (by simp) H hsym

include hsym hQ ha in
private theorem shiftedMonic (N : ℕ) : (X ^ N * F).Monic :=
  (monic_X_pow _).mul (monic_aMonicL i β a hsym (leadUnitAt_of i hQ) (ha i))

/-- Evaluate the dotted coordinate using the shifted modulus and the squared-difference polynomial. -/
def dottedTrace (N : ℕ) : EIKZero Q i β a →+ R where
  toFun z := MonicTrace.trace (X ^ N * F) (S * dottedCapPolynomial Q i γ a hsym N z)
  map_zero' := by simp only [map_zero, mul_zero, MonicTrace.trace, zero_modByMonic, coeff_zero]
  map_add' x y := by rw [map_add, mul_add, MonicTrace.trace_add _ (shiftedMonic Q i γ a hsym hQ ha N)]

local notation "tr" => dottedTrace Q i γ a hsym hQ ha
local notation "P" => dottedCapPolynomial Q i γ a hsym

include hsym hQ ha hΛ hdeg in
private theorem shiftedDegree [Nontrivial R] (N : ℕ) :
    ((X ^ N * F).natDegree : ℤ) - (S).natDegree = wt + N := by
  rw [(monic_X_pow N).natDegree_mul (monic_aMonicL i β a hsym (leadUnitAt_of i hQ) (ha i)),
    natDegree_X_pow, Nat.cast_add]
  have hd := aMonicL_degree_gap i β a RD Λ hsym hQ (ha i) hΛ hdeg
  omega

include hsym hQ ha hΛ hdeg in
private theorem relation_zero (N : ℕ) (hN : 0 < wt + N) (p : Polynomial R) :
    tr N (eiP Q i γ a (eiBSection Q i γ a p)) = 0 := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact Subsingleton.elim _ _
  have hd := shiftedDegree Q i γ a hsym hQ ha RD Λ hΛ hdeg N
  have hc (p : Polynomial R) : Commute p (X ^ N * F) :=
    (commute_X_pow p N).symm.mul_right (aMonicL_comm hsym i β a p)
  have hm := shiftedMonic Q i γ a hsym hQ ha N
  change MonicTrace.trace (X ^ N * F) (S * P N _) = 0
  rw [dottedCapPolynomial_relation]
  change MonicTrace.trace _ (S * (((-1 : k)^Multiset.card β) • Amap (p * X ^ N))) = 0
  rw [mul_smul_comm, smul_eq_mul_C_algebraMap, MonicTrace.trace_mul_C _ hm]
  suffices hz : MonicTrace.trace (X ^ N * F) (S * Amap (p * X ^ N)) = 0 by rw [hz, zero_mul]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_mul, map_add, mul_add, MonicTrace.trace_add _ hm, hp, hq, add_zero]
  | monomial d r =>
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add, ← X_pow_mul_C, aMap_mul_C,
      ← mul_assoc, MonicTrace.trace_mul_C _ hm, aMap_X_pow_eq_div i β a hsym H hQ ha (by simp),
      mul_smul_comm, smul_eq_mul_C_algebraMap, MonicTrace.trace_mul_C _ hm, pow_add, mul_assoc (X ^ d),
      weighted_quotient_trace_zero (X ^ N * F) S hm (sPoly_monic i β a) hc (by omega), zero_mul, zero_mul]

private theorem lowerProjected_eq (t : KZeroPrime Q i γ a) :
    middleCyclotomicProj Q i γ a (lowerF Q i γ a t) =
      cyclotomicSigma Q i γ a (lowerCyclotomicProj Q i γ a t) := by
  have h := cyclotomicSigma_lowerPCoker Q i γ a (Submodule.Quotient.mk t)
  exact h.symm

include hsym hQ ha hΛ hdeg in
private theorem trace_congr (N : ℕ) (hN : 0 < wt + N) {z u : EIKZero Q i β a}
    (hu : middleCyclotomicProj Q i γ a z = middleCyclotomicProj Q i γ a u) :
    tr N z = tr N u := by
  have hmem : z - u ∈ LinearMap.range (eiP Q i γ a) := by
    rw [← ker_middleCyclotomicProj, LinearMap.mem_ker, map_sub, hu, sub_self]
  obtain ⟨l, hl⟩ := hmem
  obtain ⟨⟨t,p⟩, rfl⟩ := (eiBSplitEquiv Q i γ a hsym).surjective l
  have hzero : P N (lowerF Q i γ a (lowerP Q i γ a t)) = 0 := by
    ext j
    rw [dottedCapPolynomial_crossing_coeff, lowerCyclotomicProj_lowerP, map_zero, ite_self, coeff_zero]
  have hf : tr N (lowerF Q i γ a (lowerP Q i γ a t)) = 0 := by
    change MonicTrace.trace _ (_ * P N _) = 0
    rw [hzero, mul_zero, MonicTrace.trace, zero_modByMonic, coeff_zero]
  rw [← sub_eq_zero, ← map_sub, ← hl, eiBSplitEquiv_apply, map_add, ← lowerP_tensor_square,
    map_add, hf, relation_zero Q i γ a hsym hQ ha RD Λ hΛ hdeg N hN, add_zero]

include hsym hQ ha hΛ hdeg in
private theorem trace_of_small (N : ℕ) (hN : 0 < wt + N) (z : EIKZero Q i β a)
    (hz : ∀ j, (wt + N).toNat ≤ j → (P N z).coeff j = 0) :
    tr N z = (P N z).coeff ((wt + N).toNat - 1) := by
  rcases subsingleton_or_nontrivial R with hs | hn
  · exact Subsingleton.elim _ _
  have hd := shiftedDegree Q i γ a hsym hQ ha RD Λ hΛ hdeg N
  have he : (X ^ N * F).natDegree - (S).natDegree = (wt + N).toNat := by omega
  change MonicTrace.trace _ _ = _
  rw [← he]
  apply weighted_small_trace _ _ (shiftedMonic Q i γ a hsym hQ ha N) (sPoly_monic i β a) (by omega)
  rw [he, degree_lt_iff_coeff_zero]
  exact hz

private theorem lowerProj_surjective : Function.Surjective (lowerCyclotomicProj Q i γ a) := by
  intro l
  obtain ⟨u, rfl⟩ := (lowerPCokerEquiv Q i γ a).surjective l
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact ⟨t, rfl⟩

include hΛ hdeg in
private theorem trace_positive_representative (N : ℕ) (hw : 0 < wt) (z : EIKZero Q i β a) :
    tr N z = positive Q i γ a hsym hQ ha RD Λ hΛ hdeg hw (middleCyclotomicProj Q i γ a z) := by
  have hN : 0 < wt + N := by omega
  obtain ⟨⟨l,r⟩, he⟩ := (cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hw.le).surjective
    (middleCyclotomicProj Q i γ a z)
  obtain ⟨t, rfl⟩ := lowerProj_surjective Q i γ a l
  have he' : middleCyclotomicProj Q i γ a (lowerF Q i γ a t + eiCSection Q i γ a r) =
      middleCyclotomicProj Q i γ a z := by
    rw [map_add, lowerProjected_eq]
    exact he
  rw [← trace_congr Q i γ a hsym hQ ha RD Λ hΛ hdeg N hN he',
    ← he', trace_of_small Q i γ a hsym hQ ha RD Λ hΛ hdeg N hN _]
  · have hv := cyclotomicCommutator_inverse_representative Q i γ a hsym hQ ha RD Λ hΛ hdeg hw.le t r
    change _ = (cyclotomicCorrectionEquiv Q i γ a (wt).toNat
      ((cyclotomicCommutatorEquiv Q i γ a hsym hQ ha RD Λ hΛ hdeg hw.le).symm _).2) _
    rw [hv, map_add, coeff_add, dottedCapPolynomial_crossing_coeff, dottedCapPolynomial_section,
      ite_eq_right (by omega), zero_add,
      show (wt + N).toNat - 1 = ((wt).toNat - 1) + N by omega, coeff_mul_X_pow]
    rfl
  · intro j hj
    rw [map_add, coeff_add, dottedCapPolynomial_crossing_coeff, dottedCapPolynomial_section,
      ite_eq_right (by omega), zero_add,
      show j = (j - N) + N by omega, coeff_mul_X_pow]
    exact (degree_lt_iff_coeff_zero _ _).mp (Polynomial.mem_degreeLT.mp r.2) _ (by omega)

include hΛ hdeg in
private theorem trace_nonpositive_representative (N : ℕ) (hw : wt ≤ 0) (hN : 0 < wt + N)
    (z : EIKZero Q i β a) :
    tr N z = nonpositive Q i γ a hsym hQ ha RD Λ hΛ hdeg hw (middleCyclotomicProj Q i γ a z) := by
  let m := middleCyclotomicProj Q i γ a z
  let l := negativeLift Q i γ a hsym hQ ha RD Λ hΛ hdeg hw m
  obtain ⟨t, ht⟩ := lowerProj_surjective Q i γ a l
  obtain ⟨hs, hc⟩ := negativeLift_spec Q i γ a hsym hQ ha RD Λ hΛ hdeg hw m
  have he : middleCyclotomicProj Q i γ a (lowerF Q i γ a t) = m := by rw [lowerProjected_eq, ht]; exact hs
  rw [← trace_congr Q i γ a hsym hQ ha RD Λ hΛ hdeg N hN he,
    trace_of_small Q i γ a hsym hQ ha RD Λ hΛ hdeg N hN _]
  · rw [dottedCapPolynomial_crossing_coeff, ite_eq_left (by omega), ht,
      show N - 1 - ((wt + N).toNat - 1) = (-wt).toNat by omega]
    rfl
  · intro j hj
    rw [dottedCapPolynomial_crossing_coeff]
    split_ifs with hj'
    · rw [ht]
      exact hc ⟨N - 1 - j, by omega⟩
    · rfl

/-- The opposite cap in Brundan (1.15), (1.17) is the weighted remainder of the
`N`-dotted polynomial coordinate for every shift making the degree gap positive.
The nonpositive branch uses the normalized negative lift and its dotted counits. -/
theorem trace_eq_dotted (N : ℕ) (hN : 0 < wt + N) (z : EIKZero Q i β a) :
    trace Q i γ a hsym hQ ha RD Λ hΛ hdeg (middleCyclotomicProj Q i γ a z) =
      MonicTrace.trace (X ^ N * F) (S * P N z) := by
  change _ = tr N z
  unfold trace
  split_ifs with hw
  · exact (trace_positive_representative Q i γ a hsym hQ ha RD Λ hΛ hdeg N hw z).symm
  · exact (trace_nonpositive_representative Q i γ a hsym hQ ha RD Λ hΛ hdeg N (le_of_not_gt hw) hN z).symm

end Categorification.KLR.KLRAlgebra.CornerTrace
