/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CyclotomicRedSingleton
import Categorification.WeightedKLR.RedStrands.CyclotomicRedTracePolynomial
import Categorification.KLR.CyclotomicCornerTracePolynomial

/-!
# Trace adjoints of the singleton red crossings

Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25. On the vacuum induction edge,
the crossing that multiplies a lift by the new dot power is adjoint to
the cyclotomic quotient for the two Frobenius traces.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra Polynomial PolynomialTrace

/-- Multiplying the modulus and its argument by the same power of X preserves
the leading remainder coefficient used in Webster's red crossing calculation. -/
theorem redTrace_mul_X_pow {R : Type*} [Ring R] (f : R[X]) (hf : f.Monic) (d : ℕ) (p : R[X]) :
    MonicTrace.trace (X ^ d * f) (X ^ d * p) = MonicTrace.trace f p := by
  nontriviality R
  have hm : (X ^ d * f).Monic := (monic_X_pow _).mul hf
  have hr : (X ^ d * p) %ₘ (X ^ d * f) = X ^ d * (p %ₘ f) := by
    apply (div_modByMonic_unique (p /ₘ f) _ hm ?_).2
    constructor
    · rw [mul_assoc, ← mul_add, modByMonic_add_div]
    · rw [(commute_X_pow (p %ₘ f) d).eq, (commute_X_pow f d).eq,
        degree_mul_X_pow, degree_mul_X_pow]
      exact WithBot.add_lt_add_right (by simp) (degree_modByMonic_lt _ hf)
  unfold MonicTrace.trace
  rw [hr, (monic_X_pow d).natDegree_mul hf, natDegree_X_pow]
  by_cases h : f.natDegree = 0
  · have he : f = 1 := eq_one_of_monic_natDegree_zero hf h
    simp [he]
  · rw [show d + f.natDegree - 1 = (f.natDegree - 1) + d by omega, coeff_X_pow_mul]

/-- Monic remainder traces commute with change of coefficient ring. -/
theorem redTrace_map {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) (p f : R[X]) (hf : f.Monic) :
    φ (MonicTrace.trace f p) = MonicTrace.trace (f.map φ) (p.map φ) := by
  nontriviality S
  rw [MonicTrace.trace, MonicTrace.trace, ← map_modByMonic φ hf, coeff_map, hf.natDegree_map]

variable {I k : Type*} [DecidableEq I] [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (i : I) (n d : I → ℕ)

local notation "lo" => (fun j => (X ^ n j : Polynomial k))
local notation "hi" => (fun j => (X ^ (n j + d j) : Polynomial k))

/-- On the singleton block the quotient crossing and the reverse red crossing
are adjoint for the monic cyclotomic trace forms (Webster, §4.5, Theorem 4.25). -/
theorem singletonRedCrossing_trace (r : CycKLR k Q hi {i}) (z : CycKLR k Q lo {i}) :
    PolynomialTrace.trace Q i hi (monic_X_pow _) (r * singletonRedDotCrossing Q i n d z) =
      PolynomialTrace.trace Q i lo (monic_X_pow _)
        (cyclotomicRedProjection Q (redPower_dvd (k := k) n d) {i} r * z) := by
  rw [← singletonRedDotCrossing_mul]
  obtain ⟨p, hp⟩ := eval_surjective Q i lo
    (cyclotomicRedProjection Q (redPower_dvd (k := k) n d) {i} r * z)
  rw [← hp, singletonRedDotCrossing_eval, trace_eval, trace_eval]
  rw [add_comm (n i) (d i), pow_add]
  exact redTrace_mul_X_pow _ (monic_X_pow _) _ _

section Relative

variable {a b : I → Polynomial k} (hab : ∀ j, a j ∣ b j) (e : ℕ) (hfactor : b i = X ^ e * a i)
  (hsym : KLRSymm Q)
  (hQ : ∀ j l : I, j ≠ l → ∃ c : k, IsUnit c ∧ (polyInY (Q j l)).leadingCoeff = C c)
  (ha : ∀ j, (a j).Monic) (hb : ∀ j, (b j).Monic)

include hfactor hsym hQ ha hb in
/-- Change of highest weight for the relative remainder trace, including the squared
difference factor of Kang–Kashiwara §5.2. -/
theorem redProjection_weighted_trace (β : Multiset I) (p : Polynomial (CycKLR k Q b β)) :
    cyclotomicRedProjection Q hab β
      (RelativePolynomialTrace.trace i β b (sPoly (Q := Q) i β b * (X ^ e * p))) =
      RelativePolynomialTrace.trace i β a
        (sPoly (Q := Q) i β a * p.map (cyclotomicRedProjection Q hab β).toRingHom) := by
  let π := (cyclotomicRedProjection Q hab β).toRingHom
  unfold RelativePolynomialTrace.trace
  change π _ = _
  rw [redTrace_map π _ _ (monic_aMonicL i β b hsym hQ (hb i)),
    cyclotomicRedProjection_aMonicL Q hab i β e hfactor, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, cyclotomicRedProjection_sPoly, ← mul_assoc,
    ← (commute_X_pow (sPoly (Q := Q) i β a) e).eq, mul_assoc,
    redTrace_mul_X_pow _ (monic_aMonicL i β a hsym hQ (ha i))]

variable (γ : Multiset I)
  {C : QuantumGroup.CartanDatum I} {X' Y : Type*} [AddCommGroup X'] [AddCommGroup Y]
  (RD : QuantumGroup.UDot.WeightDatum C X' Y) (lower upper : X')
  (hl : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) lower)
  (hu : ((b i).natDegree : ℤ) = RD.pair (RD.iY i) upper)
  (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))

local notation "β" => (Singleton.singleton i + γ)

include hfactor in
/-- Webster, §4.5, Theorem 4.25, opposite-cap trace comparison on the polynomial part
of a present-colour corner where both coroot weights are positive. -/
theorem redProjection_positive_polynomial
    (wl : 0 < RD.pair (RD.iY i) (lower - ((β).map RD.iX).sum))
    (wu : 0 < RD.pair (RD.iY i) (upper - ((β).map RD.iX).sum))
    (p : Polynomial (CycKLR k Q b β)) :
    cyclotomicRedProjection Q hab β
      (CornerTrace.positive Q i γ b hsym hQ hb RD upper hu hdeg wu
        (cyclotomicDotUnit Q i γ b (X ^ e * p))) =
    CornerTrace.positive Q i γ a hsym hQ ha RD lower hl hdeg wl
      (cyclotomicDotUnit Q i γ a (p.map (cyclotomicRedProjection Q hab β).toRingHom)) := by
  rw [CornerTrace.positive_polynomial, CornerTrace.positive_polynomial]
  exact redProjection_weighted_trace Q i hab e hfactor hsym hQ ha hb β p

end Relative

end Categorification.Stendhal
