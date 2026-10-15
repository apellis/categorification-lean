/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.Completion
import Categorification.KLR.Unfurling.CompletedPolyRep

/-!
# Power series in the dots acting on the completed polynomial representation

In the proof of Lemma `lem:gamma-homo` (label) of Webster, *Unfurling Khovanov–Lauda–Rouquier
algebras*, arXiv:1603.06311v3 (§3.3 and the appendix of proofs), the graded completion of a
KLR algebra acts on the completed polynomial representation, and an element `F(x) e_i` given by
a power series `F` in the dots acts by projecting to the component `i` and multiplying by `F`.

Here the embedding `R(ν) → R̂(ν)` (`GradingDatum.toCompletion`) is identified with the series
`Unfurling.ser` of homogeneous components used by the completed action, and the action of
`GradingDatum.seriesAt hX i F = F(x) e_i` on the completion `decomp v` of a polynomial `v` is
computed: if `F · v_i` is (the power series of) a polynomial `w_i`, and `w` vanishes away from
the component `i`, then `F(x) e_i • decomp v = decomp w`. No homogeneity of the polynomials
`P a b` is needed, since only dots and idempotents occur.

## Main results

* `Unfurling.coe_toCompletion_eq_ser` : `toCompletion a = ser a` as Hahn series;
* `Unfurling.coeff_act_decomp` : the coefficients of `f • decomp v` as a finite sum;
* `Unfurling.act_seriesAt_decomp` : `F(x) e_i • decomp v = decomp w` for `w_i = F · v_i`.
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial PolyRep HahnSeries Finset KLRAlgebra

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  {G : GradingDatum Q} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- The embedding of `R(ν)` into its graded completion is the series of homogeneous
components `ser`. -/
theorem coe_toCompletion_eq_ser (a : KLRAlgebra k Q ν) :
    ((G.toCompletion a : G.completion ν) : HahnSeries ℤ (KLRAlgebra k Q ν)) = ser G a := by
  ext : 1; funext d
  rw [G.coeff_toCompletion, coeff_ser]

theorem act_sum {ι : Type*} (s : Finset ι) (f : HahnSeries ℤ (KLRAlgebra k Q ν))
    (v : ι → HahnSeries ℤ (Pol k ν)) :
    act hPQ f (∑ j ∈ s, v j) = ∑ j ∈ s, act hPQ f (v j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := act_add hPQ f 0 0
    rw [add_zero, left_eq_add] at this
    simpa using this
  | insert j s hj ih => rw [sum_insert hj, sum_insert hj, act_add, ih]

omit [DecidableEq I] in
theorem decomp_eq_sum (v : Pol k ν) :
    decomp G v = ∑ e ∈ degrees G v, single e (homPart G e v) := by
  conv_lhs => rw [← sum_homPart_degrees G v]
  rw [map_sum]
  exact sum_congr rfl fun e _ => decomp_of_mem G (homPart_mem G e v)

/-- The coefficients of `f • decomp v`, as a finite sum over the degrees of `v`. -/
theorem coeff_act_decomp (f : HahnSeries ℤ (KLRAlgebra k Q ν)) (v : Pol k ν) (n : ℤ) :
    (act hPQ f (decomp G v)).coeff n =
      ∑ e ∈ degrees G v, polyRep hPQ (f.coeff (n - e)) (homPart G e v) := by
  rw [decomp_eq_sum, act_sum, HahnSeries.coeff_sum]
  exact sum_congr rfl fun e _ => coeff_act_single hPQ f e _ n

omit [DecidableEq I] in
theorem coeff_eq_zero_of_notMem_degrees {v : Pol k ν} {i : Seq ν} {s : Fin m →₀ ℕ}
    (hs : Finsupp.weight (wt G i) s ∉ degrees G v) : (v i).coeff s = 0 := by
  by_contra h
  exact hs (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
    Finset.mem_image.2 ⟨s, mem_support_iff.2 h, rfl⟩⟩)

variable (hX : ∀ a, 0 < G.degX a)

/-- **Power series in the dots act by multiplication** (used in the proof of Webster,
arXiv:1603.06311v3, Lemma `lem:gamma-homo` (label)): if `F · v_i = w_i` as power series and
`w` vanishes away from the component `i`, then `F(x) e_i` sends the completion of `v` to the
completion of `w`. -/
theorem act_seriesAt_decomp (i : Seq ν) (F : MvPowerSeries (Fin m) k) {v w : Pol k ν}
    (hw : F * (v i : MvPowerSeries (Fin m) k) = (w i : MvPowerSeries (Fin m) k))
    (hw0 : ∀ i', i' ≠ i → w i' = 0) :
    act hPQ ((G.seriesAt hX i F : G.completion ν) : HahnSeries ℤ (KLRAlgebra k Q ν))
      (decomp G v) = decomp G w := by
  classical
  ext : 1; funext n; funext t
  rw [coeff_act_decomp, coeff_decomp, homPart_apply, Finset.sum_apply]
  simp_rw [GradingDatum.coeff_seriesAt, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_mul, polyRep_pol, polyRep_e, Module.End.mul_apply,
    Finset.sum_apply, Pi.smul_apply, opMul_apply, opE_apply]
  by_cases ht : t = i
  swap
  · simp [ht, hw0 t ht]
  subst ht
  simp only [ite_true]
  refine MvPolynomial.ext _ _ fun s => ?_
  rw [coeff_weightedHomogeneousComponent, ← MvPolynomial.coeff_coe (w t), ← hw,
    MvPowerSeries.coeff_mul]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, MvPolynomial.coeff_mul,
    MvPolynomial.coeff_monomial, homPart_apply, MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_coe, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun e _ => Finset.sum_comm, Finset.sum_comm, Finset.ite_sum_zero]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hs : Finsupp.weight (wt G t) s =
      Finsupp.weight (wt G t) x.1 + Finsupp.weight (wt G t) x.2 := by
    rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hx]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, GradingDatum.mem_weightFiber hX]
  by_cases h2 : Finsupp.weight (wt G t) x.2 ∈ degrees G v
  · rw [ite_eq_left h2]
    by_cases hn : Finsupp.weight (wt G t) s = n
    · rw [ite_eq_left hn, ite_eq_left (by change Finsupp.weight (wt G t) x.1 = _; omega)]
    · rw [ite_eq_right hn, ite_eq_right (by change ¬ Finsupp.weight (wt G t) x.1 = _; omega)]
  · rw [ite_eq_right h2, coeff_eq_zero_of_notMem_degrees h2, mul_zero, ite_self]

end Categorification.KLR.Unfurling
