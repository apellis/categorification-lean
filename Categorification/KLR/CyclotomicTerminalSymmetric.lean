/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicTerminal
import Categorification.KLR.CyclotomicFinite
import Categorification.Algebra.NilHeckeSplitting

/-!
# Symmetric relations in a saturated single-colour cyclotomic block

Webster, arXiv:1309.3796v2, Proposition 7.2. The cyclotomic relation in the
saturated single-colour block implies the positive elementary symmetric
relations. The polynomial kernel is stable under divided differences.
The dual pairing on powers of the last variable extracts the coefficients
of its monic symmetric relation.
-/

namespace Categorification.KLR.CycKLR

open KLRAlgebra Categorification.NilHecke Polynomial MvPolynomial

section Polynomial

variable {k B : Type*} [CommRing k] [Ring B]

private theorem terminal_coefficients (n : ℕ)
    (F : MvPolynomial (Fin (n + 1)) k →+* B)
    (hdd : ∀ j p, F p = 0 → F (dd k (n + 1) j p) = 0)
    (hpow : F ((X (Fin.last n)) ^ (n + 1)) = 0)
    (r : ℕ) (hr : 0 < r) (hrn : r ≤ n + 1) :
    F (esymm (Fin (n + 1)) k r) = 0 := by
  let y : MvPolynomial (Fin (n + 1)) k := X (Fin.last n)
  let i := n + 1 - r
  have hi : i ≤ n := by dsimp [i]; omega
  have hddw (w : List ℕ) (p : MvPolynomial (Fin (n + 1)) k) (hp : F p = 0) :
      F (ddw w p) = 0 := by
    induction w with
    | nil => simpa using hp
    | cons j w ih =>
      rw [ddw_cons, Module.End.mul_apply]
      exact hdd j _ ih
  let L : Module.End k (MvPolynomial (Fin (n + 1)) k) :=
    nhPair k n * mulPoly k (n + 1) (nhDual k n i)
  have hL (p : MvPolynomial (Fin (n + 1)) k) (hp : F p = 0) : F (L p) = 0 := by
    change F (nhPair k n (nhDual k n i * p)) = 0
    rw [nhPair_apply]
    exact hddw _ _ (by rw [map_mul, map_mul, hp, mul_zero, mul_zero])
  have hv := congrArg (Polynomial.eval (-y)) (prod_C_add_X_eq_sum_esymm k (Fin (n + 1)))
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at hv
  rw [Finset.prod_eq_zero (Finset.mem_univ (Fin.last n)) (by simp [y]),
    Finset.sum_range_succ', esymm_zero, one_mul, Nat.sub_zero] at hv
  have hneg : F ((-y) ^ (n + 1)) = 0 := by
    rw [neg_pow, map_mul, hpow, mul_zero]
  have hsum := congrArg (fun p => F (L p)) hv
  simp only [map_zero, map_add, map_sum, hL _ hneg, add_zero] at hsum
  have term (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      L (esymm (Fin (n + 1)) k (j + 1) * (-y) ^ (n + 1 - (j + 1))) =
        if j + 1 = r then
          (-1) ^ i * esymm (Fin (n + 1)) k r else 0 := by
    have hjn := Finset.mem_range.mp hj
    let d := n + 1 - (j + 1)
    have hd : d ≤ n := by dsimp [d]; omega
    let c : MvPolynomial (Fin (n + 1)) k := (-1)^d * esymm (Fin (n + 1)) k (j+1)
    have hc : c ∈ adjInv k (n + 1) (n + 1) := by
      apply Subalgebra.mul_mem
      · exact Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _
      · exact mem_adjInv_of_isSymmetric (esymm_isSymmetric _ _ _)
    change nhPair k n (nhDual k n i * (esymm (Fin (n + 1)) k (j+1) * (-y)^d)) = _
    rw [show nhDual k n i * (esymm (Fin (n + 1)) k (j+1) * (-y)^d) =
        c * (nhDual k n i * y^d) by rw [neg_pow]; dsimp [c]; ring,
      nhPair_mul_of_mem hc, nhPair_nhDual_mul_pow hi hd]
    by_cases he : j+1=r
    · have hdi : d = i := by dsimp [d, i]; omega
      simp [he, hdi, c]
    · have hdi : i ≠ d := by dsimp [d, i]; omega
      simp [he, hdi]
  rw [Finset.sum_congr rfl (fun j hj => congrArg F (term j hj)),
    Finset.sum_eq_single (r-1)] at hsum
  · rw [show r - 1 + 1 = r by omega, ite_eq_left rfl] at hsum
    rcases neg_one_pow_eq_or (MvPolynomial (Fin (n + 1)) k) i with h | h
    · rwa [h, one_mul, eq_comm] at hsum
    · rwa [h, neg_one_mul, map_neg, eq_comm, neg_eq_zero] at hsum
  · intro j _ hj
    rw [ite_eq_right (by omega), map_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

end Polynomial
section Cyclotomic

variable {I k : Type*} [DecidableEq I] [Field k] {ν : Multiset I} {i : I}
  (same : ∀ j ∈ ν, j = i) (Q : I → I → MvPolynomial (Fin 2) k)

local notation "n" => Multiset.card ν
local notation "powers" => fun _ : I => (Polynomial.X ^ n : Polynomial k)
local notation "π" => CycKLR.mk k Q powers ν
local notation "R" => CycKLR k Q powers ν

include same in
/-- The positive elementary symmetric polynomials of the black dots vanish
in the saturated one-colour cyclotomic block. -/
theorem terminal_pol_esymm_eq_zero (r : ℕ) (hr : 0 < r) (hrn : r ≤ n) :
    π (pol (esymm (Fin n) k r)) = 0 := by
  let F : MvPolynomial (Fin n) k →+* R := (AlgHom.comp π pol).toRingHom
  let _ : Module (KLRAlgebra k Q ν) R := Module.compHom _ (AlgHom.toRingHom π)
  let _ := Seq.uniqueOfForall same
  let s : Seq ν := default
  have he : (e s : KLRAlgebra k Q ν) = 1 := e_eq_one_of_forall same Q s
  have hlabels (a b : Fin n) : s.lbl a = s.lbl b := (same _ (s.mem a)).trans (same _ (s.mem b)).symm
  have hact (p : MvPolynomial (Fin n) k) (hp : F p = 0) :
      ∀ v : R, (pol p * e s : KLRAlgebra k Q ν) • v = 0 := by
    intro v
    change π (pol p * e s) * v = 0
    rw [he, mul_one, show π (pol p) = 0 from hp, zero_mul]
  have hdd (j : ℕ) (p : MvPolynomial (Fin n) k) (hp : F p = 0) :
      F (dd k n j p) = 0 := by
    by_cases hj : j + 1 < n
    · have hd := dd_smul_eq_zero (Q := Q) j hj (hlabels ⟨j, by omega⟩ ⟨j+1, hj⟩)
        (hact p hp) (1 : R)
      change π (pol (dd k n j p) * e s) * 1 = 0 at hd
      change π (pol (dd k n j p)) = 0
      simpa only [he, mul_one] using hd
    · rw [dd_eq_zero (Nat.le_of_not_gt hj), LinearMap.zero_apply, map_zero]
  have hpow : ∀ a : Fin n, F (X a ^ n) = 0 := by
    intro a
    obtain ⟨j, hj⟩ := a
    induction j with
    | zero =>
      have hc := mk_cycElt (Q := Q) (a := powers) s
      rw [cycElt_of_pos _ _ s hj, he, mul_one, map_pow, Polynomial.aeval_X] at hc
      change π (pol (X ⟨0, hj⟩ ^ n)) = 0
      rw [map_pow, pol_X, map_pow]
      simpa only [map_pow] using hc
    | succ j ih =>
      have hf := ih (by omega)
      have hs := swap_smul_eq_zero (Q := Q) j hj (hlabels ⟨j, by omega⟩ ⟨j+1, hj⟩)
          (hact _ hf) (1 : R)
      change π (pol (swapPol j hj (X ⟨j, by omega⟩ ^ n)) * e s) * 1 = 0 at hs
      rw [he, mul_one, mul_one, swapPol, map_pow, rename_X, Equiv.swap_apply_left] at hs
      exact hs
  have hgen (m : ℕ) (G : MvPolynomial (Fin m) k →+* R)
      (hd : ∀ j p, G p = 0 → G (dd k m j p) = 0)
      (hp : ∀ a : Fin m, G (X a ^ m) = 0) (hrm : r ≤ m) :
      G (esymm (Fin m) k r) = 0 := by
    cases m with
    | zero => omega
    | succ m => exact terminal_coefficients m G hd (hp (Fin.last m)) r hr hrm
  exact hgen n F hdd hpow hrn

include same in
/-- Every polynomial in the coinvariant ideal vanishes in the saturated
single-colour cyclotomic block. -/
theorem terminal_pol_eq_zero_of_mem_coinvIdeal (p : MvPolynomial (Fin n) k)
    (hp : p ∈ coinvIdeal k n) : π (pol p) = 0 := by
  let F : MvPolynomial (Fin n) k →+* R := (AlgHom.comp π pol).toRingHom
  apply (RingHom.mem_ker (f := F)).1
  rw [coinvIdeal_eq_span_esymm] at hp
  refine (Ideal.span_le.2 ?_) hp
  rintro _ ⟨j, rfl⟩
  exact terminal_pol_esymm_eq_zero same Q (j.val + 1) (by omega) j.isLt

end Cyclotomic
end Categorification.KLR.CycKLR
