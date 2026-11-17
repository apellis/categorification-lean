/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicPresentCommutatorK0
import LieLean.Algebra.QuantumGroup.QBinomial

/-!
# The equal-colour quantum commutator on ordinary cyclotomic projectives

Kang–Kashiwara, arXiv:1102.4677v4, Lemma 6.1, i = j. On each summand of
the graded projective Grothendieck group the commutator acts by the signed
Laurent-polynomial quantum integer of the coroot pairing.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot
local notation "LP" => LaurentPolynomial ℤ

/-- The two finite-sum conventions for the Laurent quantum integer agree. -/
theorem qNatU_eq_qint (u : LPˣ) (n : ℕ) : LieLean.QuantumGroup.qNatU u n = qint u n := by
  rw [LieLean.QuantumGroup.qNatU, qint_eq_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr := Finset.mem_range.mp hr
  rw [← zpow_natCast, ← zpow_natCast, inv_zpow, ← zpow_neg, ← zpow_add]
  congr 2
  push_cast [Nat.sub_sub, Nat.cast_sub (by omega : 1 + r ≤ n)]
  ring

private theorem qIntU_nonneg (u : LPˣ) {n : ℤ} (h : 0 ≤ n) :
    LieLean.QuantumGroup.qIntU u n = qint u n.toNat := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
  exact qNatU_eq_qint u m

private theorem qIntU_neg (u : LPˣ) {n : ℤ} (h : n < 0) :
    LieLean.QuantumGroup.qIntU u n = -qint u (-n).toNat := by
  cases n with
  | ofNat m => exact False.elim ((Int.natCast_nonneg m).not_gt h)
  | negSucc m => exact congrArg Neg.neg (qNatU_eq_qint u (m+1))

private theorem normalized_counit_sum (d : ℤ) (n : ℕ) :
    (LaurentPolynomial.T (d * (1 + (n : ℤ))) : LP) *
      ∑ r : Fin n, LaurentPolynomial.T (-(((r : ℕ) + 1) • (2 * d))) = qint (qUnitLP ^ d) n := by
  rw [qint_eq_sum, Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← LaurentPolynomial.T_add, ← zpow_mul, val_qUnitLP_zpow]
  congr 1
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I) (β : Multiset I)
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
    {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X) (hΛ : (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
    (hdot : G.degX i = 2 * di C i)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "β₁" => (Si + β)
local notation "wt" => RD.pair (RD.iY i) (highest - Multiset.sum (Multiset.map RD.iX β₁))
local notation "EFK" => LinearMap.comp (resK0 G Λ i β₁ hsym hQ) (indK0 G Λ i β₁)
local notation "FEK" => LinearMap.comp (indK0 G Λ i β) (resK0 G Λ i β hsym hQ)
local notation "s" => raiseShift Λ i β₁ C
local notation "t" => raiseShift Λ i β C
local notation "T" => LaurentPolynomial.T (R := ℤ)

omit [DecidableEq I] in
include hdot in
private theorem shift_step : s + (-G.degX i) = t := by
  simp only [raiseShift, Multiset.map_add, Multiset.map_singleton, Multiset.sum_add,
    Multiset.sum_singleton, A_self, hdot]
  ring

include hΛ hdeg hdot in
private theorem normalized_present (x : K0 (grade G Λ β₁)) :
    T s • EFK x - T t • FEK x = LieLean.QuantumGroup.qIntU (qUnitLP ^ di C i) wt • x := by
  have hs : s = di C i * (1 - wt) := by rw [pair_sub_content Λ i β₁ RD highest hΛ, raiseShift]
  have hs' := shift_step G Λ i β hdot
  rw [← hs', LaurentPolynomial.T_add, mul_smul, ← smul_sub]
  by_cases hp : 0 ≤ wt
  · rw [positiveCommutatorK0 G Λ i β hsym hQ RD highest hΛ hdeg hp, add_sub_cancel_left,
      smul_smul, qIntU_nonneg _ hp, hdot, hs]
    congr 1
    simpa only [Int.toNat_of_nonneg hp] using normalized_dot_sum (di C i) (wt).toNat
  · have hn := lt_of_not_ge hp
    rw [negativeCommutatorK0 G Λ i β hsym hQ RD highest hΛ hdeg hn.le, sub_add_cancel_left,
      smul_neg, smul_smul, qIntU_neg _ hn, neg_smul, hdot, hs]
    congr 2
    simpa only [Int.toNat_of_nonneg (neg_nonneg.mpr hn.le), ← sub_eq_add_neg]
      using normalized_counit_sum (di C i) (-wt).toNat

include hΛ hdeg hdot in
/-- The equal-colour commutator on every projective weight group, including
the boundary, for arbitrary sign of the coroot pairing (Kang–Kashiwara,
arXiv:1102.4677v4, Lemma 6.1, i = j). -/
theorem raise_lower_sub_lower_raise (x : K0 (grade G Λ β)) :
    raise G Λ i hsym hQ C (lower G Λ i (DirectSum.lof LP _ _ β x)) -
      lower G Λ i (raise G Λ i hsym hQ C (DirectSum.lof LP _ _ β x)) =
    LieLean.QuantumGroup.qIntU (qUnitLP ^ di C i)
      (RD.pair (RD.iY i) (highest - (β.map RD.iX).sum)) • DirectSum.lof LP _ _ β x := by
  by_cases hi : i ∈ β
  · obtain ⟨γ, he⟩ := Multiset.exists_cons_of_mem hi
    rw [← Multiset.singleton_add] at he
    subst β
    have H := congrArg (DirectSum.lof LP _ (fun δ => K0 (grade G Λ δ)) (Si + γ))
      (normalized_present G Λ i γ hsym hQ RD highest hΛ hdeg hdot x)
    simpa only [lower_lof, raise_lof, raiseK0, LinearMap.smul_apply, LinearMap.comp_apply,
      map_sub, map_smul] using H
  · have hp : 0 ≤ RD.pair (RD.iY i) (highest - (β.map RD.iX).sum) := by
      let a := fun j => (Polynomial.X : Polynomial k) ^ Λ j
      have ha : ((a i).natDegree : ℤ) = RD.pair (RD.iY i) highest := by simpa [a] using hΛ
      rw [← degA_sub_count_eq_pair i β a RD highest ha hdeg, Multiset.count_eq_zero.mpr hi]
      simp
    rw [qIntU_nonneg _ hp]
    exact raise_lower_sub_lower_raise_of_notMem G Λ i β hsym hQ RD highest hΛ hdeg hi hdot x

end Categorification.KLR.CycKLR
