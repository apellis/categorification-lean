/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicGradedRestriction
import Categorification.KLR.CyclotomicGradedCharacter
import Categorification.KLR.Prop32
import Categorification.KLR.DividedPowerK0

/-!
# The cyclotomic quantum commutator at an absent colour

Kang–Kashiwara, arXiv:1102.4677v4, Theorem 5.2 and Lemma 6.1. If the
weight content contains no i, the FE term vanishes. The dot-unit summands
in EF give the quantum-integer coefficient on every graded projective class.
-/

noncomputable section

namespace Categorification.KLR.CycKLR

open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (G : GradingDatum Q) (Λ : I → ℕ) (i : I) (β : Multiset I)
    (hsym : KLRSymm Q)
    (hQ : ∀ s t : I, s ≠ t → ∃ c : k, IsUnit c ∧ (polyInY (Q s t)).leadingCoeff = Polynomial.C c)
    {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X) (hΛ : (Λ i : ℤ) = RD.pair (RD.iY i) highest)
    (hdeg : ∀ j, j ≠ i → ((polyInY (Q j i)).natDegree : ℤ) = -RD.pair (RD.iY i) (RD.iX j))
    (hi : i ∉ β)

local notation "aΛ" => (fun j => (Polynomial.X : Polynomial k) ^ Λ j)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rl" => CycKLR k Q aΛ β
local notation "Su" => CycKLR k Q aΛ (Si + β)
local notation "wt" => RD.pair (RD.iY i) (highest - Multiset.sum (Multiset.map RD.iX β))
local notation "LP" => LaurentPolynomial ℤ

private theorem dotTensor_mem_grade (P : GProj (grade G Λ β)) (d : ℤ) (r : ℕ) (z : P.carrier)
    (hz : z ∈ P.grading (d - r • G.degX i)) :
    BalancedTensor.tmul (cornerToInd Q i aΛ β (dotUnitTerm Q i aΛ β r 1)) z ∈
      balancedGrading Su Rl (Graded.submodule (grade G Λ (Si + β)) (lIdeal (lastIdem Q i aΛ β)))
        P.grading d := by
  let x := cornerToInd Q i aΛ β (dotUnitTerm Q i aΛ β r 1)
  have hx : x ∈ Graded.submodule (grade G Λ (Si + β)) (lIdeal (lastIdem Q i aΛ β)) (r • G.degX i) := by
    change (dotUnitTerm Q i aΛ β r 1 : Su) ∈ grade G Λ (Si + β) _
    simpa only [zero_add] using dotUnitTerm_mem_grade G Λ i β r SetLike.GradedOne.one_mem
  have h := tmul_mem_balancedGrading (B := Su) (A := Rl) hx hz
  rw [show r • G.degX i + (d - r • G.degX i) = d by abel] at h
  exact h

include hΛ hdeg hi in
private theorem absentEF_preserves (P : GProj (grade G Λ β)) (d : ℤ)
    (v : Fin (wt).toNat → P.carrier)
    (hv : ∀ r : Fin (wt).toNat, v r ∈ P.grading (d - (r : ℕ) • G.degX i)) :
    (absentEFEquiv Q i aΛ β P.carrier hsym hQ (fun _ => Polynomial.monic_X_pow _) RD highest
      (by simpa using hΛ) hdeg hi v).1 ∈ balancedGrading Su Rl
      (Graded.submodule (grade G Λ (Si + β)) (lIdeal (lastIdem Q i aΛ β))) P.grading d := by
  rw [absentEFEquiv_val]
  exact Submodule.sum_mem _ fun r _ => dotTensor_mem_grade G Λ i β P d r _ (hv r)

include hΛ hdeg hi in
/-- The absent-colour dot-unit isomorphism is homogeneous after the shift
by the degree of each dot power (Kang–Kashiwara, Theorem 5.2(a)). -/
def gradedAbsentEFEquiv (P : GProj (grade G Λ β)) :
    (GProj.pi fun r : Fin (wt).toNat => P.shift ((r : ℕ) • G.degX i)).Iso
      (gradedResProj G Λ i β hsym hQ (gradedIndProj G Λ i β P)) :=
  GradedEquiv.ofPreserves
    (absentEFEquiv Q i aΛ β P.carrier hsym hQ (fun _ => Polynomial.monic_X_pow _) RD highest
      (by simpa using hΛ) hdeg hi)
    (absentEF_preserves G Λ i β hsym hQ RD highest hΛ hdeg hi P)

include hΛ hdeg hi in
/-- At an absent colour, unshifted EF multiplies each projective class by
the finite sum of the dot degrees from Kang–Kashiwara, Theorem 5.2(a). -/
theorem resK0_indK0_of_notMem (x : K0 (grade G Λ β)) :
    resK0 G Λ i β hsym hQ (indK0 G Λ i β x) =
      (∑ r : Fin (wt).toNat, (LaurentPolynomial.T ((r : ℕ) • G.degX i) : LP)) • x := by
  induction x using K0.induction_on with
  | of P =>
    rw [indK0_of, resK0_of, ← K0.of_eq_of_iso (gradedAbsentEFEquiv G Λ i β hsym hQ RD highest hΛ hdeg hi P),
      K0.of_pi, Finset.sum_smul]
    exact Finset.sum_congr rfl fun r _ => (K0.T_smul_of _ P).symm
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | neg x hx => simp only [map_neg, smul_neg, hx]

/-- The shifted nonnegative string of dot degrees gives the quantum integer. -/
theorem normalized_dot_sum (d : ℤ) (n : ℕ) :
    (LaurentPolynomial.T (d * (1 - (n : ℤ))) : LP) *
      ∑ r : Fin n, LaurentPolynomial.T ((r : ℕ) • (2 * d)) = qint (qUnitLP ^ d) n := by
  rw [qint, ← zpow_mul, val_qUnitLP_zpow, val_qUnitLP_zpow]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [LaurentPolynomial.T_pow, Nat.cast_ofNat, nsmul_eq_mul]

omit [DecidableEq I] in
include hΛ in
/-- The coroot pairing at content β in simple-root coordinates. -/
theorem pair_sub_content : wt = (Λ i : ℤ) - (β.map (A C i)).sum := by
  rw [map_sub, ← hΛ]
  congr 1
  induction β using Multiset.induction_on with
  | empty => simp
  | cons j β ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, map_add, RD.pair_iY_iX_eq_A]
    exact congrArg _ ih

include hΛ hdeg hi in
/-- The quantum commutator from Kang–Kashiwara, Lemma 6.1, on every weight
whose root content omits i. The scalar is the symmetric quantum integer
in the Laurent polynomial ring. -/
theorem raise_lower_sub_lower_raise_of_notMem (hdot : G.degX i = 2 * di C i)
    (x : K0 (grade G Λ β)) :
    raise G Λ i hsym hQ C (lower G Λ i (DirectSum.lof LP _ _ β x)) -
        lower G Λ i (raise G Λ i hsym hQ C (DirectSum.lof LP _ _ β x)) =
      qint (qUnitLP ^ di C i) (wt).toNat • DirectSum.lof LP _ _ β x := by
  have hwt := pair_sub_content Λ i β RD highest hΛ
  have hnat : ((aΛ i).natDegree : ℤ) = RD.pair (RD.iY i) highest := by simpa using hΛ
  have hpos : 0 ≤ wt := by
    rw [← degA_sub_count_eq_pair i β aΛ RD highest hnat hdeg, Multiset.count_eq_zero.mpr hi]
    simp
  rw [lower_lof, raise_lof, raise_lof_of_notMem _ _ _ _ _ _ _ hi, map_zero, sub_zero,
    ← map_smul, raiseK0, LinearMap.smul_apply, resK0_indK0_of_notMem G Λ i β hsym hQ RD highest hΛ hdeg hi,
    smul_smul, raiseShift, ← hwt, hdot]
  congr 2
  simpa only [Int.toNat_of_nonneg hpos] using normalized_dot_sum (di C i) (wt).toNat

end Categorification.KLR.CycKLR
