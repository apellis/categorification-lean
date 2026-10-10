/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicBProduct

/-!
# The monic squared-difference polynomial

The polynomial `S` in Kang–Kashiwara, arXiv:1102.4677v4, §5.2, immediately before
(5.16). It is the value of the actual `B` map on the intertwiner product, and it
is monic of degree twice the multiplicity of the selected colour.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}
  (i : I) (β : Multiset I) (a : I → Polynomial k)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "Rl" => CycKLR k Q a β
local notation "R" => KLRAlgebra k Q (Si + β)

/-- Number of entries of the selected colour in a prefix. -/
def colourPrefix (n : ℕ) (hn : n ≤ Multiset.card β) (s : Seq β) : ℕ :=
  ∑ b : Fin n, if s.1 ⟨b.val, lt_of_lt_of_le b.isLt hn⟩ = i then 1 else 0

theorem colourPrefix_zero (s : Seq β) : colourPrefix i β 0 (Nat.zero_le _) s = 0 := by
  simp [colourPrefix]

theorem colourPrefix_succ (n : ℕ) (hn : n + 1 ≤ Multiset.card β) (s : Seq β) :
    colourPrefix i β (n + 1) hn s = colourPrefix i β n (by omega) s +
      if s.1 ⟨n, by omega⟩ = i then 1 else 0 := by
  rw [colourPrefix, Fin.sum_univ_castSucc]
  rfl

theorem colourPrefix_full (s : Seq β) :
    colourPrefix i β (Multiset.card β) le_rfl s = β.count i := by
  have h := congrArg (Multiset.count i) s.2
  rw [Multiset.count_map] at h
  rw [← h]
  change (∑ b : Fin (Multiset.card β), if s.1 b = i then 1 else 0) = _
  simp only [Finset.sum_boole, Finset.card, Finset.filter_val, eq_comm (a := i)]
  rfl

/-- The monic factor before the sequence idempotent. -/
noncomputable def gLeadFactors : (n : ℕ) → n ≤ Multiset.card β → Seq β → Polynomial Rl
  | 0, _, _ => 1
  | n + 1, hn, s =>
    (if s.1 ⟨n, by omega⟩ = i then
      (Polynomial.X - Polynomial.C (CycKLR.mk k Q a β (x ⟨n, by omega⟩))) ^ 2 else 1) *
      gLeadFactors n (by omega) s

theorem gLeadPoly_eq_factors (n : ℕ) (hn : n ≤ Multiset.card β) (s : Seq β) :
    gLeadPoly (Q := Q) i β a n hn s =
      gLeadFactors (Q := Q) i β a n hn s * Polynomial.C (CycKLR.mk k Q a β (e s)) := by
  induction n with
  | zero => rw [gLeadPoly, gLeadFactors, one_mul]
  | succ n ih => rw [gLeadPoly, gLeadFactors, ih (by omega), mul_assoc]

theorem gLeadFactors_monic (n : ℕ) (hn : n ≤ Multiset.card β) (s : Seq β) :
    (gLeadFactors (Q := Q) i β a n hn s).Monic := by
  induction n with
  | zero => exact Polynomial.monic_one
  | succ n ih =>
    rw [gLeadFactors]
    split_ifs
    · exact ((Polynomial.monic_X_sub_C _).pow 2).mul (ih (by omega))
    · simpa only [one_mul] using ih (by omega)

theorem gLeadFactors_natDegree [Nontrivial Rl] (n : ℕ) (hn : n ≤ Multiset.card β) (s : Seq β) :
    (gLeadFactors (Q := Q) i β a n hn s).natDegree = 2 * colourPrefix i β n hn s := by
  induction n with
  | zero => rw [gLeadFactors, Polynomial.natDegree_one, colourPrefix_zero, mul_zero]
  | succ n ih =>
    rw [gLeadFactors, colourPrefix_succ]
    split_ifs
    · rw [Polynomial.Monic.natDegree_mul ((Polynomial.monic_X_sub_C _).pow 2)
        (gLeadFactors_monic i β a n (by omega) s),
        Polynomial.Monic.natDegree_pow (Polynomial.monic_X_sub_C _) 2,
        Polynomial.natDegree_X_sub_C, ih (by omega)]
      omega
    · rw [one_mul, ih (by omega), add_zero]

/-- The sum of the sequence coefficients of `B(G_n)`. -/
noncomputable def sPoly : Polynomial Rl :=
  ∑ s : Seq β, gLeadPoly (Q := Q) i β a (Multiset.card β) le_rfl s

/-- Each summand has no terms above twice the colour multiplicity. -/
theorem gLeadPoly_degree_le (s : Seq β) :
    (gLeadPoly (Q := Q) i β a (Multiset.card β) le_rfl s).degree ≤ (2 * β.count i : ℕ) := by
  nontriviality Rl
  rw [gLeadPoly_eq_factors]
  apply Polynomial.degree_le_of_natDegree_le
  exact (Polynomial.natDegree_mul_C_le _ _).trans (by
    rw [gLeadFactors_natDegree, colourPrefix_full])

/-- The top coefficient of a summand is exactly its cyclotomic idempotent. -/
theorem gLeadPoly_coeff_top (s : Seq β) :
    (gLeadPoly (Q := Q) i β a (Multiset.card β) le_rfl s).coeff (2 * β.count i) =
      CycKLR.mk k Q a β (e s) := by
  nontriviality Rl
  rw [gLeadPoly_eq_factors, Polynomial.coeff_mul_C]
  have hd := gLeadFactors_natDegree (Q := Q) i β a (Multiset.card β) le_rfl s
  rw [colourPrefix_full] at hd
  rw [← hd, Polynomial.coeff_natDegree, (gLeadFactors_monic i β a _ _ s).leadingCoeff, one_mul]

theorem sPoly_degree_le : (sPoly i β a (Q := Q)).degree ≤ (2 * β.count i : ℕ) := by
  exact (Polynomial.degree_sum_le _ _).trans
    (Finset.sup_le fun s _ => gLeadPoly_degree_le i β a s)

theorem sPoly_coeff_top : (sPoly i β a (Q := Q)).coeff (2 * β.count i) = 1 := by
  rw [sPoly, Polynomial.finsetSum_coeff]
  simp only [gLeadPoly_coeff_top, ← map_sum, sum_e, map_one]

theorem sPoly_monic : (sPoly i β a (Q := Q)).Monic := by
  nontriviality Rl
  exact Polynomial.monic_of_degree_le _
    (sPoly_degree_le i β a) (sPoly_coeff_top i β a)

theorem sPoly_natDegree [Nontrivial Rl] :
    (sPoly i β a (Q := Q)).natDegree = 2 * β.count i := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (Polynomial.natDegree_le_of_degree_le (sPoly_degree_le i β a))
  rw [sPoly_coeff_top]
  exact one_ne_zero

variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)
  (h1 : 1 < Multiset.card ((Singleton.singleton i : Multiset I) + β))
  (hβ : 0 < Multiset.card β)

/-- `S X^m` is obtained by applying `B` to the dotted full intertwiner. -/
theorem bMap_gProd_mul_first_dot_pow (m : ℕ) :
    bMap i β hPQ hP a h1 hβ (Submodule.Quotient.mk
      (gProd (Multiset.card β) * oneConcat Q Si β *
        x ⟨0, zero_lt_card_single_add i β⟩ ^ m)) = sPoly i β a * Polynomial.X ^ m := by
  rw [bMap_mk, oneConcat_single_eq, Finset.mul_sum, Finset.sum_mul, map_sum, sPoly, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => bMap_gProd_cons1_mul_first_dot_pow i β a hPQ hP h1 hβ s m

end Categorification.KLR.KLRAlgebra
