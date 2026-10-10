/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicInj

/-!
# KK's element `A` is central: Kang–Kashiwara Remark 4.20 (i)

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, Remark 4.20 (i): the element
`∑_ν a_i(t) ∏_{ν_a ≠ i} Q_{i, ν_a}(t, x_a) e(ν)` is central in `R(β) ⊗ k[t]` (cf. KL I Thm. 2.9).
Here: KK's `A = ∑_𝐢 a_{i_1}(x_1) F_n(𝐢) e(𝐢)` (`aElt`) commutes with `k[x_1] ⊗ R^1(β)`
(`aElt_comm_subR1`), the key input being that `F_n(𝐢)` is equivariant under the transpositions
of the strands `2, …, n + 1` (`swapPol_cycF_shift`).
-/

namespace Categorification.KLR

open MvPolynomial TypeA Equiv PolyRep NilHecke

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-- The transposition `j ↔ j + 1` of `ℕ`. -/
def swapIdx (j b : ℕ) : ℕ := if b = j then j + 1 else if b = j + 1 then j else b

omit [DecidableEq I] in
theorem swapIdx_swapIdx (j b : ℕ) : swapIdx j (swapIdx j b) = b := by
  unfold swapIdx; split_ifs <;> omega

theorem cycFac_pos (s : Seq ν) {b : ℕ} (hb : b < m) (h1 : 1 ≤ b) :
    cycFac Q s b = if s.1 ⟨b, hb⟩ = s.1 ⟨0, by omega⟩ then -1
      else rename ![⟨0, by omega⟩, ⟨b, hb⟩] (Q (s.1 ⟨0, by omega⟩) (s.1 ⟨b, hb⟩)) := by
  simp only [cycFac, hb, ↓reduceDIte, h1, ↓reduceIte]

theorem swapPol_cycFac (s : Seq ν) (j : ℕ) (hj : j + 1 < m) (hj1 : 1 ≤ j) (b : ℕ) :
    swapPol j hj (cycFac Q s b) = cycFac Q (sadj m j • s) (swapIdx j b) := by
  have hσ : swapIdx j b < m ↔ b < m := by unfold swapIdx; split_ifs <;> omega
  have hσ1 : 1 ≤ swapIdx j b ↔ 1 ≤ b := by unfold swapIdx; split_ifs <;> omega
  by_cases hb : b < m
  · have hb' : swapIdx j b < m := hσ.2 hb
    have hval : (sadj m j (⟨swapIdx j b, hb'⟩ : Fin m)) = ⟨b, hb⟩ := by
      apply Fin.ext; rw [sadj_apply_val hj]
      show (if swapIdx j b = j then j + 1 else if swapIdx j b = j + 1 then j else swapIdx j b) = b
      unfold swapIdx; split_ifs <;> omega
    have hsw : swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, hj⟩ ⟨b, hb⟩ = ⟨swapIdx j b, hb'⟩ := by
      apply Fin.ext; rw [swap_apply_def]
      split_ifs with e1 e2
      · rw [Fin.ext_iff] at e1; simp only at e1 ⊢; unfold swapIdx; split_ifs; omega
      · rw [Fin.ext_iff] at e2; simp only at e2 ⊢; unfold swapIdx; split_ifs <;> omega
      · rw [Fin.ext_iff] at e1 e2; simp only at e1 e2 ⊢; unfold swapIdx; split_ifs; omega
    have hlab : (sadj m j • s).1 ⟨swapIdx j b, hb'⟩ = s.1 ⟨b, hb⟩ := by
      rw [sadj_smul_apply, hval]
    have h0 : (sadj m j • s).1 ⟨0, by omega⟩ = s.1 ⟨0, by omega⟩ := by
      rw [sadj_smul_apply, sadj_apply_of_ne _ (by show (0 : ℕ) ≠ j; omega)
        (by show (0 : ℕ) ≠ j + 1; omega)]
    by_cases h1 : 1 ≤ b
    · rw [cycFac_pos s hb h1, cycFac_pos _ hb' (hσ1.2 h1), hlab, h0]
      split_ifs
      · rw [map_neg, map_one]
      · rw [swapPol, rename_rename_vec2, swap_apply_of_ne_of_ne
          (Fin.ne_of_val_ne (by show (0 : ℕ) ≠ j; omega))
          (Fin.ne_of_val_ne (by show (0 : ℕ) ≠ j + 1; omega)), hsw]
    · have hb0 : b = 0 := by omega
      subst hb0
      have : swapIdx j 0 = 0 := by
        simp only [swapIdx, (show (0 : ℕ) ≠ j by omega), (show (0 : ℕ) ≠ j + 1 by omega),
          ↓reduceIte]
      rw [this]
      simp only [cycFac, hb, ↓reduceDIte, h1, ↓reduceIte, map_one]
  · have hb' : ¬ swapIdx j b < m := fun h => hb (hσ.1 h)
    simp only [cycFac, hb, hb', ↓reduceDIte, map_one]

theorem swapPol_cycF_shift (s : Seq ν) (j : ℕ) (hj : j + 1 < m) (hj1 : 1 ≤ j) (n : ℕ)
    (hn : j + 1 ≤ n) : swapPol j hj (cycF Q s n) = cycF Q (sadj m j • s) n := by
  rw [cycF, map_prod, cycF]
  simp_rw [swapPol_cycFac s j hj hj1]
  refine Finset.prod_nbij' (swapIdx j) (swapIdx j) ?_ ?_ ?_ ?_ ?_
  · intro b hb; simp only [Finset.mem_range] at hb ⊢; unfold swapIdx; split_ifs <;> omega
  · intro b hb; simp only [Finset.mem_range] at hb ⊢; unfold swapIdx; split_ifs <;> omega
  · intro b _; exact swapIdx_swapIdx j b
  · intro b _; exact swapIdx_swapIdx j b
  · intro b _; rfl

variable (a : I → Polynomial k)

/-- **KK Remark 4.20 (i)**: `A` commutes with the crossings `ψ_j`, `j ≥ 1`. -/
theorem aElt_mul_ψ (h0 : 0 < m) (n : ℕ) (hn : n + 1 = m) (j : ℕ) (hj1 : 1 ≤ j) :
    (aElt a h0 n * ψ j : A) = ψ j * aElt a h0 n := by
  by_cases hj : j + 1 < m
  · have hG : ∀ s : Seq ν, swapPol j hj (cycA a h0 s * cycF Q s n) =
        cycA a h0 (sadj m j • s) * cycF Q (sadj m j • s) n := by
      intro s
      rw [map_mul, swapPol_cycA a h0 s j hj hj1, swapPol_cycF_shift s j hj hj1 n (by omega)]
      congr 1
      rw [cycA, cycA, sadj_smul_apply, sadj_apply_of_ne _ (by show (0 : ℕ) ≠ j; omega)
        (by show (0 : ℕ) ≠ j + 1; omega)]
    have hne : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, hj⟩ := fun e => by simp [Fin.ext_iff] at e
    have hterm : ∀ s : Seq ν, (ψ j * (pol (cycA a h0 s * cycF Q s n) * e s) : A) =
        pol (cycA a h0 (sadj m j • s) * cycF Q (sadj m j • s) n) * e (sadj m j • s) * ψ j := by
      intro s
      rw [← mul_assoc, ψ_mul_pol_mul_e j hj s, hG, mul_assoc _ (ψ j), ψ_mul_e, ← mul_assoc]
      split_ifs with hs
      · have hss : sadj m j • s = s := sadj_smul_eq_self hj hs
        have hsym : swapPol j hj (cycA a h0 s * cycF Q s n) = cycA a h0 s * cycF Q s n := by
          rw [hG, hss]
        rw [dd_of_lt hj, ddiff_eq_zero_of_rename_eq hne hsym, map_zero, zero_mul, add_zero]
      · rw [add_zero]
    rw [aElt, Finset.sum_mul, Finset.mul_sum]
    simp_rw [hterm]
    exact (Fintype.sum_equiv (MulAction.toPerm (sadj m j)) _ _ (fun s => rfl)).symm
  · rw [ψ_eq_zero j (by omega), mul_zero, zero_mul]

/-- **KK Remark 4.20 (i)**: `A` commutes with `k[x_1] ⊗ R^1(β)`. -/
theorem aElt_comm_subR1 (h0 : 0 < m) (n : ℕ) (hn : n + 1 = m) {w : A}
    (hw : w ∈ subR1 (k := k) (Q := Q) ν) : aElt a h0 n * w = w * aElt a h0 n := by
  induction hw using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨b, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · rw [aElt, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_assoc, ← x_mul_e, ← mul_assoc, ← mul_assoc, ← pol_X, ← map_mul, mul_comm, map_mul]
    · rw [aElt, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_assoc, e_mul_e, ← mul_assoc, (commute_e_pol t _).eq, mul_assoc, e_mul_e]
      split_ifs with h1 h2 h2
      · subst h1; rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    · exact aElt_mul_ψ a h0 n hn j hj
  | algebraMap c => exact Algebra.commutes c _ |>.symm
  | add y z _ _ hy hz => rw [mul_add, add_mul, hy, hz]
  | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]

end KLRAlgebra

end Categorification.KLR
