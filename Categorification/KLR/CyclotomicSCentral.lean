/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicS

/-!
# Centrality of the squared-difference polynomial

The centrality assertion for `S` used in Kang–Kashiwara, arXiv:1102.4677v4, §5.2.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial TypeA Equiv PolyRep NilHecke
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

/-- A squared difference when the two strand colours agree, and one otherwise. -/
noncomputable def sFac (s : Seq ν) (b : ℕ) : MvPolynomial (Fin m) k :=
  if h : b < m ∧ 1 ≤ b then
    if s.1 ⟨b, h.1⟩ = s.1 ⟨0, by omega⟩ then
      (X ⟨0, by omega⟩ - X ⟨b, h.1⟩) ^ 2 else 1
  else 1

noncomputable def sFactors (s : Seq ν) (n : ℕ) : MvPolynomial (Fin m) k :=
  ∏ b ∈ Finset.range (n + 1), sFac s b

theorem gLead_eq_sFactors (n : ℕ) (hn : n < m) (s : Seq ν) :
    gLead (k := k) n hn s = sFactors s n := by
  induction n with
  | zero => simp [gLead, sFactors, sFac]
  | succ n ih =>
    rw [sFactors, Finset.prod_range_succ, ← sFactors, ← ih (by omega), gLead]
    simp only [sFac, hn]
    exact mul_comm _ _

theorem swapPol_sFac (s : Seq ν) (j : ℕ) (hj : j + 1 < m) (hj1 : 1 ≤ j) (b : ℕ) :
    swapPol j hj (sFac (k := k) s b) = sFac (sadj m j • s) (swapIdx j b) := by
  have hσ : swapIdx j b < m ↔ b < m := by unfold swapIdx; split_ifs; all_goals omega
  have hσ1 : 1 ≤ swapIdx j b ↔ 1 ≤ b := by unfold swapIdx; split_ifs; all_goals omega
  by_cases hb : b < m ∧ 1 ≤ b
  · have hb' : swapIdx j b < m ∧ 1 ≤ swapIdx j b := ⟨hσ.2 hb.1, hσ1.2 hb.2⟩
    have hval : sadj m j (⟨swapIdx j b, hb'.1⟩ : Fin m) = ⟨b, hb.1⟩ := by
      apply Fin.ext
      rw [sadj_apply_val hj]
      show (if swapIdx j b = j then j + 1 else if swapIdx j b = j + 1 then j else swapIdx j b) = b
      unfold swapIdx
      split_ifs <;> omega
    have hsw : swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, hj⟩ ⟨b, hb.1⟩ = ⟨swapIdx j b, hb'.1⟩ := by
      apply Fin.ext
      rw [swap_apply_def]
      split_ifs with e1 e2
      · rw [Fin.ext_iff] at e1; simp only at e1 ⊢; unfold swapIdx; split_ifs; all_goals omega
      · rw [Fin.ext_iff] at e2; simp only at e2 ⊢; unfold swapIdx; split_ifs; all_goals omega
      · rw [Fin.ext_iff] at e1 e2; simp only at e1 e2 ⊢; unfold swapIdx; split_ifs; all_goals omega
    have hlab : (sadj m j • s).1 ⟨swapIdx j b, hb'.1⟩ = s.1 ⟨b, hb.1⟩ := by
      rw [sadj_smul_apply, hval]
    have h0 : (sadj m j • s).1 ⟨0, by omega⟩ = s.1 ⟨0, by omega⟩ := by
      rw [sadj_smul_apply, sadj_apply_of_ne _ (by show (0 : ℕ) ≠ j; omega)
        (by show (0 : ℕ) ≠ j + 1; omega)]
    rw [sFac, dite_eq_left hb, sFac, dite_eq_left hb', hlab, h0]
    split_ifs
    · rw [swapPol, map_pow, map_sub, rename_X, rename_X,
        swap_apply_of_ne_of_ne (Fin.ne_of_val_ne (by show (0 : ℕ) ≠ j; omega))
          (Fin.ne_of_val_ne (by show (0 : ℕ) ≠ j + 1; omega)), hsw]
    · rw [map_one]
  · have hb' : ¬ (swapIdx j b < m ∧ 1 ≤ swapIdx j b) := fun h => hb ⟨hσ.1 h.1, hσ1.1 h.2⟩
    simp only [sFac, hb, hb', ↓reduceDIte, map_one]

theorem swapPol_sFactors (s : Seq ν) (j : ℕ) (hj : j + 1 < m) (hj1 : 1 ≤ j)
    (n : ℕ) (hn : j + 1 ≤ n) :
    swapPol j hj (sFactors (k := k) s n) = sFactors (sadj m j • s) n := by
  rw [sFactors, map_prod, sFactors]
  simp_rw [swapPol_sFac s j hj hj1]
  refine Finset.prod_nbij' (swapIdx j) (swapIdx j) ?_ ?_ ?_ ?_ ?_
  · intro b hb; simp only [Finset.mem_range] at hb ⊢; unfold swapIdx; split_ifs; all_goals omega
  · intro b hb; simp only [Finset.mem_range] at hb ⊢; unfold swapIdx; split_ifs; all_goals omega
  · intro b _; exact swapIdx_swapIdx j b
  · intro b _; exact swapIdx_swapIdx j b
  · intro b _; rfl

/-- The diagonal squared-difference element before selecting the first colour. -/
noncomputable def sElt (n : ℕ) : A := ∑ s : Seq ν, pol (sFactors s n) * e s

theorem sElt_mul_e (n : ℕ) (t : Seq ν) : (sElt n * e t : A) = pol (sFactors t n) * e t := by
  rw [sElt, Finset.sum_mul, Finset.sum_eq_single t]
  · rw [mul_assoc, e_mul_self]
  · intro s _ hs; rw [mul_assoc, e_mul_e]; simp only [hs, ↓reduceIte, mul_zero]
  · simp

theorem sElt_mul_ψ (n : ℕ) (hn : n + 1 = m) (j : ℕ) (hj1 : 1 ≤ j) :
    (sElt n * ψ j : A) = ψ j * sElt n := by
  by_cases hj : j + 1 < m
  · have hG := fun s : Seq ν => swapPol_sFactors (k := k) s j hj hj1 n (by omega)
    have hne : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, hj⟩ := fun e => by simp [Fin.ext_iff] at e
    have hterm : ∀ s : Seq ν, (ψ j * (pol (sFactors s n) * e s) : A) =
        pol (sFactors (sadj m j • s) n) * e (sadj m j • s) * ψ j := by
      intro s
      rw [← mul_assoc, ψ_mul_pol_mul_e j hj s, hG, mul_assoc _ (ψ j), ψ_mul_e, ← mul_assoc]
      split_ifs with hs
      · have hss : sadj m j • s = s := sadj_smul_eq_self hj hs
        have hsym : swapPol j hj (sFactors (k := k) s n) = sFactors s n := by rw [hG, hss]
        rw [dd_of_lt hj, ddiff_eq_zero_of_rename_eq hne hsym, map_zero, zero_mul, add_zero]
      · rw [add_zero]
    rw [sElt, Finset.sum_mul, Finset.mul_sum]
    simp_rw [hterm]
    exact (Fintype.sum_equiv (MulAction.toPerm (sadj m j)) _ _ (fun s => rfl)).symm
  · rw [ψ_eq_zero j (by omega), mul_zero, zero_mul]

theorem sElt_comm_subR1 (n : ℕ) (hn : n + 1 = m) {w : A}
    (hw : w ∈ subR1 (k := k) (Q := Q) ν) : sElt n * w = w * sElt n := by
  induction hw using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with (⟨b, rfl⟩ | ⟨t, rfl⟩) | ⟨j, hj, rfl⟩
    · rw [sElt, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_assoc, ← x_mul_e, ← mul_assoc, ← mul_assoc, ← pol_X, ← map_mul, mul_comm, map_mul]
    · rw [sElt, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_assoc, e_mul_e, ← mul_assoc, (commute_e_pol t _).eq, mul_assoc, e_mul_e]
      split_ifs with h1 h2 h2
      · subst h1; rfl
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    · exact sElt_mul_ψ n hn j hj
  | algebraMap c => exact Algebra.commutes c _ |>.symm
  | add y z _ _ hy hz => rw [mul_add, add_mul, hy, hz]
  | mul y z _ _ hy hz => rw [← mul_assoc, hy, mul_assoc, hz, mul_assoc]

section Polynomial

variable (i : I) (β : Multiset I) (a : I → Polynomial k)
local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "T" => KLRAlgebra k Q Si ⊗[k] KLRAlgebra k Q β
local notation "R" => KLRAlgebra k Q (Si + β)
local notation "Rl" => CycKLR k Q a β

noncomputable def sTensor : T := ∑ s : Seq β, gLeadTensor i β (Multiset.card β) le_rfl s

theorem concat_sTensor : concat Q Si β (sTensor i β) = sElt (Multiset.card β) * oneConcat Q Si β := by
  rw [sTensor, map_sum, oneConcat_single_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [concat_gLeadTensor, gLead_eq_sFactors, sElt_mul_e]

theorem thetaL_sTensor : thetaL Q i β a (sTensor i β) = sPoly i β a := by
  rw [sTensor, map_sum, sPoly]
  exact Finset.sum_congr rfl fun s _ => thetaL_gLeadTensor i β a _ _ s

variable (hsym : KLRSymm Q)

include hsym in
theorem sTensor_comm (t : T) : sTensor i β * t = t * sTensor i β := by
  apply concat_injective hsym
  have hc := sElt_comm_subR1 (Multiset.card β) (card_single_add i β).symm
    (concat_mem_subR1 i β t)
  rw [concat_mul, concat_mul, concat_sTensor, mul_assoc, oneConcat_mul_concat,
    ← mul_assoc, ← hc, mul_assoc, concat_mul_oneConcat]

include hsym in
/-- The actual squared-difference polynomial `S` is central. -/
theorem sPoly_comm (q : Polynomial Rl) : Commute q (sPoly i β a) := by
  obtain ⟨t, rfl⟩ := thetaL_surjective (Q := Q) i β a q
  rw [← thetaL_sTensor]
  exact (show Commute t (sTensor i β) from (sTensor_comm i β hsym t).symm).map
    (thetaL Q i β a)

end Polynomial

end Categorification.KLR.KLRAlgebra
