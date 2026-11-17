/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Rouquier.SerreMaps
import Categorification.KLR.KL2.Serre
import Categorification.KLR.Rouquier.Polynomial

/-!
# Degrees and idempotent corners of the Serre crossing maps

Rouquier, *2-Kac–Moody algebras*, arXiv:0812.5023v1, §4.1.1,
Proposition 4.2, uses divided-power crossing maps and a contracting homotopy.
This module proves their homogeneous degrees for Cartan-compatible KLR
gradings, and restricts the maps to the divided-power idempotents at source
and target. The reverse map is scaled by the inverse leading coefficient.
The degree formulas agree with KL II arXiv:0804.2080v1, §3,
equations (17)–(26). No special choice of crossing polynomial is needed here.
-/

noncomputable section

namespace Categorification.KLR.Rouquier

open MvPolynomial KLRAlgebra TypeA QuantumGroup KL2

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "A" => KLRAlgebra k Q ν

section Chains

variable (G : GradingDatum Q)

theorem chainL_mul_e_mem_grade {s : Seq ν} {q l : ℕ} {c : I} (h : q + l < ν.card)
    (hc : IsConstOn s q (l + 1)) (hs : s.lbl ⟨q, by omega⟩ = c) :
    (chainL q l * e s : A) ∈ G.grade ν (-(l : ℤ) * G.degX c) := by
  have hmem := G.ψw_mul_pol_mul_e_mem_grade (List.range' q l) s
    (isWeightedHomogeneous_one k _)
  rw [map_one, mul_one, add_zero, degW_of_forall G (c := c)
    (fun j hj => by rw [List.mem_range'_1] at hj; omega) (fun j hj hj' => by
      rw [List.mem_range'_1] at hj
      exact ⟨(hc _ _ (by simp only; omega) (by simp only; omega) le_rfl (by simp only; omega)).trans
        hs, (hc _ _ (by simp only; omega) (by simp only; omega) le_rfl
          (by simp only; omega)).trans hs⟩), List.length_range'] at hmem
  exact hmem

theorem chainR_mul_e_mem_grade {s : Seq ν} {q l : ℕ} {c : I} (h : q + l < ν.card)
    (hc : IsConstOn s q (l + 1)) (hs : s.lbl ⟨q, by omega⟩ = c) :
    (chainR q l * e s : A) ∈ G.grade ν (-(l : ℤ) * G.degX c) := by
  have hmem := G.ψw_mul_pol_mul_e_mem_grade (List.range' q l).reverse s
    (isWeightedHomogeneous_one k _)
  rw [map_one, mul_one, add_zero, degW_of_forall G (c := c)
    (fun j hj => by rw [List.mem_reverse, List.mem_range'_1] at hj; omega) (fun j hj hj' => by
      rw [List.mem_reverse, List.mem_range'_1] at hj
      exact ⟨(hc _ _ (by simp only; omega) (by simp only; omega) le_rfl (by simp only; omega)).trans
        hs, (hc _ _ (by simp only; omega) (by simp only; omega) le_rfl
          (by simp only; omega)).trans hs⟩), List.length_reverse, List.length_range'] at hmem
  exact hmem

end Chains


variable {t : Seq ν} {p N : ℕ} {i j : I}
  (hpN : p + N < ν.card)
  (ht₀ : ∀ r : Fin ν.card, (r : ℕ) = p → t.lbl r = j)
  (ht : ∀ r : Fin ν.card, p < r → (r : ℕ) ≤ p + N → t.lbl r = i)

local notation "S" => serreSeq t p

theorem etop_eq_divIdem (a : ℕ) :
    (etop t p N a : A) = divIdem (S a) [(p, a), (p + a + 1, N - a)] := by
  simp [divIdem, blocksElt, etop, mul_assoc]

include hpN ht₀ ht in
theorem isIdempotentElem_etop {a : ℕ} (ha : a ≤ N) :
    IsIdempotentElem (etop t p N a : A) := by
  rw [etop_eq_divIdem]
  exact isIdempotentElem_divIdem (KL2.isBlocks_etop hpN ht₀ ht ha)

include hpN ht₀ ht in
theorem etop_mem_grade (G : GradingDatum Q) {a : ℕ} (ha : a ≤ N) :
    (etop t p N a : A) ∈ G.grade ν 0 := by
  rw [etop_eq_divIdem]
  exact divIdem_mem_grade G (KL2.isBlocks_etop hpN ht₀ ht ha)

theorem etop_mul_e (a : ℕ) : (etop t p N a * e (S a) : A) = etop t p N a := by
  rw [etop, mul_assoc, e_mul_self]

include hpN ht₀ ht in
theorem e_mul_etop {a : ℕ} (ha : a ≤ N) :
    (e (S a) * etop t p N a : A) = etop t p N a := by
  rw [etop, ← mul_assoc, ← mul_assoc,
    ← (commute_blockElt_left_e hpN ht₀ ht ha le_rfl le_rfl).eq,
    mul_assoc (blockElt p a),
    ← (commute_blockElt_right_e hpN ht₀ ht ha (by omega) (by omega)).eq,
    ← mul_assoc, mul_assoc _ (e _) (e _), e_mul_self]

include hpN ht₀ ht in
theorem etop_mul_aplus {a : ℕ} (ha : a + 1 ≤ N) :
    (etop t p N (a + 1) * aplus t p N a : A) = aplus t p N a := by
  rw [aplus_eq hpN ht₀ ht ha, ← mul_assoc, (isIdempotentElem_etop hpN ht₀ ht ha).eq]

include hpN ht₀ ht in
theorem etop_mul_aminus {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (etop t p N (a - 1) * aminus t p N a : A) = aminus t p N a := by
  rw [aminus_eq hpN ht₀ ht ha1 ha, ← mul_assoc,
    (isIdempotentElem_etop hpN ht₀ ht (by omega)).eq]


section Degrees

variable {C : CartanDatum I} (G : GradingDatum Q)
  (hX : ∀ c, G.degX c = C.dot c c) (hΨ : ∀ c d, G.degΨ c d = -C.dot c d)

include hpN ht₀ ht hX hΨ in
/-- The forward crossing map has one mixed crossing and `N-a-1` equal-colour crossings. -/
theorem aplus_mem_grade {a : ℕ} (ha : a + 1 ≤ N) :
    (aplus t p N a : A) ∈ G.grade ν
      (-((N - a - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j) := by
  have hL : Commute (chainL (p + a + 1) (N - a - 1) : A) (e (S a)) :=
    commute_chainL_right_e hpN ht₀ ht (by omega) (by omega) (by omega)
  have hsrc : (aplus t p N a * e (S a) : A) = aplus t p N a := by
    rw [aplus, mul_assoc, e_mul_self]
  have heq : (aplus t p N a : A) = etop t p N (a + 1) *
      ((ψ (p + a) * e (S a)) * (chainL (p + a + 1) (N - a - 1) * e (S a))) := by
    calc
      _ = aplus t p N a * e (S a) := hsrc.symm
      _ = _ := by
        rw [aplus_eq hpN ht₀ ht ha, chainL_eq_ψ_mul (by omega)]
        simp only [mul_assoc]
        rw [hL.symm.left_comm, e_mul_self]
  rw [heq, show -((N - a - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j =
    0 + (-C.dot i j + -((N - a - 1 : ℕ) : ℤ) * C.dot i i) by ring]
  refine SetLike.mul_mem_graded (etop_mem_grade hpN ht₀ ht G ha)
    (SetLike.mul_mem_graded ?_ ?_)
  · have h := G.ψ_mul_e_mem_grade (j := p + a) (by omega) (S a)
    rw [serreSeq_lbl_eq_j hpN ht₀ ht (by omega) _ rfl,
      serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega)
        (by simp only; omega) (by simp only; omega), hΨ, C.symm j i] at h
    exact h
  · have h := chainL_mul_e_mem_grade G (s := S a) (q := p + a + 1)
      (l := N - a - 1) (c := i) (by omega)
      (isConstOn_serreSeq_right hpN ht₀ ht (by omega) (by omega) (by omega))
      (serreSeq_lbl_eq_i hpN ht₀ ht (by omega) _ (by simp only; omega)
        (by simp only; omega) (by simp only; omega))
    rwa [hX] at h

include hpN ht₀ ht hX hΨ in
/-- The reverse crossing map has one mixed crossing and `a-1` equal-colour crossings. -/
theorem aminus_mem_grade {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (aminus t p N a : A) ∈ G.grade ν
      (-((a - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j) := by
  have hR : Commute (chainR p (a - 1) : A) (e (S a)) :=
    commute_chainR_left_e hpN ht₀ ht ha le_rfl (by omega)
  have hsrc : (aminus t p N a * e (S a) : A) = aminus t p N a := by
    rw [aminus, mul_assoc, e_mul_self]
  have heq : (aminus t p N a : A) = etop t p N (a - 1) *
      ((ψ (p + a - 1) * e (S a)) * (chainR p (a - 1) * e (S a))) := by
    calc
      _ = aminus t p N a * e (S a) := hsrc.symm
      _ = _ := by
        rw [aminus_eq hpN ht₀ ht ha1 ha, chainR_eq_ψ_mul ha1]
        simp only [mul_assoc]
        rw [hR.symm.left_comm, e_mul_self]
  rw [heq, show -((a - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j =
    0 + (-C.dot i j + -((a - 1 : ℕ) : ℤ) * C.dot i i) by ring]
  refine SetLike.mul_mem_graded (etop_mem_grade hpN ht₀ ht G (by omega))
    (SetLike.mul_mem_graded ?_ ?_)
  · have h := G.ψ_mul_e_mem_grade (j := p + a - 1) (by omega) (S a)
    rw [serreSeq_lbl_eq_i hpN ht₀ ht ha _ (by simp only; omega) (by simp only; omega)
      (by simp only; omega), serreSeq_lbl_eq_j hpN ht₀ ht ha _ (by simp only; omega), hΨ] at h
    exact h
  · have h := chainR_mul_e_mem_grade G (s := S a) (q := p) (l := a - 1) (c := i) (by omega)
      (isConstOn_serreSeq_left hpN ht₀ ht ha le_rfl (by omega))
      (serreSeq_lbl_eq_i hpN ht₀ ht ha _ le_rfl (by simp only; omega) (by simp only; omega))
    rwa [hX] at h

end Degrees

/-- The forward map restricted to its divided-power source idempotent. -/
def serreAp (t : Seq ν) (p N a : ℕ) : A :=
  if a + 1 ≤ N then aplus t p N a * etop t p N a else 0

/-- The reverse map restricted to its source and normalized by an invertible
leading coefficient. -/
def serreAm (u : kˣ) (t : Seq ν) (p N a : ℕ) : A :=
  if 1 ≤ a ∧ a ≤ N then (↑(u⁻¹) : k) • (aminus t p N a * etop t p N a) else 0

include hpN ht₀ ht in
theorem serreAp_mem_grade {C : CartanDatum I} (G : GradingDatum Q)
    (hX : ∀ c, G.degX c = C.dot c c) (hΨ : ∀ c d, G.degΨ c d = -C.dot c d)
    {a : ℕ} (ha : a + 1 ≤ N) :
    (serreAp t p N a : A) ∈ G.grade ν
      (-((N - a - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j) := by
  rw [serreAp, ite_eq_left ha]
  have h := SetLike.mul_mem_graded (aplus_mem_grade hpN ht₀ ht G hX hΨ ha)
    (etop_mem_grade hpN ht₀ ht G (a := a) (by omega))
  simpa only [add_zero] using h

include hpN ht₀ ht in
theorem serreAm_mem_grade {C : CartanDatum I} (G : GradingDatum Q)
    (hX : ∀ c, G.degX c = C.dot c c) (hΨ : ∀ c d, G.degΨ c d = -C.dot c d)
    (u : kˣ) {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ N) :
    (serreAm u t p N a : A) ∈ G.grade ν
      (-((a - 1 : ℕ) : ℤ) * C.dot i i - C.dot i j) := by
  rw [serreAm, ite_eq_left ⟨ha1, ha⟩]
  apply Submodule.smul_mem
  have h := SetLike.mul_mem_graded (aminus_mem_grade hpN ht₀ ht G hX hΨ ha1 ha)
    (etop_mem_grade hpN ht₀ ht G ha)
  simpa only [add_zero] using h

@[simp] theorem serreAp_of_not {a : ℕ} (ha : ¬a + 1 ≤ N) :
    (serreAp t p N a : A) = 0 := by rw [serreAp, ite_eq_right ha]

@[simp] theorem serreAm_of_not (u : kˣ) {a : ℕ} (ha : ¬(1 ≤ a ∧ a ≤ N)) :
    (serreAm u t p N a : A) = 0 := by rw [serreAm, ite_eq_right ha]

include hpN ht₀ ht in
theorem serreAp_mul_etop (a : ℕ) :
    (serreAp t p N a * etop t p N a : A) = serreAp t p N a := by
  by_cases ha : a + 1 ≤ N
  · rw [serreAp, ite_eq_left ha, mul_assoc,
      (isIdempotentElem_etop hpN ht₀ ht (a := a) (by omega)).eq]
  · rw [serreAp_of_not ha, zero_mul]

include hpN ht₀ ht in
theorem etop_mul_serreAp (a : ℕ) :
    (etop t p N (a + 1) * serreAp t p N a : A) = serreAp t p N a := by
  by_cases ha : a + 1 ≤ N
  · rw [serreAp, ite_eq_left ha, ← mul_assoc, etop_mul_aplus hpN ht₀ ht ha]
  · rw [serreAp_of_not ha, mul_zero]

include hpN ht₀ ht in
theorem serreAm_mul_etop (u : kˣ) (a : ℕ) :
    (serreAm u t p N a * etop t p N a : A) = serreAm u t p N a := by
  by_cases ha : 1 ≤ a ∧ a ≤ N
  · rw [serreAm, ite_eq_left ha, smul_mul_assoc, mul_assoc,
      (isIdempotentElem_etop hpN ht₀ ht ha.2).eq]
  · rw [serreAm_of_not u ha, zero_mul]

include hpN ht₀ ht in
theorem etop_mul_serreAm (u : kˣ) (a : ℕ) :
    (etop t p N (a - 1) * serreAm u t p N a : A) = serreAm u t p N a := by
  by_cases ha : 1 ≤ a ∧ a ≤ N
  · rw [serreAm, ite_eq_left ha, mul_smul_comm, ← mul_assoc,
      etop_mul_aminus hpN ht₀ ht ha.1 ha.2]
  · rw [serreAm_of_not u ha, mul_zero]

include hpN ht₀ ht in
/-- Consecutive restricted forward arrows compose to zero. -/
theorem serreAp_succ_mul_serreAp (hij : i ≠ j) (a : ℕ) :
    (serreAp t p N (a + 1) * serreAp t p N a : A) = 0 := by
  by_cases ha : a + 2 ≤ N
  · rw [serreAp, serreAp, ite_eq_left (show a + 1 + 1 ≤ N by omega),
      ite_eq_left (show a + 1 ≤ N by omega), mul_assoc,
      ← mul_assoc (etop t p N (a + 1)), etop_mul_aplus hpN ht₀ ht (by omega),
      ← mul_assoc, serre_Dplus hpN ht₀ ht hij ha, zero_mul]
  · rw [serreAp_of_not (show ¬a + 1 + 1 ≤ N by omega), zero_mul]

include hpN ht₀ ht in
/-- Consecutive normalized restricted reverse arrows compose to zero. -/
theorem serreAm_mul_serreAm_succ (hij : i ≠ j) (u : kˣ) (a : ℕ) :
    (serreAm u t p N a * serreAm u t p N (a + 1) : A) = 0 := by
  by_cases ha0 : 1 ≤ a
  · by_cases haN : a + 1 ≤ N
    · rw [serreAm, serreAm, ite_eq_left ⟨ha0, by omega⟩,
        ite_eq_left ⟨by omega, haN⟩, smul_mul_smul_comm, mul_assoc,
        ← mul_assoc (etop t p N a)]
      have he := etop_mul_aminus (k := k) (Q := Q) hpN ht₀ ht
        (a := a + 1) (by omega) haN
      rw [show a + 1 - 1 = a by omega] at he
      have hz := serre_Dminus (k := k) (Q := Q) hpN ht₀ ht hij
        (a := a + 1) (by omega) haN
      simp only [Nat.add_sub_cancel] at hz
      rw [he, ← mul_assoc, hz, zero_mul, smul_zero]
    · rw [serreAm_of_not u (show ¬(1 ≤ a + 1 ∧ a + 1 ≤ N) by omega), mul_zero]
  · rw [serreAm_of_not u (show ¬(1 ≤ a ∧ a ≤ N) by omega), zero_mul]

end Categorification.KLR.Rouquier
