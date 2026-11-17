/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.Serre
import Categorification.WeightedKLR.GradedK0.SpacedClasses

/-!
# Quantum Serre relations in the weighted Grothendieck algebra

The divided-power Serre relation needed for the natural map in Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap (C). The alternating relation on weighted loading projectives
comes from the transported Rouquier zigzag (arXiv:0812.5023v1, §4.1.1,
Proposition 4.2). The divided-power shifts are those of KL II,
arXiv:0804.2080v1, §3, Proposition 6 and Corollary 7. Over a field, concatenation
of divided-power loading classes is multiplication in graded projective `K₀`.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded Categorification.KLR Categorification.KLR.KL2
  Categorification.KLR.KL2Gamma KLRAlgebra LaurentPolynomial _root_.Finset

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  (hS : Γ.Standing) (hD : Γ.Dagger) (hne : ∀ e, Γ.head e ≠ Γ.tail e)
  (hl : ∀ i, Γ.loop i = none)

local notation "G" => hS.gradingDatum
local notation "C" => hS.cartanDatum

/-- The normalized alternating Serre relation among divided-power loading classes,
over every commutative coefficient ring. -/
theorem spacedClsDiv_serre {i j : I} (hij : i ≠ j) :
    ∑ a ∈ range ((C).serreN i j + 1), ((-1 : LaurentPolynomial ℤ) ^ a) •
      spacedClsDiv hS hD hne hl [(i, a), (j, 1), (i, (C).serreN i j - a)] = 0 := by
  classical
  let N := (C).serreN i j
  have hN : N = (C).dij i j + 1 := serreN_eq_dij hij
  let d : ℕ → List (I × ℕ) := fun a => [(i, a), (j, 1), (i, N - a)]
  let ν : Multiset I := (j :: List.replicate N i : List I)
  have hm : ν.card = N + 1 := by simp [ν]
  have hexp (a : ℕ) : expandDiv (d a) = List.replicate a i ++ j :: List.replicate (N - a) i := by
    simp [d, expandDiv]
  have hν (a : ℕ) (ha : a ≤ N) : (expandDiv (d a) : Multiset I) = ν := by
    rw [hexp]
    apply Multiset.coe_eq_coe.2
    refine List.perm_middle.trans ?_
    rw [← List.replicate_add, show a + (N - a) = N by omega]
  let t : Seq ν := KLRAlgebra.Seq.ofList (j :: List.replicate N i) rfl
  have hpN : 0 + N < ν.card := by omega
  have htlabel (r : Fin ν.card) : t.lbl r = if (r : ℕ) = 0 then j else i := by
    change (KLRAlgebra.Seq.ofList (List.replicate 0 i ++ j :: List.replicate N i) rfl).lbl r = _
    rw [KLRAlgebra.Seq.ofList_lbl, getElem_midL]
  have ht₀ : ∀ r : Fin ν.card, (r : ℕ) = 0 → t.lbl r = j := by
    intro r hr
    rw [htlabel, ite_eq_left hr]
  have ht : ∀ r : Fin ν.card, (0 : ℕ) < r → (r : ℕ) ≤ 0 + N → t.lbl r = i := by
    intro r hr _
    rw [htlabel, ite_eq_right (by omega)]
  have hSeq (a : ℕ) (ha : a ≤ N) : serreSeq t 0 a = KLRAlgebra.Seq.ofList (expandDiv (d a)) (hν a ha) := by
    apply Subtype.ext
    funext r
    change (serreSeq t 0 a).lbl r = (KLRAlgebra.Seq.ofList (expandDiv (d a)) (hν a ha)).lbl r
    rw [lbl_serreSeq hpN ht₀ ht ha r, KLRAlgebra.Seq.ofList_lbl]
    have hr : (r : ℕ) ≤ N := by have := r.2; omega
    simp only [zero_add, Nat.zero_le, hr, and_self, ite_true]
    have he := getElem_midL i j a (N - a) (r : ℕ) (by
      simp only [List.length_append, List.length_replicate, List.length_cons]
      omega)
    simpa only [hexp a, KLRAlgebra.Seq.ofList_lbl] using he.symm
  have hIdem (a : ℕ) :
      (divIdem (serreSeq t 0 a) (blocksDiv (d a) 0) : KLRAlgebra k Γ.klrQ ν) =
        divIdem (serreSeq t 0 a) [(0, a), (a + 1, N - a)] := by
    rw [← divIdem_bigBlocks _ (blocksDiv (d a) 0),
      ← divIdem_bigBlocks _ [(0, a), (a + 1, N - a)]]
    congr 1
    by_cases h1 : 2 ≤ a <;> by_cases h2 : 2 ≤ N - a <;>
      simp [d, blocksDiv, bigBlocks, h1, h2]
  let sh : ℕ → ℤ := fun a => divAngle2 C (d a)
  have hshform (a : ℕ) : sh a = (C).dot i i / 2 * ((a.choose 2 : ℕ) + ((N - a).choose 2 : ℕ) : ℤ) := by
    simpa only [sh, d, List.nil_append, List.append_nil, divAngle2, List.map_nil, List.sum_nil, zero_add]
      using divAngle2_serre C [] [] i j a (N - a)
  have hsh : ∀ a, a < N → sh (a + 1) = sh a +
      (-((N - a - 1 : ℕ) : ℤ) * (C).dot i i - (C).dot i j) := by
    intro a ha
    rw [hshform, hshform]
    have e1 : ((a + 1).choose 2 : ℤ) = (a.choose 2 : ℕ) + a := by
      rw [NilHecke.choose_two_succ]; push_cast; ring
    have e2 : ((N - a).choose 2 : ℤ) = ((N - (a + 1)).choose 2 : ℕ) + ((N - a - 1 : ℕ) : ℤ) := by
      rw [show N - a = (N - (a + 1)) + 1 by omega, NilHecke.choose_two_succ]
      push_cast
      rw [show N - (a + 1) = N - a - 1 by omega]
    have e3 : ((N - a - 1 : ℕ) : ℤ) = N - a - 1 := by omega
    obtain ⟨r, hr⟩ := (C).dot_self_even i
    have e4 : (C).dot i i / 2 = r := by omega
    have e5 := (C).two_mul_dot_eq hij
    change 2 * (C).dot i j = (C).dot i i * (1 - (N : ℤ)) at e5
    rw [e1, e2, e3, e4]
    rw [hr] at e5 ⊢
    have e6 : (C).dot i j = r * (1 - N) := by linarith
    linear_combination e6
  let P : ℕ → K0 ((G).klrGrade ν.toFinsupp) := fun a => if ha : a ≤ N then
    K0.of ((G).spacedProjFlip hS hD hne hl (serreSeq t 0 a)
      [(0, a), (0 + a + 1, N - a)] (isBlocks_etop hpN ht₀ ht ha)) else 0
  have hP : ∀ a (ha : a ≤ N), P a = K0.of ((G).spacedProjFlip hS hD hne hl (serreSeq t 0 a)
      [(0, a), (0 + a + 1, N - a)] (isBlocks_etop hpN ht₀ ht ha)) := fun _ ha => dite_eq_left ha
  have hclass (a : ℕ) (ha : a ≤ N) :
      K0.of ((G).spacedProjFlip hS hD hne hl (KLRAlgebra.Seq.ofList (expandDiv (d a)) (hν a ha))
        (blocksDiv (d a) 0) (isBlocks_ofList (d a) (hν a ha))) = P a := by
    rw [hP a ha]
    apply K0.of_ofIdempotent_congr
    rw [← hSeq a ha]
    simpa only [Nat.zero_add, Function.comp_apply] using
      congrArg (spacedEntryMap hS hD hne hl (serreSeq t 0 a) (serreSeq t 0 a) ∘ hflip) (hIdem a)
  have key : ∀ a ∈ range (N + 1), ((-1 : LaurentPolynomial ℤ) ^ a) •
      spacedClsDiv hS hD hne hl (d a) = DirectSum.of (G).K0fam ν.toFinsupp
        (((-1 : LaurentPolynomial ℤ) ^ a * T (-sh a)) • P a) := by
    intro a ha'
    have ha : a ≤ N := by rw [mem_range] at ha'; omega
    rw [spacedClsDiv_eq hS hD hne hl (d a) (hν a ha), spacedProjDiv,
      ← K0.T_smul_of, hclass a ha, ← (G).K0W_of_smul, mul_smul]
  change ∑ a ∈ range (N + 1), ((-1 : LaurentPolynomial ℤ) ^ a) •
    spacedClsDiv hS hD hne hl (d a) = 0
  rw [sum_congr rfl key, ← map_sum, K0_serre_window hS hD hne hl hpN ht₀ ht hij hN sh hsh P hP,
    map_zero]

end Categorification.WeightedKLR.GradingDatum

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded Categorification.KLR LaurentPolynomial _root_.Finset

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  (hS : Γ.Standing) (hD : Γ.Dagger) (hne : ∀ e, Γ.head e ≠ Γ.tail e)
  (hl : ∀ i, Γ.loop i = none)

local notation "C" => hS.cartanDatum

/-- The divided-power quantum Serre relation expressed in the multiplication of the
weighted Grothendieck algebra. The standing grading supplies all needed graded dimensions. -/
theorem spacedClsDiv_serre_mul {i j : I} (hij : i ≠ j) :
    ∑ a ∈ range ((C).serreN i j + 1), ((-1 : LaurentPolynomial ℤ) ^ a) •
      (spacedClsDiv hS hD hne hl [(i, a)] * spacedClsDiv hS hD hne hl [(j, 1)] *
        spacedClsDiv hS hD hne hl [(i, (C).serreN i j - a)]) = 0 := by
  simpa only [← spacedClsDiv_append, List.cons_append, List.nil_append] using
    spacedClsDiv_serre hS hD hne hl hij

end Categorification.WeightedKLR.GradingDatum
