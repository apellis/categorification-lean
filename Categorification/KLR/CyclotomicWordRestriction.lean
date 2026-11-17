/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicRepresentation

/-!
# Cyclotomic restriction of a sequence projective by deletion of a letter

Hu–Shi, arXiv:2108.05508v5, §3, Proposition 3.3 and Theorem 1.1.
On the integral projective Grothendieck group, commuting a raising operator
through a string of lowerings gives one term for each possible removal of
its colour. The quantum integer depends on the prefix before that occurrence.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot
open LieLean.QuantumGroup

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
    {C : CartanDatum I} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (RD : WeightDatum C X Y)
    (highest : X) (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest)

local notation "G" => hP.gradingDatum
local notation "LP" => LaurentPolynomial ℤ
local notation "ι" => DirectSum.lof LP _ (fun ν => K0 (grade G Λ ν))
local notation "raising" => fun i => raise G Λ i hP.klrSymm hP.polyInY_leading C
local notation "lowering" => lower G Λ

/-- A choice of position in a word, recorded by the prefix, label and suffix.
Repeated equal labels give separate entries. -/
def markedWords : List I → List (List I × I × List I)
  | [] => []
  | a::w => ([],a,w) :: (markedWords w).map (fun t => (a::t.1,t.2))

omit [DecidableEq I] in
private theorem markedWords_append (w : List I) (a : I) :
    markedWords (w++[a]) = (markedWords w).map (fun t => (t.1,t.2.1,t.2.2++[a])) ++ [(w,a,[])] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [markedWords,ih,List.map_map,Function.comp_def]

/-- The coroot pairing after the prefix `w`, equal to the integer associated
to the identity permutation in Hu–Shi, Definition 3.2, at the next position. -/
def prefixPair (C : CartanDatum I) (Λ : I → ℕ) (i : I) (w : List I) : ℤ :=
  Λ i - (w.map (A C i)).sum

/-- The class of the ordinary sequence projective in the total projective lattice. -/
def sequenceClass (w : List I) : projectiveK0 G Λ :=
  totalQuotientK0 G Λ ((G).clsW w)

private theorem sequenceClass_lof (w : List I) :
    sequenceClass hP Λ w = ι (w : Multiset I)
      (quotientK0 G Λ (w : Multiset I) (K0.of ((G).projP (Seq.ofList w rfl)))) :=
  totalQuotientK0_lof ..

theorem sequenceClass_append (w : List I) (i : I) :
    sequenceClass hP Λ (w++[i]) = lowering i (sequenceClass hP Λ w) := by
  rw [sequenceClass,sequenceClass,(G).clsW_append,
    lower_totalQuotientK0 G Λ i hP.klrSymm C.dot_self_pos]

include hΛ in
private theorem commute_on_word (i j : I) (w : List I) :
    raising i (lowering j (sequenceClass hP Λ w)) = lowering j (raising i (sequenceClass hP Λ w)) +
      if i = j then qIntU (qUnitLP ^ di C i) (prefixPair C Λ i w) • sequenceClass hP Λ w else 0 := by
  by_cases hij : i = j
  · subst j
    rw [sequenceClass_lof]
    have h := raise_lower_sub_lower_raise G Λ i (w : Multiset I) hP.klrSymm hP.polyInY_leading
      RD highest (hΛ i) (hP.polyInY_degree_pair RD i) (two_mul_di C i).symm
      (quotientK0 G Λ _ (K0.of ((G).projP (Seq.ofList w rfl))))
    rw [pair_sub_content Λ i _ RD highest (hΛ i),sub_eq_iff_eq_add] at h
    simpa only [↓reduceIte,add_comm,prefixPair,Multiset.map_coe,Multiset.sum_coe] using h
  · simp only [hij,↓reduceIte,add_zero]
    exact DFunLike.congr_fun (raise_lower_commute_of_ne G Λ i j hP.klrSymm hP.polyInY_leading
      C hij rfl).eq (sequenceClass hP Λ w)

include hΛ in
/-- Normalized restriction of a sequence projective, over the integral Laurent
ring. Every matching occurrence of the removed label contributes its prefix
quantum integer times the class with just that occurrence deleted. -/
theorem raise_sequenceClass (i : I) (w : List I) :
    raising i (sequenceClass hP Λ w) = ((markedWords w).map (fun t =>
      if i = t.2.1 then qIntU (qUnitLP ^ di C i) (prefixPair C Λ i t.1) •
        sequenceClass hP Λ (t.1 ++ t.2.2) else 0)).sum := by
  induction w using List.reverseRecOn with
  | nil =>
    rw [sequenceClass_lof,raise_lof_of_notMem (h := by simp)]
    rfl
  | append_singleton w j ih =>
    rw [sequenceClass_append,commute_on_word hP Λ RD highest hΛ,ih,markedWords_append,
      List.map_append,List.sum_append,List.map_singleton,List.sum_singleton,List.map_map]
    congr 1
    · rw [map_list_sum]
      simp only [List.map_map,Function.comp_def]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t _
      split_ifs <;> simp only [map_smul,map_zero,←List.append_assoc, sequenceClass_append]
    · simp

end Categorification.KLR.CycKLR
