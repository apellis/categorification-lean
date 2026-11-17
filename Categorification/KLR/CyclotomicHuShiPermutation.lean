/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicHuShi
import Mathlib.GroupTheory.Perm.Fin

/-!
# Hu–Shi's permutation formula for cyclotomic corners

Hu–Shi, arXiv:2108.05508v5, Theorem 1.1 and Definition 3.2. The matching
permutation sends each position in the source sequence to its position in
the target sequence. Removing its last source position gives the recursion
for the graded Hom polynomial.
-/

noncomputable section
namespace Categorification.KLR.CycKLR
open QuantumGroup QuantumGroup.UDot LieLean.QuantumGroup Equiv
local notation "LP" => LaurentPolynomial ℤ
local notation "T" => LaurentPolynomial.T (R := ℤ)

variable {I : Type*} {n : ℕ}

/-- Hu–Shi's integer N^Λ(w,ν,t) (Definition 3.2). Only earlier positions
whose images also precede the image of t contribute to the coroot pairing. -/
def huShiN (C : CartanDatum I) (Λ : I → ℕ) (s : Fin n → I) (w : Perm (Fin n)) (i : Fin n) : ℤ :=
  Λ (s i) - ∑ j, if j < i ∧ w j < w i then A C (s i) (s j) else 0

private def insertLast (p : Fin (n+1)) (w : Perm (Fin n)) : Perm (Fin (n+1)) :=
  Equiv.ofBijective (Fin.lastCases (motive := fun _ => Fin (n+1)) p (fun j => p.succAbove (w j))) (by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨?_,rfl⟩
    intro j k
    induction j using Fin.lastCases <;> induction k using Fin.lastCases <;>
      simp [Fin.succAbove_ne,Ne.symm (Fin.succAbove_ne _ _),Fin.succAbove_right_injective.eq_iff])

private theorem insert_last (p : Fin (n+1)) (w : Perm (Fin n)) :
    insertLast p w (Fin.last n) = p := by simp [insertLast]
private theorem insert_cast (p : Fin (n+1)) (w : Perm (Fin n)) (i : Fin n) :
    insertLast p w i.castSucc = p.succAbove (w i) := by simp [insertLast]

private def permChoices (n : ℕ) : Fin (n+1) × Perm (Fin n) ≃ Perm (Fin (n+1)) :=
  Equiv.ofBijective (fun z => insertLast z.1 z.2) (by
    rw [Nat.bijective_iff_injective_and_card]
    constructor
    · rintro ⟨p,v⟩ ⟨q,w⟩ he
      have hp := DFunLike.congr_fun he (Fin.last n)
      simp only [insert_last] at hp
      subst q
      congr 1
      ext j : 1
      exact Fin.succAbove_right_injective (by simpa only [insert_cast] using DFunLike.congr_fun he j.castSucc)
    · rw [Nat.card_prod,Nat.card_perm,Nat.card_perm,Nat.card_eq_fintype_card,
        Nat.card_eq_fintype_card,Fintype.card_fin,Fintype.card_fin,Nat.factorial_succ])

private theorem marked_sum (n : ℕ) (t : Fin (n+1) → I) (f : List I → I → List I → LP) :
    ((markedWords (List.ofFn t)).map (fun z => f z.1 z.2.1 (z.1 ++ z.2.2))).sum =
      ∑ p : Fin (n+1), f ((List.ofFn t).take p.val) (t p) (List.ofFn (p.removeNth t)) := by
  induction n generalizing f with
  | zero => simp [List.ofFn_succ,markedWords]
  | succ n ih =>
    rw [Fin.sum_univ_succ,List.ofFn_succ]
    simp only [markedWords,List.map_cons,List.sum_cons,List.nil_append,Fin.val_zero,List.take_zero,
      Fin.removeNth_zero,List.map_map,Function.comp_def]
    apply congrArg₂ (·+·) rfl
    have H := ih (fun j => t j.succ) (fun pre a rem => f (t 0::pre) a (t 0::rem))
    simp only [List.cons_append] at *
    rw [H]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.val_succ,List.take_succ_cons]
    congr 1
    rw [List.ofFn_succ]
    simp only [Fin.removeNth_apply,Fin.succ_succAbove_zero,Fin.succ_succAbove_succ]
    rfl

private theorem lastPair (C : CartanDatum I) (Λ : I → ℕ) (s t : Fin (n+1) → I)
    (w : Perm (Fin (n+1))) (h : ∀ j, s j = t (w j)) :
    huShiN C Λ s w (Fin.last n) = prefixPair C Λ (s (Fin.last n))
      ((List.ofFn t).take (w (Fin.last n)).val) := by
  rw [huShiN,prefixPair,List.map_take,List.map_ofFn,List.sum_take_ofFn,Finset.sum_filter]
  congr 1
  simp only [Function.comp_apply]
  rw [← Equiv.sum_comp w (fun j : Fin (n+1) => if j.val < (w (Fin.last n)).val then A C (s (Fin.last n)) (t j) else 0)]
  apply Finset.sum_congr rfl
  intro j _
  induction j using Fin.lastCases with
  | last => simp
  | cast i => simp only [Fin.castSucc_lt_last,true_and,h i.castSucc]; rfl

private theorem initN (C : CartanDatum I) (Λ : I → ℕ) (s : Fin (n+1) → I)
    (w : Perm (Fin n)) (p : Fin (n+1)) (i : Fin n) :
    huShiN C Λ s (insertLast p w) i.castSucc = huShiN C Λ (fun j => s j.castSucc) w i := by
  simp only [huShiN,Fin.sum_univ_castSucc,not_lt_of_gt (Fin.castSucc_lt_last i), false_and, ↓reduceIte,
    add_zero,insert_cast,Fin.succAbove_lt_succAbove_iff,Fin.castSucc_lt_castSucc_iff]

private theorem initId (C : CartanDatum I) (Λ : I → ℕ) (s : Fin (n+1) → I) (i : Fin n) :
    huShiN C Λ s 1 i.castSucc = huShiN C Λ (fun j => s j.castSucc) 1 i := by
  simp only [huShiN,Perm.one_apply,and_self,Fin.sum_univ_castSucc,not_lt_of_gt (Fin.castSucc_lt_last i), ↓reduceIte,
    add_zero,Fin.castSucc_lt_castSucc_iff]

private theorem lastId (C : CartanDatum I) (Λ : I → ℕ) (s : Fin (n+1) → I) :
    huShiN C Λ s 1 (Fin.last n) = prefixPair C Λ (s (Fin.last n)) (List.ofFn fun j : Fin n => s j.castSucc) := by
  simp only [huShiN,Perm.one_apply,and_self,Fin.sum_univ_castSucc,lt_irrefl,↓reduceIte,
    add_zero,Fin.castSucc_lt_last,prefixPair,List.map_ofFn,List.sum_ofFn,Function.comp_def]

variable [DecidableEq I]

private def permTerm (C : CartanDatum I) (Λ : I → ℕ) (s t : Fin n → I) (w : Perm (Fin n)) : LP :=
  if ∀ j, s j = t (w j) then ∏ j, T (di C (s j) * (huShiN C Λ s 1 j - 1)) *
    qIntU (qUnitLP ^ di C (s j)) (huShiN C Λ s w j) else 0

private theorem term_insert (C : CartanDatum I) (Λ : I → ℕ) (s t : Fin (n+1) → I)
    (p : Fin (n+1)) (w : Perm (Fin n)) :
    permTerm C Λ s t (insertLast p w) = T (di C (s (Fin.last n)) *
      (prefixPair C Λ (s (Fin.last n)) (List.ofFn fun j : Fin n => s j.castSucc) - 1)) *
      (if s (Fin.last n) = t p then qIntU (qUnitLP ^ di C (s (Fin.last n)))
        (prefixPair C Λ (s (Fin.last n)) ((List.ofFn t).take p.val)) *
        permTerm C Λ (fun j => s j.castSucc) (p.removeNth t) w else 0) := by
  by_cases h : ∀ j, s j = t (insertLast p w j)
  · have hh := Fin.forall_fin_succ'.1 h
    simp only [insert_cast,insert_last] at hh
    rw [permTerm,ite_eq_left h,ite_eq_left hh.2,permTerm,ite_eq_left (show ∀ j, s j.castSucc = p.removeNth t (w j) from hh.1),Fin.prod_univ_castSucc,
      lastId,lastPair C Λ s t _ h,insert_last]
    simp only [initId,initN]
    ring
  · rw [permTerm,ite_eq_right h]
    by_cases hp : s (Fin.last n) = t p
    · have hr : ¬ ∀ j : Fin n, s j.castSucc = p.removeNth t (w j) := by
        intro hh
        apply h
        exact Fin.forall_fin_succ'.2 ⟨fun j => by rw [insert_cast]; exact hh j,by rw [insert_last]; exact hp⟩
      rw [ite_eq_left hp,permTerm,ite_eq_right hr,mul_zero,mul_zero]
    · rw [ite_eq_right hp,mul_zero]

private theorem sum_perm (C : CartanDatum I) (Λ : I → ℕ) (n : ℕ) (s t : Fin n → I) :
    huShiPolynomial C Λ (List.ofFn s) (List.ofFn t) = ∑ w, permTerm C Λ s t w := by
  induction n with
  | zero => simp [huShiPolynomial,huShiFromRight,permTerm]
  | succ n ih =>
    rw [← (permChoices n).sum_comp (permTerm C Λ s t),Fintype.sum_prod_type]
    change _ = ∑ p, ∑ w, permTerm C Λ s t (insertLast p w)
    simp_rw [term_insert,← Finset.mul_sum]
    rw [huShiPolynomial,List.ofFn_succ_last (f := s),List.reverse_append,
      List.reverse_singleton,List.singleton_append,huShiFromRight,List.reverse_reverse]
    rw [marked_sum n t (fun pre c rem => if s (Fin.last n) = c then
      qIntU (qUnitLP ^ di C (s (Fin.last n))) (prefixPair C Λ (s (Fin.last n)) pre) *
        huShiFromRight C Λ (List.ofFn fun j : Fin n => s j.castSucc).reverse rem else 0)]
    apply congrArg (_ * ·)
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp only [Finset.sum_const_zero,← Finset.mul_sum]
    rw [← ih]
    rfl

/-- Hu–Shi, arXiv:2108.05508v5, Theorem 1.1. The Laurent polynomial for the
graded sequence corner is the sum over matching permutations of the products
of the signed quantum integers and the source-prefix grading shifts. -/
theorem huShiPolynomial_eq_sum_permutations (C : CartanDatum I) (Λ : I → ℕ) (s t : Fin n → I) :
    huShiPolynomial C Λ (List.ofFn s) (List.ofFn t) =
      ∑ w : Perm (Fin n) with ∀ j, s j = t (w j),
        ∏ j, T (di C (s j) * (huShiN C Λ s 1 j - 1)) *
          qIntU (qUnitLP ^ di C (s j)) (huShiN C Λ s w j) := by
  rw [sum_perm,Finset.sum_filter]
  rfl

/-- Hu–Shi, arXiv:2108.05508v5, Theorem 1.1 in each homogeneous degree,
for arbitrary pairs of sequences and homogeneous Rouquier parameters. -/
theorem finrank_cornerGrade_permutationFormula {k : Type*} [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {β : Multiset I} (s t : Seq β) (d : ℤ) :
    (Module.finrank k ↥(grade hP.gradingDatum Λ β d ⊓
      corner k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ j) s t) : ℤ) =
      (∑ w : Perm (Fin β.card) with ∀ j, s.1 j = t.1 (w j),
        ∏ j, T (di C (s.1 j) * (huShiN C Λ s.1 1 j - 1)) *
          qIntU (qUnitLP ^ di C (s.1 j)) (huShiN C Λ s.1 w j)).coeff d := by
  rw [finrank_cornerGrade_huShi hP Λ s t,huShiPolynomial_eq_sum_permutations]

/-- The graded dimension polynomial of the cyclotomic corner, in the form of
Hu–Shi, arXiv:2108.05508v5, Theorem 1.1. -/
theorem gdimPoly_corner_permutationFormula {k : Type*} [Field k] {C : CartanDatum I}
    {Q : I → I → MvPolynomial (Fin 2) k} (hP : IsRouquierQ C Q) (Λ : I → ℕ)
    {β : Multiset I} (s t : Seq β) :
    Graded.gdimPoly (fun d => grade hP.gradingDatum Λ β d ⊓
      corner k Q (fun j => (Polynomial.X : Polynomial k) ^ Λ j) s t) =
      ∑ w : Perm (Fin β.card) with ∀ j, s.1 j = t.1 (w j),
        ∏ j, T (di C (s.1 j) * (huShiN C Λ s.1 1 j - 1)) *
          qIntU (qUnitLP ^ di C (s.1 j)) (huShiN C Λ s.1 w j) := by
  let H := fun d => grade hP.gradingDatum Λ β d ⊓
    corner k Q (fun j => (Polynomial.X : Polynomial k)^Λ j) s t
  have h : (fun d => (Module.finrank k (H d) : ℤ)) =
      (huShiPolynomial C Λ (List.ofFn s.1) (List.ofFn t.1)).coeff := by
    funext d
    exact finrank_cornerGrade_huShi hP Λ s t d
  change Graded.gdimPoly H = _
  rw [← huShiPolynomial_eq_sum_permutations]
  have hfin : (Function.support (fun d => (Module.finrank k (H d) : ℤ))).Finite := by
    rw [h]
    exact Finsupp.hasFiniteSupport _
  ext d
  simp only [Graded.gdimPoly,dite_eq_left hfin,AddMonoidAlgebra.coeff_ofCoeff,Finsupp.ofSupportFinite_coe]
  exact congrFun h d

end Categorification.KLR.CycKLR
