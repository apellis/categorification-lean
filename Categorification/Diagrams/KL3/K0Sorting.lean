/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.K0Relations

/-!
# Sorting signed sequences in `K₀(U̇)` (the `K₀`-shadow of KL III Lemma 3.38)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.8.4,
Lemma 3.38 and its proof: "If `i = i' -i +j i''` […] then `P` is a direct summand of `E_i 1_λ {t}`
if and only if it is a direct summand of `E_{i' +j -i i''} 1_λ {t}`. Indeed, these two
1-morphisms are either isomorphic (if `i ≠ j`) or differ by direct summands `E_{i' i''} 1_λ {t'}`
[…]. Moving all positive terms of `i` to the left of all negative terms produces a sequence
`j (-j')` […]."

The module-level statement (about indecomposable summands and their width) needs the
Krull–Schmidt property of `U̇(λ, μ)`, which rests on the finite-dimensionality of its graded Hom
spaces (KL III §3.2) and is not formalized. We prove the corresponding statement for classes:

* `eC_mem_span_sorted`: for every signed sequence `w`, `[E_w 1_λ]` lies in the
  `ℤ[q, q⁻¹]`-span of the classes `[E_{(+s)(-t)} 1_λ]` of *sorted* sequences (all `+` letters to
  the left of all `-` letters) of length at most the length of `w`, with the same parity.

In particular the classes `[E_{+ν, -ν'} 1_λ]` span the image of the free algebra `'U 1_λ` under
`E_w 1_λ ↦ [E_w 1_λ]`.

The proof sorts `w` by adjacent transpositions `(-j)(+i) ↦ (+i)(-j)`, using Propositions 3.25
and 3.26 in `K₀` (`eC_EF`, `eC_FE`, `eC_ij`): each transposition changes the class by a multiple
of the class of a sequence shorter by two.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Categorification.GradedBicat
  LaurentPolynomial

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y} {k : Type w} [CommRing k]

/-! ## Inversions of signed sequences -/

/-- The number of `+` letters of a signed sequence. -/
def nUp (w : List (Letter I)) : ℕ := (w.filter fun l => l.1).length

/-- The number of inversions of a signed sequence: pairs (a `-` letter, a `+` letter to its
right). -/
def nInv : List (Letter I) → ℕ
  | [] => 0
  | l :: w => (if l.1 then 0 else nUp w) + nInv w

/-- A signed sequence is *sorted* if all its `+` letters are to the left of its `-` letters. -/
def IsSorted (w : List (Letter I)) : Prop := ∃ s t : List I, w = ups s ++ t.map dn

theorem nUp_append (a b : List (Letter I)) : nUp (a ++ b) = nUp a + nUp b := by
  simp [nUp, List.filter_append]

theorem nUp_cons (l : Letter I) (w : List (Letter I)) :
    nUp (l :: w) = (if l.1 then 1 else 0) + nUp w := by
  cases h : l.1 <;> simp [nUp, List.filter_cons, h, add_comm]

/-- The number of `-` letters of a signed sequence. -/
def nDn (w : List (Letter I)) : ℕ := (w.filter fun l => !l.1).length

theorem nDn_cons (l : Letter I) (w : List (Letter I)) :
    nDn (l :: w) = (if l.1 then 0 else 1) + nDn w := by
  cases h : l.1 <;> simp [nDn, List.filter_cons, h, add_comm]

theorem nInv_append (a w : List (Letter I)) :
    nInv (a ++ w) = nInv a + nInv w + nDn a * nUp w := by
  induction a with
  | nil => simp [nInv, nDn]
  | cons l a ih =>
    simp only [List.cons_append, nInv, ih, nUp_append, nDn_cons]
    split_ifs <;> ring

/-- Swapping an adjacent pair `(-j)(+i)` removes exactly one inversion. -/
theorem nInv_swap (a b : List (Letter I)) (i j : I) :
    nInv (a ++ (false, j) :: (true, i) :: b) = nInv (a ++ (true, i) :: (false, j) :: b) + 1 := by
  rw [nInv_append, nInv_append]
  simp only [nInv, nUp_cons, if_true, Bool.false_eq_true, if_false]
  ring

theorem nInv_le_of_remove (a b : List (Letter I)) (i j : I) :
    nInv (a ++ b) ≤ nInv (a ++ (true, i) :: (false, j) :: b) := by
  rw [nInv_append, nInv_append]
  simp only [nInv, nUp_cons, if_true, Bool.false_eq_true, if_false]
  have := Nat.mul_le_mul_left (nDn a) (show nUp b ≤ 1 + (0 + nUp b) by omega)
  omega

/-- A sequence with no adjacent pair `(-j)(+i)` is sorted. -/
theorem isSorted_or_exists_swap (w : List (Letter I)) :
    IsSorted w ∨ ∃ a b i j, w = a ++ (false, j) :: (true, i) :: b := by
  induction w with
  | nil => exact Or.inl ⟨[], [], rfl⟩
  | cons l w ih =>
    rcases ih with ⟨s, t, rfl⟩ | ⟨a, b, i, j, rfl⟩
    · obtain ⟨ε, c⟩ := l
      cases ε
      · cases s with
        | nil => exact Or.inl ⟨[], c :: t, rfl⟩
        | cons s₀ s =>
          exact Or.inr ⟨[], ups s ++ t.map dn, s₀, c, rfl⟩
      · exact Or.inl ⟨c :: s, t, rfl⟩
    · exact Or.inr ⟨l :: a, b, i, j, rfl⟩

/-! ## The sorting lemma in `K₀` -/

variable (RD k)

/-- The `ℤ[q, q⁻¹]`-span of the classes of sorted sequences of length at most `m` and length
congruent to `m` modulo `2`, in `K₀(U̇(λ, ρ))`. -/
def sortedSpan (ρ lam : X) (m : ℕ) : Submodule (LaurentPolynomial ℤ) (K0Kar RD k ρ lam) :=
  Submodule.span _ {x | ∃ (w : List (Letter I)) (h : wt RD lam w = ρ),
    IsSorted w ∧ w.length ≤ m ∧ w.length % 2 = m % 2 ∧ x = eC RD k ρ lam w h}

variable {RD k}

theorem sortedSpan_mono {ρ lam : X} {m m' : ℕ} (h : m ≤ m') (hp : m % 2 = m' % 2) :
    sortedSpan RD k ρ lam m ≤ sortedSpan RD k ρ lam m' :=
  Submodule.span_mono fun _ ⟨w, hw, hs, hl, hpar, e⟩ => ⟨w, hw, hs, hl.trans h, hpar.trans hp, e⟩

/-- **Sorting in `K₀`** (the `K₀`-shadow of KL III Lemma 3.38): the class `[E_w 1_λ]` of any
signed sequence lies in the `ℤ[q, q⁻¹]`-span of the classes `[E_{(+s)(-t)} 1_λ]` of sorted
sequences of length `≤ |w|` (and of the same parity). -/
theorem eC_mem_span_sorted : ∀ (n : ℕ) (w : List (Letter I)) {ρ lam : X} (h : wt RD lam w = ρ),
    w.length + nInv w ≤ n → eC RD k ρ lam w h ∈ sortedSpan RD k ρ lam w.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro w ρ lam h hn
    rcases isSorted_or_exists_swap w with hs | ⟨a, b, i, j, rfl⟩
    · exact Submodule.subset_span ⟨w, h, hs, le_rfl, rfl, rfl⟩
    · -- `w = a (-j) (+i) b`; compare with `w' = a (+i) (-j) b` and `a b`.
      have hlen : (a ++ (true, i) :: (false, j) :: b).length =
          (a ++ (false, j) :: (true, i) :: b).length := by simp
      have hinv := nInv_swap a b i j
      have hwt : wt RD lam (a ++ (false, j) :: (true, i) :: b) =
          wt RD (wt RD (wt RD lam b) [up i, dn j]) a := by
        rw [wt_append]; congr 1; simp only [wt_cons, wt_nil]; abel
      have h' : wt RD lam (a ++ [up i, dn j] ++ b) = ρ := by
        rw [← h, hwt, wt_append, wt_append]
      have e1 : eC RD k ρ lam (a ++ (true, i) :: (false, j) :: b) (by simpa using h') ∈
          sortedSpan RD k ρ lam (a ++ (false, j) :: (true, i) :: b).length := by
        rw [← hlen]
        exact ih _ (by omega) _ _ le_rfl
      have hw : (a ++ (false, j) :: (true, i) :: b) = a ++ [dn j, up i] ++ b := by simp
      have hw' : (a ++ (true, i) :: (false, j) :: b) = a ++ [up i, dn j] ++ b := by simp
      by_cases hij : i = j
      · subst hij
        have h3 : wt RD lam (a ++ [] ++ b) = ρ := by
          rw [← h, hwt, List.append_nil, wt_append, wt_up_dn]
        have e2 : eC RD k ρ lam (a ++ [] ++ b) h3 ∈
            sortedSpan RD k ρ lam (a ++ (false, i) :: (true, i) :: b).length := by
          refine sortedSpan_mono (m := (a ++ [] ++ b).length) (by simp; omega) (by simp; omega) ?_
          exact ih _ (by
            have := nInv_le_of_remove a b i i
            simp only [List.append_nil, List.length_append, List.length_cons] at hn this ⊢
            omega) _ _ le_rfl
        have ha : wt RD (wt RD lam b) a = ρ := by rw [← h3, List.append_nil, wt_append]
        have e0 : eC RD k ρ lam (a ++ (false, i) :: (true, i) :: b) h =
            eC RD k ρ lam (a ++ [dn i, up i] ++ b) (by rw [← hw]; exact h) := by
          congr 1
        rw [e0]
        rcases le_total 0 (ip RD i (wt RD lam b)) with hn0 | hn0
        · have := eC_EF (k := k) a b ha rfl i hn0 h' (by rw [← hw]; exact h) h3
          rw [eq_sub_of_add_eq this.symm]
          refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ e2)
          convert e1 using 2; simp
        · have := eC_FE (k := k) a b ha rfl i hn0 h' (by rw [← hw]; exact h) h3
          rw [this]
          refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ e2)
          convert e1 using 2; simp
      · have ha : wt RD (wt RD (wt RD lam b) [up i, dn j]) a = ρ := by rw [← hwt, h]
        have := eC_ij (k := k) a b i j hij ha rfl rfl h' (by rw [← hw]; exact h)
        have e0 : eC RD k ρ lam (a ++ (false, j) :: (true, i) :: b) h =
            eC RD k ρ lam (a ++ [dn j, up i] ++ b) (by rw [← hw]; exact h) := by
          congr 1
        rw [e0, ← this]
        convert e1 using 2; simp

/-- **Sorting in `K₀`**, for all signed sequences. -/
theorem eC_mem_sortedSpan {ρ lam : X} (w : List (Letter I)) (h : wt RD lam w = ρ) :
    eC RD k ρ lam w h ∈ sortedSpan RD k ρ lam w.length :=
  eC_mem_span_sorted _ w h le_rfl

end Categorification.KL3.Diagram
