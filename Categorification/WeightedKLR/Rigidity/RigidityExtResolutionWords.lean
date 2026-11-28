/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.RigidityExtStandardResolution

/-!
# The terms of the resolution of Proposition 7.6, indexed by subsets

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.1,
Proposition 7.6. For a word `t` (the strands left of the last red strand) and a word
`u = u₁ … u_m` of black strands right of it, the terms of homological degree `k` of the
resolution of the standard module are indexed by the subsets `T ⊆ {0, …, m - 1}` with `|T| = k`:
the term of `T` is the projective of the loading `i_T` with word

`t, (u_a)_{a ∈ T} in reversed order, λ_ℓ, (u_a)_{a ∉ T} in order`

(`websterWord`). This file proves that the recursive description `termWords` of
`loadingSum_stdResolution` is this family (`termWords_eq_websterWords`).
-/

namespace Categorification.Stendhal

variable {I : Type} {ℓ : ℕ}

/-- The letters of `u` at the positions in `T`, in order. -/
def pickIn (u : List I) (T : Multiset ℕ) : List I :=
  ((u.zip (List.range u.length)).filter (fun p => decide (p.2 ∈ T))).map Prod.fst

/-- The letters of `u` at the positions not in `T`, in order. -/
def pickOut (u : List I) (T : Multiset ℕ) : List I :=
  ((u.zip (List.range u.length)).filter (fun p => decide (p.2 ∉ T))).map Prod.fst

/-- The word of the loading `i_T` of Proposition 7.6: `t`, the letters of `u` at the positions in
`T` in reversed order, the last red strand, and the other letters of `u` in order. -/
def websterWord (t : List (I ⊕ Fin (ℓ + 1))) (u : List I) (T : Multiset ℕ) :
    List (I ⊕ Fin (ℓ + 1)) :=
  t ++ (pickIn u T).reverse.map Sum.inl ++ [Sum.inr (Fin.last ℓ)] ++ (pickOut u T).map Sum.inl

/-- The words of the terms of degree `k` of the resolution of Proposition 7.6: one for each
subset `T ⊆ {0, …, |u| - 1}` with `k` elements. -/
def websterWords (t : List (I ⊕ Fin (ℓ + 1))) (u : List I) (k : ℕ) :
    Multiset (List (I ⊕ Fin (ℓ + 1))) :=
  (Multiset.powersetCard k (Multiset.range u.length)).map (websterWord t u)

theorem zip_range_append (u : List I) (j : I) :
    (u ++ [j]).zip (List.range (u ++ [j]).length) =
      u.zip (List.range u.length) ++ [(j, u.length)] := by
  rw [List.length_append, List.length_singleton, List.range_succ,
    List.zip_append (by simp)]
  rfl

theorem lt_of_mem_zip_range {u : List I} {p : I × ℕ} (hp : p ∈ u.zip (List.range u.length)) :
    p.2 < u.length :=
  List.mem_range.1 (List.of_mem_zip hp).2

theorem websterWord_append_of_le (t : List (I ⊕ Fin (ℓ + 1))) (u : List I) (j : I)
    {T : Multiset ℕ} (hT : T ≤ Multiset.range u.length) :
    websterWord t (u ++ [j]) T = websterWord t u T ++ [Sum.inl j] := by
  have hm : u.length ∉ T := fun h => by
    simpa using Multiset.mem_of_le hT h
  simp only [websterWord, pickIn, pickOut, zip_range_append, List.filter_append,
    List.filter_singleton, hm, decide_false, decide_true, not_false_eq_true, Bool.cond_false,
    Bool.cond_true, List.append_nil, List.map_append, List.map_cons, List.map_nil, List.append_assoc]

theorem websterWord_append_cons (t : List (I ⊕ Fin (ℓ + 1))) (u : List I) (j : I)
    (T : Multiset ℕ) :
    websterWord t (u ++ [j]) (u.length ::ₘ T) = websterWord (t ++ [Sum.inl j]) u T := by
  have hin : ((u.zip (List.range u.length)).filter
      (fun p => decide (p.2 ∈ u.length ::ₘ T))) =
      (u.zip (List.range u.length)).filter (fun p => decide (p.2 ∈ T)) := by
    refine List.filter_congr fun p hp => ?_
    have := lt_of_mem_zip_range hp
    simp only [Multiset.mem_cons, this.ne, false_or]
  have hout : ((u.zip (List.range u.length)).filter
      (fun p => decide (p.2 ∉ u.length ::ₘ T))) =
      (u.zip (List.range u.length)).filter (fun p => decide (p.2 ∉ T)) := by
    refine List.filter_congr fun p hp => ?_
    have := lt_of_mem_zip_range hp
    simp only [Multiset.mem_cons, this.ne, false_or]
  simp only [websterWord, pickIn, pickOut, zip_range_append, List.filter_append,
    List.filter_singleton, hin, hout, Multiset.mem_cons_self, decide_true, decide_false,
    not_true_eq_false, Bool.cond_true, Bool.cond_false, List.append_nil, List.map_append, List.map_cons,
    List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.cons_append]

/-- **The terms of Proposition 7.6 are indexed by subsets** (Webster, arXiv:1309.3796v3, §7.1,
Proposition 7.6): the words of the terms of degree `k` of the resolution of
`S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(w))` are the words `websterWord t w.reverse T` of the subsets `T` of
the positions of the word `w.reverse` (read left to right) with `|T| = k`. -/
theorem termWords_eq_websterWords (t : List (I ⊕ Fin (ℓ + 1))) (w : List I) (k : ℕ) :
    termWords t w k = websterWords t w.reverse k := by
  induction w generalizing t k with
  | nil =>
    cases k with
    | zero => simp [termWords, websterWords, websterWord, pickIn, pickOut]
    | succ k =>
      simp only [termWords, websterWords, List.reverse_nil, List.length_nil,
        Multiset.range_zero]
      rw [Multiset.powersetCard_eq_empty _ (by simp), Multiset.map_zero]
  | cons j w ih =>
    have hlen : (w.reverse ++ [j]).length = w.reverse.length + 1 := by simp
    rw [List.reverse_cons]
    cases k with
    | zero =>
      rw [termWords, ih, websterWords, websterWords, Multiset.powersetCard_zero_left,
        Multiset.powersetCard_zero_left, Multiset.map_singleton, Multiset.map_singleton,
        Multiset.map_singleton, websterWord_append_of_le _ _ _ (Multiset.zero_le _)]
    | succ k =>
      rw [termWords, ih, ih, websterWords, websterWords, websterWords, hlen,
        Multiset.range_succ, Multiset.powersetCard_cons, Multiset.map_add, Multiset.map_map,
        Multiset.map_map]
      congr 1
      · refine Multiset.map_congr rfl fun T hT => ?_
        exact (websterWord_append_of_le _ _ _ (Multiset.mem_powersetCard.1 hT).1).symm
      · refine Multiset.map_congr rfl fun T _ => ?_
        exact (websterWord_append_cons _ _ _ T).symm

/-! ### Proposition 7.6 -/

section Resolution

open CategoryTheory KLR

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [DecidableEq I] [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (hQ : KLRSymm Q)
  {C : QuantumGroup.CartanDatum I}

/-- **Proposition 7.6** (Webster, arXiv:1309.3796v3, §7.1), ungraded. Let `t` be a red-ordered
loading of the first `ℓ` red strands and `u` a word of black strands. The standardization
`S(T^{λ'} e(t) ⊠ R^{λ_ℓ} e(u))` has a projective resolution whose term of degree `n` is a direct
sum of the projectives `T^λ e(i_T)`, one for each subset `T ⊆ {0, …, |u| - 1}` with `|T| = n`,
where `i_T` has word `t, (u_a)_{a ∈ T} in reversed order, λ_ℓ, (u_a)_{a ∉ T} in order`
(`websterWord`).

The module `cycWord Q Λ w` is `R^{λ_ℓ} e(u)` for `u = w.reverse`. The grading shifts `χ_T` of
the printed statement are not recorded: the algebras here are ungraded. The route hypothesis
`hall` (injectivity of `δ₁` of (7.25) on finite-dimensional modules) holds for Rouquier parameters (`exists_projectiveResolution_websterWords_of_rouquier`). -/
theorem exists_projectiveResolution_websterWords (hR : IsRouquierQ C Q)
    (hall : AllFiniteDeltaInjective Q Λ hQ) {θ : Multiset I}
    (t : Seq (stendhalWeight ℓ θ)) (ht : IsRedOrdered t) (w : List I) {ν : Multiset I}
    (h : θ + wordWt w 0 = ν) :
    ∃ P : ProjectiveResolution (tensorStd Q Λ hQ h (oldProj Q Λ θ t ht) (cycWord Q Λ w)),
      ∀ n, LoadingSum (P.complex.X n) (websterWords (t.word.map (addRedColor ℓ)) w.reverse n) :=
  ⟨stdResolution Q Λ hQ hR hall w (oldProj Q Λ θ t ht) ⟨t, ht, ⟨LinearEquiv.refl _ _⟩⟩ h,
    fun n => termWords_eq_websterWords (t.word.map (addRedColor ℓ)) w n ▸
      loadingSum_stdResolution Q Λ hQ hR hall w _ _ h t ht (LinearEquiv.refl _ _) n⟩

end Resolution

end Categorification.Stendhal
