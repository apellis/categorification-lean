/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Prop320

/-!
# String parametrizations of simple KLR modules

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §3.2, before Proposition 3.20: for an order `i(0) < i(1) < …` of the vertices,
taken cyclically, a simple module `M` gets the sequence `y_0 y_1 …` with `y_r = ε_{i(r)}(M_r)` and
`M_{r+1} = ẽ_{i(r)}^{y_r} M_r`. B. Webster, *Knot invariants and higher representation theory*,
arXiv:1309.3796v2, before Definition 5.16, calls this the **string parametrization** of `M` and
orders simples lexicographically by it (the order used in Propositions 5.17 and 5.18).

Here the colour sequence is any `σ : ℕ → I` in which every colour occurs infinitely often
(`σ r = i(r mod |I|)` in KL I). For a sequence `l` of colours, `strY σ l` reads the maximal runs of
`l` from the right along `σ`: at step `r`, if the last remaining run has colour `σ r` its length
is recorded and the run removed, otherwise `0` is recorded. For a simple module `M` (finite
dimensional, nilpotent dots) the sequence of its support `{s | 1_s M ≠ 0}` with lexicographically
largest `strY σ` (`IsStrMax`) has `strY σ s 0 = ε_{σ 0}(M)` (`strY_zero_eq_epsI`), and removing
the last run passes to `HW(Δ_{σ0^ε} M)` with the shifted colour sequence (`isStrMax_hw`,
`isStrMax_shift`). So `strY σ s` is the string parametrization of `M`, with
`M_{r+1} = HW(Δ_{i(r)^{y_r}} M_r)`, which is isomorphic to `ẽ_{i(r)}^{y_r} M_r` by KL I,
Lemma 3.13. The proof below works with `HW(Δ)` directly and never uses `ẽ`.

## Main results

* `strY`, `strKey`, `strY_injective` (when every colour occurs infinitely often).
* `KLRAlgebra.isStrMax_aux`: **the string parametrization determines a simple module**, and
  `dim 1_s M = ∏ (run lengths of s)!` for its string-maximal sequence `s`; this is the statement
  behind KL I, Proposition 3.20, for any colour sequence.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.KLR

open KLRAlgebra

variable {I : Type*} [DecidableEq I]

/-! ### Reading runs along a colour sequence -/

section Strings

/-- The colour sequence with its first entry removed. -/
def seqShift (σ : ℕ → I) : ℕ → I := fun m => σ (m + 1)

/-- Prepend an entry to a sequence of natural numbers. -/
def natCons (a : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => a
  | r + 1 => f r

/-- Read a list of runs (the last run first) along `σ`: at step `r`, if the first remaining run
has colour `σ r` record its length and remove it, else record `0`. -/
def strYR : (ℕ → I) → List (I × ℕ) → ℕ → ℕ
  | _, [], _ => 0
  | σ, (a, n) :: _, 0 => if a = σ 0 then n else 0
  | σ, (a, n) :: R, r + 1 =>
    if a = σ 0 then strYR (seqShift σ) R r else strYR (seqShift σ) ((a, n) :: R) r

/-- **The string sequence of `l` along `σ`**: its maximal runs, read from the right along `σ`. -/
def strY (σ : ℕ → I) (l : List I) : ℕ → ℕ := strYR σ (runs l).reverse

/-- The string sequence as an element of the lexicographically ordered `ℕ → ℕ`. -/
def strKey (σ : ℕ → I) (l : List I) : Lex (ℕ → ℕ) := toLex (strY σ l)

theorem strYR_cons_of_ne (σ : ℕ → I) {a : I} (n : ℕ) (R : List (I × ℕ)) (h : a ≠ σ 0) :
    strYR σ ((a, n) :: R) = natCons 0 (strYR (seqShift σ) ((a, n) :: R)) := by
  funext r
  cases r <;> simp [strYR, natCons, h]

theorem strYR_cons_of_eq (σ : ℕ → I) {a : I} (n : ℕ) (R : List (I × ℕ)) (h : a = σ 0) :
    strYR σ ((a, n) :: R) = natCons n (strYR (seqShift σ) R) := by
  funext r
  cases r <;> simp [strYR, natCons, h]

theorem strYR_nil (σ : ℕ → I) : strYR σ [] = natCons 0 (strYR (seqShift σ) []) := by
  funext r
  cases r <;> simp [strYR, natCons]

theorem runsCons_getLast_fst (a : I) {X : List (I × ℕ)} (hX : X ≠ []) :
    (runsCons a X).getLast?.map Prod.fst = X.getLast?.map Prod.fst := by
  rcases X with _ | ⟨⟨b, n⟩, r⟩
  · exact absurd rfl hX
  · rw [runsCons_cons]
    split_ifs with h
    · rcases r with _ | ⟨q, r⟩
      · simp
      · simp [List.getLast?_cons_cons]
    · simp [List.getLast?_cons_cons]

/-- The last run of `l` has the colour of the last letter of `l`. -/
theorem runs_getLast_fst : ∀ l : List I, (runs l).getLast?.map Prod.fst = l.getLast?
  | [] => rfl
  | [a] => rfl
  | a :: b :: l => by
    have hne : runs (b :: l) ≠ [] := fun h => by simpa using runs_eq_nil_iff.1 h
    rw [runs_cons, runsCons_getLast_fst a hne, runs_getLast_fst (b :: l),
      List.getLast?_cons_cons]

/-- Every run has positive length. -/
theorem one_le_of_mem_runs : ∀ {l : List I} {q : I × ℕ}, q ∈ runs l → 1 ≤ q.2
  | [], _, h => by simp at h
  | a :: l, q, h => by
    rw [runs_cons] at h
    rcases hr : runs l with _ | ⟨⟨b, n⟩, r⟩
    · rw [hr] at h; simp at h; rw [h]
    · rw [hr, runsCons_cons] at h
      have hb : (b, n) ∈ runs l := by rw [hr]; simp
      have hmem : ∀ x ∈ r, x ∈ runs l := fun x hx => by rw [hr]; simp [hx]
      split_ifs at h
      · rcases List.mem_cons.1 h with h | h
        · rw [h]; simp
        · exact one_le_of_mem_runs (hmem _ h)
      · rcases List.mem_cons.1 h with h | h
        · rw [h]
        · rcases List.mem_cons.1 h with h | h
          · rw [h]; exact one_le_of_mem_runs hb
          · exact one_le_of_mem_runs (hmem _ h)

/-- If `l` does not end with `σ 0`, the string sequence starts with `0` and continues along the
shifted colour sequence. -/
theorem strY_of_getLast_ne (σ : ℕ → I) {l : List I} (hl : l.getLast? ≠ some (σ 0)) :
    strY σ l = natCons 0 (strY (seqShift σ) l) := by
  unfold strY
  rcases hR : (runs l).reverse with _ | ⟨⟨a, n⟩, R⟩
  · exact strYR_nil σ
  · have ha : a ≠ σ 0 := by
      intro h
      apply hl
      rw [← runs_getLast_fst, ← List.head?_reverse, hR]
      simp [h]
    exact strYR_cons_of_ne σ n R ha

/-- Appending a run of `σ 0` to a list not ending with `σ 0`. -/
theorem strY_append_replicate (σ : ℕ → I) {l : List I} (hl : l.getLast? ≠ some (σ 0)) {n : ℕ}
    (hn : 1 ≤ n) :
    strY σ (l ++ List.replicate n (σ 0)) = natCons n (strY (seqShift σ) l) := by
  unfold strY
  rw [runs_append_replicate hn hl, List.reverse_append]
  exact strYR_cons_of_eq σ n _ rfl

/-! #### Order lemmas -/

theorem natCons_lt_natCons {a : ℕ} {f g : ℕ → ℕ} (h : toLex f < toLex g) :
    toLex (natCons a f) < toLex (natCons a g) := by
  obtain ⟨i, hi, hlt⟩ := h
  refine ⟨i + 1, fun j hj => ?_, hlt⟩
  rcases j with _ | j
  · rfl
  · exact hi j (by simpa using hj)

theorem le_of_natCons_le {a : ℕ} {f g : ℕ → ℕ}
    (h : toLex (natCons a f) ≤ toLex (natCons a g)) : toLex f ≤ toLex g := by
  by_contra h'
  exact absurd h (not_le.2 (natCons_lt_natCons (not_le.1 h')))

theorem apply_zero_le_of_le {f g : ℕ → ℕ} (h : toLex f ≤ toLex g) : f 0 ≤ g 0 := by
  by_contra h'
  refine absurd h (not_le.2 ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩)
  exact not_le.1 h'

/-! #### Injectivity -/

/-- Steps that do not meet the colour of the first run record `0` and shift `σ`. -/
theorem strYR_skip {a : I} :
    ∀ (k : ℕ) (σ : ℕ → I) (R : List (I × ℕ)), (∀ q ∈ R.head?, q.1 = a) →
      (∀ j < k, σ j ≠ a) →
      (∀ j < k, strYR σ R j = 0) ∧ ∀ r, strYR σ R (r + k) = strYR (fun m => σ (m + k)) R r
  | 0, σ, R, _, _ => ⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ => rfl⟩
  | k + 1, σ, R, hR, hk => by
    have hR' : strYR σ R = natCons 0 (strYR (seqShift σ) R) := by
      rcases R with _ | ⟨⟨b, n⟩, R⟩
      · exact strYR_nil σ
      · have : b = a := hR _ rfl
        exact strYR_cons_of_ne σ n R (this ▸ (hk 0 (by omega)).symm)
    obtain ⟨h1, h2⟩ := strYR_skip k (seqShift σ) R hR (fun j hj => hk (j + 1) (by omega))
    refine ⟨fun j hj => ?_, fun r => ?_⟩
    · rw [hR']
      rcases j with _ | j
      · rfl
      · exact h1 j (by omega)
    · rw [hR', show r + (k + 1) = (r + k) + 1 by omega]
      exact h2 r

/-- The first step meeting the colour `a` of the first run records its length `n` and removes
the run. -/
theorem strYR_cons_pop (σ : ℕ → I) (a : I) (n : ℕ) (R : List (I × ℕ)) {k : ℕ} (hk : σ k = a)
    (hmin : ∀ j < k, σ j ≠ a) :
    (∀ j < k, strYR σ ((a, n) :: R) j = 0) ∧ strYR σ ((a, n) :: R) k = n ∧
      ∀ r, strYR σ ((a, n) :: R) (r + k + 1) = strYR (fun m => σ (m + k + 1)) R r := by
  obtain ⟨h1, h2⟩ := strYR_skip k σ ((a, n) :: R) (by simp) hmin
  have h3 := strYR_cons_of_eq (a := a) (fun m => σ (m + k)) n R (by simp [hk])
  refine ⟨h1, ?_, fun r => ?_⟩
  · have := h2 0
    rw [zero_add] at this
    rw [this, h3]; rfl
  · rw [show r + k + 1 = (r + 1) + k by omega, h2, h3]
    show strYR (seqShift fun m => σ (m + k)) R r = _
    congr 1
    funext m
    simp only [seqShift]
    congr 1
    omega

omit [DecidableEq I] in
/-- The colour sequence starting at position `k + 1` still meets every colour infinitely often. -/
theorem hσ_shift {σ : ℕ → I} (hσ : ∀ a m, ∃ r, m ≤ r ∧ σ r = a) (k : ℕ) :
    ∀ a m, ∃ r, m ≤ r ∧ (fun m => σ (m + k + 1)) r = a := fun a m => by
  obtain ⟨r, hr, h⟩ := hσ a (m + k + 1)
  exact ⟨r - (k + 1), by omega, by simp only; rw [show r - (k + 1) + k + 1 = r by omega]; exact h⟩

theorem strYR_injective {σ : ℕ → I} (hσ : ∀ a m, ∃ r, m ≤ r ∧ σ r = a) {R R' : List (I × ℕ)}
    (hR : ∀ q ∈ R, 1 ≤ q.2) (hR' : ∀ q ∈ R', 1 ≤ q.2) (h : strYR σ R = strYR σ R') : R = R' := by
  induction R generalizing σ R' with
  | nil =>
    rcases R' with _ | ⟨⟨b, m⟩, R'⟩
    · rfl
    · exfalso
      have hb : ∃ r, σ r = b := (hσ b 0).imp fun _ h => h.2
      have := (strYR_cons_pop σ b m R' (Nat.find_spec hb) fun j hj => Nat.find_min hb hj).2.1
      have h0 := congrFun h (Nat.find hb)
      rw [this] at h0
      have : strYR σ [] (Nat.find hb) = 0 := by cases Nat.find hb <;> rfl
      have hm := hR' (b, m) (by simp)
      simp only at hm
      omega
  | cons q R ih =>
    obtain ⟨a, n⟩ := q
    have ha : ∃ r, σ r = a := (hσ a 0).imp fun _ h => h.2
    obtain ⟨pa0, pa1, pa2⟩ :=
      strYR_cons_pop σ a n R (Nat.find_spec ha) fun j hj => Nat.find_min ha hj
    have hn := hR (a, n) (by simp)
    simp only at hn
    rcases R' with _ | ⟨⟨b, m⟩, R'⟩
    · exfalso
      have h0 := congrFun h (Nat.find ha)
      rw [pa1] at h0
      have : strYR σ [] (Nat.find ha) = 0 := by cases Nat.find ha <;> rfl
      omega
    · have hb : ∃ r, σ r = b := (hσ b 0).imp fun _ h => h.2
      obtain ⟨pb0, pb1, pb2⟩ :=
        strYR_cons_pop σ b m R' (Nat.find_spec hb) fun j hj => Nat.find_min hb hj
      have hm := hR' (b, m) (by simp)
      simp only at hm
      have hk : Nat.find ha = Nat.find hb := by
        rcases lt_trichotomy (Nat.find ha) (Nat.find hb) with hlt | heq | hlt
        · have := congrFun h (Nat.find ha)
          rw [pa1, pb0 _ hlt] at this; omega
        · exact heq
        · have := congrFun h (Nat.find hb)
          rw [pb1, pa0 _ hlt] at this; omega
      have hab : a = b := by
        rw [← Nat.find_spec ha, ← Nat.find_spec hb, hk]
      subst hab
      have hnm : n = m := by
        have := congrFun h (Nat.find ha)
        rwa [pa1, hk, pb1] at this
      subst hnm
      have htail : strYR (fun m => σ (m + Nat.find ha + 1)) R =
          strYR (fun m => σ (m + Nat.find ha + 1)) R' := by
        funext r
        rw [← pa2, h, hk, pb2]
      rw [ih (hσ_shift hσ _) (fun q hq => hR q (by simp [hq]))
        (fun q hq => hR' q (by simp [hq])) htail]

/-- **The string sequence determines the list**, when every colour occurs infinitely often in
`σ`. -/
theorem strY_injective {σ : ℕ → I} (hσ : ∀ a m, ∃ r, m ≤ r ∧ σ r = a) :
    Function.Injective (strY σ) := fun _ _ h =>
  runs_injective (List.reverse_injective
    (strYR_injective hσ (fun _ hq => one_le_of_mem_runs (List.mem_reverse.1 hq))
      (fun _ hq => one_le_of_mem_runs (List.mem_reverse.1 hq)) h))

theorem strKey_injective {σ : ℕ → I} (hσ : ∀ a m, ∃ r, m ≤ r ∧ σ r = a) :
    Function.Injective (strKey σ) := fun _ _ h => strY_injective hσ (toLex.injective h)

/-- `strY σ s` at `0` is the number of trailing letters `σ 0` of `s`. -/
theorem strY_ofFn_zero (σ : ℕ → I) {ν : Multiset I} (s : Seq ν) :
    strY σ (List.ofFn s.1) 0 = Seq.tailLen (σ 0) s := by
  rcases Nat.eq_zero_or_pos (Seq.tailLen (σ 0) s) with h0 | hpos
  · rw [strY_of_getLast_ne σ (getLast?_ofFn_ne s h0), h0]; rfl
  · obtain ⟨rest, hrest⟩ := seqKey_eq_cons (id : I → I) s (σ 0) hpos
    unfold seqKey runKey at hrest
    unfold strY
    rcases hR : (runs (List.ofFn s.1)).reverse with _ | ⟨⟨a, n⟩, R⟩
    · rw [hR] at hrest; simp at hrest
    · rw [hR] at hrest
      simp only [List.map_cons, List.cons.injEq] at hrest
      have := congrArg ofLex hrest.1
      simp only [ofLex_toLex, id, Prod.mk.injEq] at this
      rw [strYR_cons_of_eq σ n R this.1]
      exact this.2

end Strings

/-! ### The string-maximal sequence of a simple module -/

namespace KLRAlgebra

section StrMax

variable {K : Type*} [Field K] {Q : I → I → MvPolynomial (Fin 2) K}
  {P : I → I → MvPolynomial (Fin 2) K}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0)

variable (Q) in
/-- `s` is the sequence of the support `{s | 1_s M ≠ 0}` of `M` with the lexicographically
largest string sequence along `σ`. -/
def IsStrMax (σ : ℕ → I) (ν : Multiset I) (M : Type*) [AddCommGroup M] [Module K M]
    [Module (KLRAlgebra K Q ν) M] [IsScalarTower K (KLRAlgebra K Q ν) M] (s : Seq ν) : Prop :=
  s ∈ seqSupp Q ν M ∧ ∀ t ∈ seqSupp Q ν M, strKey σ (List.ofFn t.1) ≤ strKey σ (List.ofFn s.1)

section Basic

variable {ν : Multiset I} {M : Type*} [AddCommGroup M] [Module K M]
  [Module (KLRAlgebra K Q ν) M] [IsScalarTower K (KLRAlgebra K Q ν) M]

theorem exists_isStrMax [Nontrivial M] (σ : ℕ → I) : ∃ s, IsStrMax Q σ ν M s := by
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image (seqSupp Q ν M)
    (fun t : Seq ν => strKey σ (List.ofFn t.1)) (seqSupp_nonempty (Q := Q) (ν := ν) (M := M))
  exact ⟨s, hs, hmax⟩

/-- **The first entry of the string sequence is `ε_{σ 0}(M)`.** -/
theorem strY_zero_eq_epsI [Nontrivial M] {σ : ℕ → I} {s : Seq ν} (hs : IsStrMax Q σ ν M s) :
    strY σ (List.ofFn s.1) 0 = epsI Q ν (σ 0) M := by
  rw [strY_ofFn_zero]
  refine le_antisymm (tailLen_le_epsI (mem_seqSupp.1 hs.1)) ?_
  obtain ⟨t, ht, hte⟩ := exists_tailLen_eq_epsI (Q := Q) (ν := ν) (i := σ 0) (M := M)
  have := apply_zero_le_of_le (hs.2 t (mem_seqSupp.2 ht))
  rw [strY_ofFn_zero, strY_ofFn_zero, hte] at this
  exact this

/-- If `ε_{σ 0}(M) = 0`, the string-maximal sequence for `σ` is string-maximal for the shifted
colour sequence. -/
theorem isStrMax_shift [Nontrivial M] {σ : ℕ → I} {s : Seq ν} (hs : IsStrMax Q σ ν M s)
    (h0 : epsI Q ν (σ 0) M = 0) : IsStrMax Q (seqShift σ) ν M s := by
  have htail : ∀ t ∈ seqSupp Q ν M, Seq.tailLen (σ 0) t = 0 := fun t ht =>
    Nat.eq_zero_of_le_zero ((tailLen_le_epsI (mem_seqSupp.1 ht)).trans_eq h0)
  refine ⟨hs.1, fun t ht => ?_⟩
  have h := hs.2 t ht
  unfold strKey at h ⊢
  rw [strY_of_getLast_ne σ (getLast?_ofFn_ne t (htail t ht)),
    strY_of_getLast_ne σ (getLast?_ofFn_ne s (htail s hs.1))] at h
  exact le_of_natCons_le h

end Basic

universe u

section Step

variable {μ ν' : Multiset I} {i : I} (hν' : ∀ a ∈ ν', a = i)
  {L : Type u} [AddCommGroup L] [Module K L] [Module (KLRAlgebra K Q (μ + ν')) L]
  [IsScalarTower K (KLRAlgebra K Q (μ + ν')) L] [FiniteDimensional K L]
  [IsSimpleModule (KLRAlgebra K Q (μ + ν')) L]
  (hnil : ∀ a, SmulNilpotent (x a : KLRAlgebra K Q (μ + ν')) L)
  (hε : epsI Q (μ + ν') i L = Multiset.card ν')

include hPQ hP hnil hε in
/-- **Removing the last run**: if `σ 0 = i` and the string-maximal sequence of `L` is `s' i^ε`,
then `s'` is string-maximal for `HW(Δ_{i^ε} L)` and the shifted colour sequence. -/
theorem isStrMax_hw (hn : 1 ≤ Multiset.card ν') {σ : ℕ → I} (hσ0 : σ 0 = i) {s' : Seq μ}
    (hs : IsStrMax Q σ (μ + ν') L (s'.append (Seq.constSeq hν'))) :
    IsStrMax Q (seqShift σ) μ (HWSpace Q μ ν' (ResSub Q μ ν' L)) s' := by
  subst hσ0
  have h3 := (lemma_3_8 hν' hPQ hP hnil hε).2.2
  have htail : ∀ t ∈ seqSupp Q μ (HWSpace Q μ ν' (ResSub Q μ ν' L)), Seq.tailLen (σ 0) t = 0 :=
    fun t ht => Nat.eq_zero_of_le_zero ((tailLen_le_epsI (mem_seqSupp.1 ht)).trans_eq h3)
  have hs' := (mem_seqSupp_hw_iff hPQ hP hν' hnil hε s').2 hs.1
  refine ⟨hs', fun t ht => ?_⟩
  have h := hs.2 _ ((mem_seqSupp_hw_iff hPQ hP hν' hnil hε t).1 ht)
  unfold strKey at h ⊢
  rw [ofFn_append, ofFn_constSeq, ofFn_append, ofFn_constSeq,
    strY_append_replicate σ (getLast?_ofFn_ne t (htail t ht)) hn,
    strY_append_replicate σ (getLast?_ofFn_ne s' (htail s' hs')) hn] at h
  exact le_of_natCons_le h

end Step

include hPQ hP in
/-- **The string parametrization determines a simple module** (the induction behind KL I,
Proposition 3.20, along any colour sequence `σ` meeting every colour infinitely often): for a
simple finite-dimensional `R(ν)`-module `L` with nilpotent dots and string-maximal sequence `s`,
(1) `dim 1_s L = ∏ (run lengths of s)!`, and (2) `L` is determined up to isomorphism by `s`. -/
theorem isStrMax_aux (n : ℕ) : ∀ (ν : Multiset I), Multiset.card ν = n →
    ∀ (σ : ℕ → I), (∀ a m, ∃ r, m ≤ r ∧ σ r = a) →
    ∀ (L : Type u) [AddCommGroup L] [Module K L] [Module (KLRAlgebra K Q ν) L]
      [IsScalarTower K (KLRAlgebra K Q ν) L] [FiniteDimensional K L]
      [IsSimpleModule (KLRAlgebra K Q ν) L],
      (∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L) → ∀ s : Seq ν, IsStrMax Q σ ν L s →
      dimCh Q ν L s = runsFact s ∧
      ∀ (L' : Type u) [AddCommGroup L'] [Module K L'] [Module (KLRAlgebra K Q ν) L']
        [IsScalarTower K (KLRAlgebra K Q ν) L'] [FiniteDimensional K L']
        [IsSimpleModule (KLRAlgebra K Q ν) L'],
        (∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L') → IsStrMax Q σ ν L' s →
        Nonempty (L ≃ₗ[KLRAlgebra K Q ν] L') := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν hν σ₀ hσ₀ L _ _ _ _ _ _ hnil s hs₀
  have : Nontrivial L := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) L
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨?_, fun L' _ _ _ _ _ _ _ _ => nonempty_equiv_of_card_eq_zero hν⟩
    have := subsingleton_seq_of_card_eq_zero (ν := ν) hν
    have he : (e s : KLRAlgebra K Q ν) = 1 := by rw [← sum_e, Fintype.sum_subsingleton _ s]
    have hnil' : List.ofFn s.1 = [] := List.eq_nil_of_length_eq_zero (by simp [hν])
    rw [dimCh, he, fixSub_one, finrank_top, finrank_eq_one_of_card_eq_zero (Q := Q) hν, runsFact,
      hnil', runs_nil]
    rfl
  -- the step at a colour `σ 0` with `ε_{σ 0}(L) ≥ 1`
  have main : ∀ (σ : ℕ → I), (∀ a m, ∃ r, m ≤ r ∧ σ r = a) → 1 ≤ epsI Q ν (σ 0) L →
      IsStrMax Q σ ν L s → dimCh Q ν L s = runsFact s ∧
      ∀ (L' : Type u) [AddCommGroup L'] [Module K L'] [Module (KLRAlgebra K Q ν) L']
        [IsScalarTower K (KLRAlgebra K Q ν) L'] [FiniteDimensional K L']
        [IsSimpleModule (KLRAlgebra K Q ν) L'],
        (∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L') → IsStrMax Q σ ν L' s →
        Nonempty (L ≃ₗ[KLRAlgebra K Q ν] L') := by
    intro σ hσ hpos hs
    obtain ⟨i, hi⟩ : ∃ i, σ 0 = i := ⟨_, rfl⟩
    have hεs : Seq.tailLen i s = epsI Q ν i L := by
      rw [← hi, ← strY_ofFn_zero, strY_zero_eq_epsI hs]
    rw [hi] at hpos
    set ε := Seq.tailLen i s with hεdef
    have hy : 1 ≤ ε := hεs ▸ hpos
    have hrep : Multiset.replicate ε i ≤ ν :=
      replicate_le_of_hasTail (Seq.hasTail_tailLen (i := i) s)
    obtain ⟨μ, hμ⟩ := Multiset.le_iff_exists_add.1 hrep
    rw [add_comm] at hμ
    have htail := Seq.hasTail_tailLen (i := i) s
    rw [← hεdef] at htail
    clear_value ε
    obtain ⟨ν', hν'def⟩ : ∃ ν', Multiset.replicate ε i = ν' := ⟨_, rfl⟩
    rw [hν'def] at hμ
    subst hμ
    have hν' : ∀ a ∈ ν', a = i := fun a ha => Multiset.eq_of_mem_replicate (hν'def ▸ ha)
    have hcard : Multiset.card ν' = ε := by rw [← hν'def, Multiset.card_replicate]
    have hε : epsI Q (μ + ν') i L = Multiset.card ν' := by rw [hcard, hεs]
    rw [← hcard] at htail
    obtain ⟨s', rfl⟩ := Seq.exists_eq_append_const_of_hasTail hν' htail
    have hn1 : 1 ≤ Multiset.card ν' := by omega
    set N := HWSpace Q μ ν' (ResSub Q μ ν' L)
    have : IsSimpleModule (KLRAlgebra K Q μ) N := (lemma_3_8 hν' hPQ hP hnil hε).2.1
    have : FiniteDimensional K N := FiniteDimensional.finiteDimensional_submodule _
    have hNnil : ∀ a : Fin (Multiset.card μ), SmulNilpotent (x a : KLRAlgebra K Q μ) N :=
      fun a => smulNilpotent_hwSpace a (hnil _)
    have hμcard : Multiset.card μ < n := by
      rw [← hν, Multiset.card_add]; omega
    have hsN := isStrMax_hw hPQ hP hν' hnil hε hn1 hi hs
    obtain ⟨hdimN, hisoN⟩ :=
      ih (Multiset.card μ) hμcard μ rfl (seqShift σ) (hσ_shift hσ 0) N hNnil s' hsN
    have htail0 : Seq.tailLen i s' = 0 := by
      have h3 := (lemma_3_8 hν' hPQ hP hnil hε).2.2
      exact Nat.eq_zero_of_le_zero (h3 ▸ tailLen_le_epsI (mem_seqSupp.1 hsN.1))
    refine ⟨?_, fun L' _ _ _ _ _ _ hnil' hs' => ?_⟩
    · rw [dimCh_append_const hν' hPQ hP hnil hε s', hdimN]
      show _ * Module.finrank K (Coinv K (Multiset.card ν')) = _
      rw [finrank_coinv, runsFact, runsFact, ofFn_append, ofFn_constSeq,
        runs_append_replicate hn1 (getLast?_ofFn_ne s' htail0), List.map_append,
        List.prod_append]
      simp
    · have : Nontrivial L' := IsSimpleModule.nontrivial (KLRAlgebra K Q (μ + ν')) L'
      have hε' : epsI Q (μ + ν') i L' = Multiset.card ν' := by
        rw [← hi, ← strY_zero_eq_epsI hs', strY_zero_eq_epsI hs, hi, hε]
      set N' := HWSpace Q μ ν' (ResSub Q μ ν' L')
      have : IsSimpleModule (KLRAlgebra K Q μ) N' := (lemma_3_8 hν' hPQ hP hnil' hε').2.1
      have : FiniteDimensional K N' := FiniteDimensional.finiteDimensional_submodule _
      have hNnil' : ∀ a : Fin (Multiset.card μ), SmulNilpotent (x a : KLRAlgebra K Q μ) N' :=
        fun a => smulNilpotent_hwSpace a (hnil' _)
      have hsN' := isStrMax_hw hPQ hP hν' hnil' hε' hn1 hi hs'
      obtain ⟨φ⟩ := hisoN N' hNnil' hsN'
      exact nonempty_equiv_of_hwSpace_equiv hν' hPQ hP hnil hnil' hε hε' φ.symm
  -- a colour `b` with `ε_b(L) ≥ 1`: the last letter of `s`
  set b : I := s.1 ⟨Multiset.card ν - 1, by omega⟩
  have hb : 1 ≤ epsI Q ν b L := by
    have : Seq.HasTail b s 1 := ⟨by omega, fun a ha => by
      rw [show a = ⟨Multiset.card ν - 1, by omega⟩ from
        Fin.ext (show a.val = Multiset.card ν - 1 by have := a.2; omega)]⟩
    exact le_trans (Seq.le_tailLen this) (tailLen_le_epsI (mem_seqSupp.1 hs₀.1))
  obtain ⟨r₀, -, hr₀⟩ := hσ₀ b 0
  clear_value b
  -- walk along `σ` until the first colour with `ε ≥ 1`
  suffices key : ∀ (r : ℕ) (σ : ℕ → I), (∀ a m, ∃ r, m ≤ r ∧ σ r = a) → 1 ≤ epsI Q ν (σ r) L →
      IsStrMax Q σ ν L s → dimCh Q ν L s = runsFact s ∧
      ∀ (L' : Type u) [AddCommGroup L'] [Module K L'] [Module (KLRAlgebra K Q ν) L']
        [IsScalarTower K (KLRAlgebra K Q ν) L'] [FiniteDimensional K L']
        [IsSimpleModule (KLRAlgebra K Q ν) L'],
        (∀ a, SmulNilpotent (x a : KLRAlgebra K Q ν) L') → IsStrMax Q σ ν L' s →
        Nonempty (L ≃ₗ[KLRAlgebra K Q ν] L') from key r₀ σ₀ hσ₀ (hr₀ ▸ hb) hs₀
  intro r
  induction r with
  | succ r ihr =>
    intro σ hσ hr hs
    rcases Nat.eq_zero_or_pos (epsI Q ν (σ 0) L) with h0 | _
    · have hσ' : ∀ a m, ∃ r, m ≤ r ∧ seqShift σ r = a := hσ_shift hσ 0
      obtain ⟨hd, hiso⟩ := ihr (seqShift σ) hσ' hr (isStrMax_shift hs h0)
      refine ⟨hd, fun L' _ _ _ _ _ _ hnil' hs' => ?_⟩
      have : Nontrivial L' := IsSimpleModule.nontrivial (KLRAlgebra K Q ν) L'
      have h0' : epsI Q ν (σ 0) L' = 0 := by
        rw [← strY_zero_eq_epsI hs', strY_zero_eq_epsI hs, h0]
      exact hiso L' hnil' (isStrMax_shift hs' h0')
    · exact main σ hσ ‹_› hs
  | zero => intro σ hσ hr hs; exact main σ hσ hr hs

end StrMax

end KLRAlgebra

end Categorification.KLR
