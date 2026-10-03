/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.CanonDeg
import Categorification.Diagrams.KL3.SpanningBend

/-!
# KL III Proposition 3.11

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3,
Proposition 3.11 (TeX l. 4568: "For any intermediate choices made, `B_{𝐢,𝐣,λ}` spans
`HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)`"), for every Cartan datum.

## The family `B_{∅,v,λ}`

An element `x = (σ, u, m)` of the index set `SpanIdx [] v` of `B_{∅,v,λ}`
(`Categorification.Diagrams.KL3.GdimBound`) is a pairing `σ` of the one-sided boundary word `v`,
a number of dots `u a` on each strand `a` of `σ` and a bubble monomial `m` of `Π_λ`. The
corresponding diagram (`oneB`) is the canonical chord diagram of `σ` (`StringDiagrams.Chord.canon`
of the chord state `StringDiagrams.Chord.ofMatching σ v`, a minimal diagram of `σ`), with `u a`
dots at the left end of the strand `a`, followed by the bubble monomial `m` on the far right:

`oneB x = chL [] (canon σ) · dots(u) · bubAt (bubMon m)`.

* `oneB_mem`: `oneB x` is homogeneous of degree `spanDeg x`: the canonical diagram has the degree
  `deg(D_σ, λ) = pdeg` of KL III §2.2 (`sdegSum_canon`), a dot on an `i`-strand has degree `i·i`,
  and the bubble monomial has degree `Σ (α + 1)(i·i)`;
* **`isSpanFamily_oneB`**: the `oneB x` of degree `d` span
  `HOM_U(1_λ, E_v 1_λ)_d`. By `mem_canonSpan` (the chord-diagram normal form of
  `Categorification.Diagrams.KL3.ChordU`), every 2-morphism is a combination of canonical
  diagrams with dots at the left ends of the arcs, followed by elements of the image of `Π_λ`;
  these are combinations of the `oneB x`.

## Proposition 3.11

Bending the lower endpoints (`Categorification.Diagrams.KL3.SpanningBend`, `isSpanFamily_bendG`)
gives the family `twoB` of `HOM_U(E_s 1_λ, E_t 1_λ)` indexed by `B_{s,t,λ}`:

* **`isSpanFamily_twoB`**, **`prop311`**: KL III Proposition 3.11 in the form
  `Prop311 RD k` of `Categorification.Diagrams.KL3.GdimBound`, for every Cartan datum;
* consequences, previously conditional on `Prop311`: **`cor_3_13_unconditional`** (Corollary 3.13,
  `gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) ≤ π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩`), `calculusNondeg_iff_unconditional`
  (the two definitions of nondegeneracy agree) and `gammaUA'_bijective_of_basisNondeg'` (KL III
  Theorem 1.2 in its original form, given Proposition 2.5 and nondegeneracy; any Cartan datum).

KL III state the bubble slides (Propositions 3.3, 3.4) only for simply-laced Cartan data. The
argument uses them, for an arbitrary Cartan datum, in the form of
`Categorification.Diagrams.KL3.BubbleSlidesGen`: through the elimination of caps (`capElim`) and
the sorting decompositions, on which `mem_canonSpan` rests.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation Module
open StringDiagrams.Chord (Same Valid Lettered canon ofMatching lettersOf matchingOf)

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y}

/-! ## Lists of dots -/

section Dots

/-- The degree of a dot at the position `i` of the letters `t`. -/
def dotDeg (t : List (Letter I)) (i : ℕ) : ℤ :=
  if h : i < t.length then C.dot (t[i]).2 (t[i]).2 else 0

theorem sdegSum_dotAt (μ : X) (t : List (Letter I)) (i : ℕ) :
    sdegSum RD μ (dotAt t i) = dotDeg (C := C) t i := by
  by_cases h : i < t.length
  · obtain ⟨u, l, w, ht, hu⟩ := exists_split_dot h
    rw [dotAt_eq' ht hu.symm]
    simp only [dotDeg, h, ↓reduceDIte]
    have : t[i] = l := by simp only [List.getElem_of_eq ht, ← hu]; simp
    simp [sdegSum, sdeg, this]
  · simp only [dotDeg, h, ↓reduceDIte]
    rw [dotAt, List.drop_eq_nil_of_le (by omega)]
    rfl

theorem sdegSum_dotsL (μ : X) (t : List (Letter I)) (is : List ℕ) :
    sdegSum RD μ (dotsL t is) = (is.map (dotDeg (C := C) t)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [dotsL_cons, sdegSum_append, sdegSum_dotAt, ih, List.map_cons, List.sum_cons]

/-- The list of the positions of the dots of `u : A → ℕ`: each `pos a` repeated `u a` times. -/
def dotList {A : Type*} [Fintype A] (pos : A → ℕ) (u : A → ℕ) : List ℕ :=
  (Finset.univ : Finset A).toList.flatMap fun a => List.replicate (u a) (pos a)

theorem count_flatMap_replicate {A : Type*} (pos u : A → ℕ) (n : ℕ) (l : List A) :
    (l.flatMap fun a => List.replicate (u a) (pos a)).count n =
      (l.map fun a => if pos a = n then u a else 0).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.count_append, ih, List.map_cons, List.sum_cons,
      List.count_replicate]
    simp only [beq_iff_eq]

theorem sum_flatMap_replicate {A : Type*} (pos u : A → ℕ) (f : ℕ → ℤ) (l : List A) :
    ((l.flatMap fun a => List.replicate (u a) (pos a)).map f).sum =
      (l.map fun a => (u a : ℤ) * f (pos a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons,
      List.map_replicate, List.sum_replicate, nsmul_eq_mul]

theorem count_dotList {A : Type*} [Fintype A] (pos u : A → ℕ) (n : ℕ) :
    (dotList pos u).count n = ∑ a, if pos a = n then u a else 0 := by
  rw [dotList, count_flatMap_replicate, Finset.sum_map_toList]

theorem sum_dotList {A : Type*} [Fintype A] (pos u : A → ℕ) (f : ℕ → ℤ) :
    ((dotList pos u).map f).sum = ∑ a, (u a : ℤ) * f (pos a) := by
  rw [dotList, sum_flatMap_replicate, Finset.sum_map_toList]

end Dots

/-! ## The family `B_{∅,v,λ}` -/

section Family

variable {k : Type w} [Field k]

/-- The letters of the one-sided boundary word `v`. -/
abbrev bwL (v : List (Letter I)) : Fin (ρW [] ++ v).length → Letter I :=
  fun p => (ρW [] ++ v).get p

/-- The chord state of a pairing `σ` of the one-sided boundary word `v`. -/
abbrev pState {v : List (Letter I)} (σ : Equiv.Perm (Fin (ρW [] ++ v).length)) :
    List (ℕ × Letter I) :=
  ofMatching σ (bwL v)

/-- The positions of the dots of `B_{∅,v,λ}` with `u a` dots on the strand `a`, at its left end. -/
abbrev arcDots {v : List (Letter I)} {σ : Equiv.Perm (Fin (ρW [] ++ v).length)}
    (u : Arc [] v σ → ℕ) : List ℕ :=
  dotList (fun a : Arc [] v σ => a.1.val) u

variable (RD k) in
/-- **The element of `B_{∅,v,λ}` indexed by `x = (σ, u, m)`** (KL III §3.2.3): the canonical
diagram of the pairing `σ` (a minimal diagram of `σ`), with `u a` dots at the left end of each
strand `a`, followed by the bubble monomial `m` of `Π_λ` on the far right. -/
def oneB (μ : X) (v : List (Letter I)) (x : SpanIdx [] v) :
    (pres RD k).obj (ob RD μ []) ⟶ (pres RD k).obj (ob RD μ v) :=
  dg RD k μ [] v (chL [] (canon (pState x.1.1)) ++ dotsL v (arcDots x.2.1)) ≫
    bubAt RD k μ v (bubMon RD k μ x.2.2)

theorem chord_isMatching {v : List (Letter I)} {σ : Equiv.Perm (Fin (ρW [] ++ v).length)}
    (hσ : σ ∈ pairings [] v) : Chord.IsMatching σ :=
  ⟨(mem_matchings.1 hσ).invol, (mem_matchings.1 hσ).ne⟩

theorem lettered_pState {v : List (Letter I)} {σ : Equiv.Perm (Fin (ρW [] ++ v).length)}
    (hσ : σ ∈ pairings [] v) : Lettered Letter.dual (pState σ) :=
  Chord.lettered_ofMatching _ (chord_isMatching hσ) fun i _ =>
    Prod.ext ((mem_matchings.1 hσ).sign i) ((mem_matchings.1 hσ).col i)

/-- The canonical diagram of a pairing has the degree `deg(D, λ) = pdeg` of KL III §2.2. -/
theorem sdegSum_canon_pState (μ : X) {v : List (Letter I)}
    {σ : Equiv.Perm (Fin (ρW [] ++ v).length)} (hσ : σ ∈ pairings [] v) :
    sdegSum RD μ (chL [] (canon (pState σ))) = pdeg C (RD.ellOf μ) [] v σ := by
  have hv := Chord.valid_ofMatching (bwL v) (chord_isMatching hσ)
  have hn : (pState σ).length = (ρW [] ++ v).length := Chord.length_ofMatching _ _
  rw [sdegSum_canon μ _ (Nat.lt_succ_self _) hv (lettered_pState hσ) hn,
    Chord.lettersOf_ofMatching, Chord.matchingOf_ofMatching (chord_isMatching hσ), pdeg]
  have h0 : ∀ L : Fin (ρW [] ++ v).length → Letter I,
      bendDeg C (RD.ellOf μ) L ([] : List (Letter I)).length = 0 := fun L => by simp [bendDeg]
  rw [h0, add_zero]

/-- **The elements of `B_{∅,v,λ}` are homogeneous of the degrees `spanDeg`.** -/
theorem oneB_mem (μ : X) (v : List (Letter I)) (x : SpanIdx [] v) :
    oneB RD k μ v x ∈ HomD RD k μ [] v (spanDeg C (RD.ellOf μ) x) := by
  have h1 : dg RD k μ [] v (chL [] (canon (pState x.1.1)) ++ dotsL v (arcDots x.2.1)) ∈
      HomD RD k μ [] v (pdeg C (RD.ellOf μ) [] v x.1.1 +
        ∑ a, (x.2.1 a : ℤ) * C.dot (arcCol a) (arcCol a)) := by
    refine dg_mem_homD ?_
    rw [sdegSum_append, sdegSum_canon_pState μ x.1.2, sdegSum_dotsL, sum_dotList]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [dotDeg, show (a.1 : ℕ) < v.length from a.1.2, ↓reduceDIte]
    rfl
  have h2 := bubAt_mem (RD := RD) (k := k) μ v (bubMon_mem (RD := RD) (k := k) μ x.2.2)
  exact comp_mem_homDeg h1 h2

end Family

/-! ## Spanning -/

section Span

variable {k : Type w} [Field k] [DecidableEq I]

omit [DecidableEq I] in
/-- Every generator of the canonical span with a bubble monomial is an element of `B_{∅,v,λ}`. -/
theorem exists_oneB (μ : X) {v : List (Letter I)} {s : List (ℕ × Letter I)} {is : List ℕ}
    (hv : Valid s) (hl : Lettered Letter.dual s) (hsv : s.map Prod.snd = v)
    (his : ∀ i ∈ is, i < s.length ∧ ¬ ∃ j, j < i ∧ Same s i j) (m : (I × ℕ) →₀ ℕ) :
    ∃ x : SpanIdx [] v, oneB RD k μ v x =
      dg RD k μ [] v (chL [] (canon s) ++ dotsL v is) ≫ bubAt RD k μ v (bubMon RD k μ m) := by
  have hn : s.length = (ρW [] ++ v).length := by
    show s.length = v.length
    rw [← hsv, List.length_map]
  set σ := matchingOf hv hn with hσdef
  have hL : lettersOf s hn = bwL v := by
    funext p
    have hp : p.val < (s.map Prod.snd).length := by rw [List.length_map, hn]; exact p.2
    show (s[p.val]'(by rw [hn]; exact p.2)).2 = v[p.val]'p.2
    have := List.getElem_of_eq hsv hp
    simp only [List.getElem_map] at this
    exact this
  have hσ : σ ∈ pairings [] v := by
    have := isMatching_lettersOf hv hl hn
    rw [hL] at this
    exact mem_matchings.2 this
  have hcanon : canon (pState σ) = canon s := by
    rw [← Chord.canon_ofMatching_matchingOf hv hn, hL]
  -- the strands of the dots
  have hleft : ∀ i ∈ is, ∃ a : Arc [] v σ, a.1.val = i := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := his i hi
    refine ⟨⟨⟨i, by rw [← hn]; exact hi1⟩, ?_⟩, rfl⟩
    have hs := (Chord.same_iff_matchingOf hv hn ⟨i, by rw [← hn]; exact hi1⟩
      (σ ⟨i, by rw [← hn]; exact hi1⟩)).2 rfl
    rcases lt_or_gt_of_ne (show i ≠ (σ ⟨i, _⟩ : ℕ) from hs.1) with h | h
    · exact h
    · exact absurd ⟨_, h, hs⟩ hi2
  refine ⟨⟨⟨σ, hσ⟩, fun a => is.count a.1.val, m⟩, ?_⟩
  have hperm : is.Perm (arcDots (v := v) (σ := σ) fun a => is.count a.1.val) := by
    rw [List.perm_iff_count]
    intro n
    rw [count_dotList]
    by_cases hn' : n ∈ is
    · obtain ⟨a₀, ha₀⟩ := hleft n hn'
      rw [Finset.sum_eq_single a₀ (fun b _ hb => ite_eq_right fun h => hb (Subtype.ext (Fin.ext
        (h.trans ha₀.symm)))) (fun h => absurd (Finset.mem_univ _) h), ite_eq_left ha₀, ha₀]
    · rw [List.count_eq_zero_of_not_mem hn']
      refine (Finset.sum_eq_zero fun a _ => ?_).symm
      split_ifs with h
      · rw [h]; exact List.count_eq_zero_of_not_mem hn'
      · rfl
  have hb : ∀ i ∈ is, i < v.length := fun i hi => by
    rw [← hsv, List.length_map]; exact (his i hi).1
  simp only [oneB, hcanon]
  congr 1
  have := dotsL_perm (RD := RD) (k := k) (t := v) hperm hb (chL [] (canon s)) [] μ [] v
  simpa using this.symm

/-- **KL III Proposition 3.11 for one-sided boundary words**: the elements
`oneB x` of `B_{∅,v,λ}` form a graded spanning family of `HOM_U(1_λ, E_v 1_λ)`. -/
theorem isSpanFamily_oneB (μ : X) (v : List (Letter I)) :
    IsSpanFamily RD k μ [] v (oneB RD k μ v) := by
  refine ⟨oneB_mem μ v, fun d => le_antisymm ?_ fun f hf => ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨x, rfl⟩, rfl⟩
    exact oneB_mem μ v x
  -- every 2-morphism lies in the span of the `oneB x`
  have hspan : CanonSpan RD k μ v ≤ Submodule.span k (Set.range (oneB RD k μ v)) := by
    rw [CanonSpan, Submodule.span_le]
    rintro _ ⟨s, is, β, hv, hl, hsv, his, hβ, rfl⟩
    let Φ := (Linear.leftComp k _ (dg RD k μ [] v (chL [] (canon s) ++ dotsL v is))).comp
      (bubAt RD k μ v)
    have hmem : Φ β ∈ (Submodule.span k (Set.range (bubMon RD k μ))).map Φ :=
      Submodule.mem_map_of_mem (isBub_mem_span hβ)
    rw [Submodule.map_span, ← Set.range_comp] at hmem
    refine Submodule.span_le.2 ?_ hmem
    rintro _ ⟨m, rfl⟩
    obtain ⟨x, hx⟩ := exists_oneB (RD := RD) (k := k) μ hv hl hsv his m
    exact Submodule.subset_span ⟨x, hx⟩
  have h1 := hspan (mem_canonSpan μ v f)
  have h2 := mem_span_image_of_homogeneous (pres_isHomogeneous (RD := RD) (k := k))
    (oneB RD k μ v) (spanDeg C (RD.ellOf μ)) (oneB_mem μ v) h1 hf
  rw [Set.image_eq_range] at h2
  exact h2

end Span

/-! ## Proposition 3.11 and its consequences -/

section Prop311

variable {k : Type w} [Field k]

variable (RD k) in
/-- **The element of `B_{s,t,λ}` indexed by `x`**: the element of `B_{∅, s* t, λ}` with the same
index, its lower endpoints bent back down (nested caps). -/
def twoB (μ : X) (s t : List (Letter I)) (x : SpanIdx s t) :
    (pres RD k).obj (ob RD μ s) ⟶ (pres RD k).obj (ob RD μ t) :=
  bendG RD k μ s t (oneB RD k μ (rd s ++ t) (oneIdx x))

/-- **Khovanov–Lauda III, Proposition 3.11** (TeX l. 4568; any Cartan datum): for signed sequences
`𝐢 = s`, `𝐣 = t` and a weight `λ`, the diagrams `twoB x`, `x ∈ B_{𝐢,𝐣,λ}`, form a graded spanning
family of `HOM_U(E_𝐢 1_λ, E_𝐣 1_λ)`: the elements of degree `d` span the degree-`d` part. -/
theorem isSpanFamily_twoB [DecidableEq I] (μ : X) (s t : List (Letter I)) :
    IsSpanFamily RD k μ s t (twoB RD k μ s t) :=
  isSpanFamily_bendG μ s t (isSpanFamily_oneB μ (rd s ++ t))

variable (RD k) in
/-- **Khovanov–Lauda III, Proposition 3.11**, in the form `Prop311`, for every Cartan datum. -/
theorem prop311 : Prop311 RD k := by
  classical
  exact fun μ s t => ⟨_, isSpanFamily_twoB μ s t⟩

variable [Finite I]

/-- **Khovanov–Lauda III, Corollary 3.13** (`cor-ineq`; any Cartan datum, `I` finite):
`gdim HOM_U(E_𝐢 1_λ, E_𝐣 1_λ) ≤ π ⟨E_𝐢 1_λ, E_𝐣 1_λ⟩`, coefficientwise. -/
theorem cor_3_13_unconditional (lam : X) (s t : List (Letter I)) (d : ℤ) :
    ((finrank k (HomD RD k lam s t d) : ℤ) : ℚ) ≤
      (piLS C * toLS (UDot.KL3.sform RD (E1 RD vQ s lam) (E1 RD vQ t lam))).coeff d :=
  cor_3_13 (prop311 RD k) lam s t d

/-- **KL III: "a calculus is nondegenerate if the equality holds in Corollary 3.13 for all
`𝐢, 𝐣, λ`"** (any Cartan datum, `I` finite): the equality form of nondegeneracy
(`CalculusNondeg`) is equivalent to KL III's definition (`BasisNondeg`). -/
theorem calculusNondeg_iff_unconditional : CalculusNondeg RD k ↔ BasisNondeg RD k :=
  calculusNondeg_iff (prop311 RD k)

/-- **KL III Theorem 1.2 in its original form** (any Cartan datum, `I` finite): given Proposition 2.5
(`UDot.KL3.FormNondeg`), if the graphical calculus is nondegenerate in KL III's sense
(`BasisNondeg`), then `γ : 1_ρ (_𝒜 U̇) 1_λ → K₀(U̇(λ, ρ))` is bijective. -/
theorem gammaUA'_bijective_of_basisNondeg' [DecidableEq I]
    (hB : BasisNondeg RD k) (h25 : UDot.KL3.FormNondeg RD) (lam ρ : X) :
    Function.Bijective (gammaUA' (RD := RD) (k := k) lam ρ) :=
  gammaUA'_bijective_of_basisNondeg (prop311 RD k) hB h25 lam ρ

end Prop311

end Categorification.KL3.Diagram
