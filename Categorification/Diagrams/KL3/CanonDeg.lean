/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.ChordU
import Categorification.QuantumGroup.UDotFormFormula
import StringDiagrams.Chord.Matching

/-!
# The degree of a canonical chord diagram

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §2.2 (the
degree `deg(D, λ)` of a minimal diagram of a pairing, table after (2.12)) and §3.2.3 (the diagrams
of `B_{𝐢,𝐣,λ}` are "minimal diagrams", with degrees "determined by the rules in Section 3.1").

For a pairing `s` (a `StringDiagrams.Chord` state whose arcs carry dual letters at their ends), the
normal-form diagram `chL [] (canon s)` of its canonical chord diagram is a diagram of `U` of cups
and crossings. Its degree (`sdegSum`, the sum of the degrees of Definition 3.1 of its generators)
is the degree `UDot.mdeg` of the pairing computed by KL III's rules, which is the degree used in
Theorem 2.7 (`UDot.pdeg`):

* removing the leftmost adjacent arc changes both by the degree of that cup
  (`UDot.mdeg_rmRes`);
* uncrossing two interleaved arcs at adjacent positions `q` (a left end) and `q + 1` (a right end)
  changes `mdeg` by the degree of the crossing of the two strands (`UDot.mdeg_swap_cross`): `-i·j`
  if they have the same orientation, `0` for a sideways crossing (`sdegSum_xLay`).

## Main results

* `UDot.mdeg_swap_cross`: the degree of a pairing under an exchange of adjacent endpoints which
  uncrosses two interleaved arcs.
* `sdegSum_xLay`: the degree of the crossing of two strands.
* `sdegSum_canon`: `sdegSum RD μ (chL [] (canon s)) = mdeg (⟨-, μ⟩) (letters of s) (matching of s)`.
-/

noncomputable section

namespace Categorification.QuantumGroup.UDot

open Equiv Finset

variable {I : Type*} (C : CartanDatum I) {n : ℕ} {L : Fin n → Bool × I} {σ : Perm (Fin n)}
  {p p' : Fin n}

/-! ## Uncrossing two interleaved arcs -/

set_option linter.unusedSimpArgs false in
theorem pair_cross_pt (h : IsMatching L σ) (hp' : p'.val = p.val + 1) (h1 : p' < σ p)
    (h2 : σ p' < p) (a b : Fin n) :
    PDn a.val b.val (σ a).val (σ b).val (L a).1 (L b).1 (C.dot (L a).2 (L b).2) =
      PDn (swap p p' a).val (swap p p' b).val (swap p p' (σ a)).val (swap p p' (σ b)).val
          (L a).1 (L b).1 (C.dot (L a).2 (L b).2) +
        if a = σ p' ∧ b = p then
          (if (L p').1 = (L p).1 then -C.dot (L p).2 (L p').2 else 0) else 0 := by
  have hne : σ p ≠ p' := fun e => (lt_irrefl p') (e ▸ h1)
  obtain ⟨f, hf⟩ : ∃ f, σ p = f := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, σ p' = e := ⟨_, rfl⟩
  have hfp : σ f = p := by rw [← hf, h.invol]
  have hep : σ e = p' := by rw [← he, h.invol]
  rw [hf] at h1 hne
  rw [he] at h2
  have v1 : p.val < f.val := by rw [Fin.lt_def] at h1; omega
  have v2 : e.val < p.val := h2
  have v3 : p'.val < f.val := h1
  have t1 : swap p p' p = p' := swap_apply_left _ _
  have t2 : swap p p' p' = p := swap_apply_right _ _
  have t3 : swap p p' f = f := swap_apply_of_ne_of_ne (fun h => by rw [h] at v1; omega)
    (fun h => by rw [h] at v3; omega)
  have t4 : swap p p' e = e := swap_apply_of_ne_of_ne (fun h => by rw [h] at v2; omega)
    (fun h => by rw [h] at v2; omega)
  have fne : ∀ x y : Fin n, x.val ≠ y.val → x ≠ y := fun x y h e => h (e ▸ rfl)
  by_cases bad1 : (a = p ∨ a = f) ∧ (b = p' ∨ b = e)
  · obtain ⟨ha, hb⟩ := bad1
    have hno : ¬ (a = e ∧ b = p) := by
      rintro ⟨rfl, rfl⟩
      rcases ha with h | h <;> [exact absurd (congrArg Fin.val h) (by omega);
        exact absurd (congrArg Fin.val h) (by omega)]
    rw [he, ite_eq_right hno, add_zero]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp only [hf, hfp, he, hep, t1, t2, t3, t4, PDn] <;> split_ifs <;> first | rfl | omega
  by_cases bad2 : (b = p ∨ b = f) ∧ (a = p' ∨ a = e)
  · obtain ⟨hb, ha⟩ := bad2
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rw [he, ite_eq_right (fun h => by have := congrArg Fin.val h.1; omega), add_zero]
      simp only [hf, hfp, he, hep, t1, t2, t3, t4, PDn]; split_ifs <;> omega
    · rw [he, ite_eq_right (fun h => by have := congrArg Fin.val h.1; omega), add_zero]
      simp only [hf, hfp, he, hep, t1, t2, t3, t4, PDn]; split_ifs <;> omega
    · rw [he, ite_eq_left ⟨rfl, rfl⟩]
      have hs : (L a).1 = !(L p').1 := by rw [← he]; exact h.sign p'
      have hc : (L a).2 = (L p').2 := by rw [← he]; exact h.col p'
      simp only [hf, hfp, he, hep, t1, t2, t3, t4, PDn, hs, hc, C.symm (L p').2 (L b).2]
      split_ifs <;> first | omega | (cases (L p').1 <;> cases (L b).1 <;> simp_all)
    · rw [he, ite_eq_right (fun h => by have := congrArg Fin.val h.2; omega), add_zero]
      simp only [hf, hfp, he, hep, t1, t2, t3, t4, PDn]; split_ifs <;> omega
  -- no pair of the four endpoints is `{p, p + 1}`: the swap preserves all comparisons
  have hno : ¬ (a = σ p' ∧ b = p) := fun ⟨h1, h2⟩ => bad2 ⟨Or.inl h2, Or.inr (h1.trans he)⟩
  rw [ite_eq_right hno, add_zero]
  have arc : ∀ x, ¬ (x = p ∧ σ x = p') ∧ ¬ (x = p' ∧ σ x = p) := fun x =>
    ⟨fun ⟨e1, e2⟩ => hne (by rw [← hf, ← e1, e2]), fun ⟨e1, e2⟩ => hne (by rw [← hf, ← e2, h.invol, e1])⟩
  have arc' : ∀ x, ¬ (σ x = p ∧ x = p') ∧ ¬ (σ x = p' ∧ x = p) := fun x =>
    ⟨fun ⟨e1, e2⟩ => (arc x).2 ⟨e2, e1⟩, fun ⟨e1, e2⟩ => (arc x).1 ⟨e2, e1⟩⟩
  have hσf : ∀ x, σ x = p ↔ x = f := fun x => ⟨fun e => by rw [← hfp] at e; exact σ.injective e,
    fun e => by rw [e, hfp]⟩
  have hσe : ∀ x, σ x = p' ↔ x = e := fun x => ⟨fun h' => by rw [← hep] at h'; exact σ.injective h',
    fun h' => by rw [h', hep]⟩
  have key : ∀ x y : Fin n, ¬ (x = p ∧ y = p') → ¬ (x = p' ∧ y = p) →
      ((swap p p' x).val < (swap p p' y).val ↔ x.val < y.val) := fun x y h1 h2 => by
    rw [← Fin.lt_def, ← Fin.lt_def]; exact swap_lt_iff hp' h1 h2
  have b1 : ¬ ((a = p ∨ σ a = p) ∧ (b = p' ∨ σ b = p')) := by
    simp only [hσf, hσe]; exact bad1
  have b2 : ¬ ((b = p ∨ σ b = p) ∧ (a = p' ∨ σ a = p')) := by
    simp only [hσf, hσe]; exact bad2
  have k1 := key a b (fun e => b1 ⟨Or.inl e.1, Or.inl e.2⟩) (fun e => b2 ⟨Or.inl e.2, Or.inl e.1⟩)
  have k2 := key b a (fun e => b2 ⟨Or.inl e.1, Or.inl e.2⟩) (fun e => b1 ⟨Or.inl e.2, Or.inl e.1⟩)
  have k3 := key b (σ a) (fun e => b2 ⟨Or.inl e.1, Or.inr e.2⟩) (fun e => b1 ⟨Or.inr e.2, Or.inl e.1⟩)
  have k4 := key (σ a) b (fun e => b1 ⟨Or.inr e.1, Or.inl e.2⟩) (fun e => b2 ⟨Or.inl e.2, Or.inr e.1⟩)
  have k5 := key (σ a) (σ b) (fun e => b1 ⟨Or.inr e.1, Or.inr e.2⟩)
    (fun e => b2 ⟨Or.inr e.2, Or.inr e.1⟩)
  have k6 := key (σ b) (σ a) (fun e => b2 ⟨Or.inr e.1, Or.inr e.2⟩)
    (fun e => b1 ⟨Or.inr e.2, Or.inr e.1⟩)
  have k7 := key a (σ a) (arc a).1 (arc a).2
  have k8 := key (σ a) a (arc' a).1 (arc' a).2
  have k9 := key b (σ b) (arc b).1 (arc b).2
  have k10 := key (σ b) b (arc' b).1 (arc' b).2
  have k11 := key a (σ b) (fun e => b1 ⟨Or.inl e.1, Or.inr e.2⟩) (fun e => b2 ⟨Or.inr e.2, Or.inl e.1⟩)
  have k12 := key (σ b) a (fun e => b2 ⟨Or.inr e.1, Or.inl e.2⟩) (fun e => b1 ⟨Or.inl e.2, Or.inr e.1⟩)
  simp only [PDn, k1, k2, k3, k5, k6, k7, k9, k11]

/-- **Uncrossing two interleaved arcs at adjacent endpoints** (KL III §2.2): if `p` is the left end
of an arc and `p' = p + 1` the right end of another, the two arcs interleave; exchanging `p` and
`p'` uncrosses them, and the degree of the pairing drops by the degree of the crossing of the two
strands at `p'` and `p`: `-i·j` if they have the same orientation (`ε_{p'} = ε_p`), `0` otherwise. -/
theorem mdeg_swap_cross (h : IsMatching L σ) (hp' : p'.val = p.val + 1) (h1 : p' < σ p)
    (h2 : σ p' < p) (ℓ : I → ℤ) :
    mdeg C ℓ L σ = mdeg C ℓ (L ∘ swap p p') (swap p p' * σ * swap p p') +
      if (L p').1 = (L p).1 then -C.dot (L p).2 (L p').2 else 0 := by
  have hne : σ p ≠ p' := fun e => (lt_irrefl p') (e ▸ h1)
  set τ := swap p p' with hτdef
  have hτ : ∀ x, τ (τ x) = x := swap_apply_self _ _
  have h' := h.conj τ hτ
  rw [mdeg_eq_alt C h' ℓ, mdeg_eq_alt C h ℓ]
  have hσ' : ∀ x, (τ * σ * τ) (τ x) = τ (σ x) := fun x => by simp [hτ]
  have hL' : ∀ x, (L ∘ τ) (τ x) = L x := fun x => by simp [hτ]
  have harc : ∀ a, τ a < τ (σ a) ↔ a < σ a := fun a =>
    swap_lt_iff hp' (fun ⟨e1, e2⟩ => hne (e1 ▸ e2))
      (fun ⟨e1, e2⟩ => hne (by rw [← e2, h.invol, e1]))
  have e0 : ∑ a, (if a < (τ * σ * τ) a then arcDeg C ℓ (L ∘ τ) a else 0) =
      ∑ a, (if a < σ a then arcDeg C ℓ L a else 0) := by
    rw [← Equiv.sum_comp τ]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hσ', harc, arcDeg, hL']
  have e1 : ∑ a, ∑ b, pairDeg C (L ∘ τ) (τ * σ * τ) a b =
      ∑ a, ∑ b, PDn (τ a).val (τ b).val (τ (σ a)).val (τ (σ b)).val (L a).1 (L b).1
        (C.dot (L a).2 (L b).2) := by
    rw [← Equiv.sum_comp τ]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp τ]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [pairDeg_eq_PDn, hσ', hσ', hL', hL']
  have e2 : ∑ a, ∑ b, pairDeg C L σ a b =
      ∑ a, ∑ b, PDn a.val b.val (σ a).val (σ b).val (L a).1 (L b).1 (C.dot (L a).2 (L b).2) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => pairDeg_eq_PDn C L σ a b
  rw [e0, e1, e2]
  have hδ : ∀ δ : ℤ, (∑ a : Fin n, ∑ b : Fin n, if a = σ p' ∧ b = p then δ else 0) = δ := by
    intro δ; simp [ite_and]
  simp only [pair_cross_pt C h hp' h1 h2, Finset.sum_add_distrib, hδ]
  ring

end Categorification.QuantumGroup.UDot

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation
open StringDiagrams.Chord (Same Valid Lettered canon)

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  {RD : RootDatum C X Y}

/-! ## Degrees of cups and crossings -/

/-- The degree of the crossing of two strands (KL III Definition 3.1): `-i·j` for an upward or
downward crossing, `0` for a sideways crossing. -/
theorem sdegSum_xLay (ν : X) (x y : Letter I) :
    sdegSum RD ν (xLay x y) = if x.1 = y.1 then -C.dot x.2 y.2 else 0 := by
  obtain ⟨_ | _, i⟩ := x <;> obtain ⟨_ | _, j⟩ := y
  · simp [xLay, sdegSum, sdeg]
  · simp only [xLay, crossrL, sdegSum, sdeg, sh, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, wt_cons, wt_nil, sgn_true, sgn_false, one_smul, neg_smul, map_add, map_neg,
      RD.pair_iY_iX_eq_A, A_self, Bool.false_eq_true, ite_false]
    have := di_mul_A C i j
    rw [C.symm j i]
    linear_combination this
  · simp only [xLay, crosslL, sdegSum, sdeg, sh, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, wt_cons, wt_nil, sgn_true, sgn_false, one_smul, neg_smul, map_add, map_neg,
      RD.pair_iY_iX_eq_A, A_self, Bool.true_eq_false, ite_false]
    have := di_mul_A C j i
    linear_combination this
  · simp [xLay, sdegSum, sdeg]

/-! ## Pairings as chord states and as matchings -/

section Transport

open StringDiagrams.Chord (lettersOf matchingOf rmAt rmIdx tau)

variable {α : Type*}

theorem lettersOf_rmAt {s : List (ℕ × α)} {r m : ℕ} (hr : r + 2 ≤ s.length) (hn : s.length = m + 2)
    (hm : (rmAt s r).length = m) : lettersOf (rmAt s r) hm = lettersOf s hn ∘ rmEmb r := by
  funext x
  have h := Chord.getElem?_rmAt s hr x.val
  have e : rmIdx r x.val = (rmEmb r x).val := rfl
  rw [e, List.getElem?_eq_getElem (by rw [hm]; exact x.2),
    List.getElem?_eq_getElem (by rw [hn]; exact (rmEmb r x).2)] at h
  simp only [lettersOf, Function.comp_apply]
  rw [Option.some.inj h]

theorem matchingOf_rmAt {s : List (ℕ × α)} {r m : ℕ} (hv : Valid s) (hadj : Same s r (r + 1))
    (hn : s.length = m + 2) (hm : (rmAt s r).length = m) (hvt : Valid (rmAt s r)) (hp : r ≤ m)
    {L : Fin (m + 2) → Bool × I} (hσ : UDot.IsMatching L (matchingOf hv hn))
    (h01 : matchingOf hv hn (rmP0 r hp) = rmP1 r hp) :
    matchingOf hvt hm = rmRes hp (matchingOf hv hn) hσ h01 := by
  have hr : r + 2 ≤ s.length := hadj.lt_right
  refine Equiv.ext fun x => rmEmb_injective r ?_
  rw [rmEmb_rmRes]
  refine ((Chord.same_iff_matchingOf hv hn _ _).1 ?_).symm
  have := (Chord.same_iff_matchingOf hvt hm x (matchingOf hvt hm x)).2 rfl
  rwa [Chord.same_rmAt hr] at this

theorem swap_val_eq_tau {n q : ℕ} (P P' : Fin n) (hP : P.val = q) (hP' : P'.val = q + 1)
    (x : Fin n) : (Equiv.swap P P' x).val = tau q x.val := by
  rw [Equiv.swap_apply_def]
  unfold tau
  split_ifs with h1 h2 h3 h4 h3 h4 <;> simp only [Fin.ext_iff] at * <;> omega

theorem lettersOf_swapAt {s : List (ℕ × α)} {q n : ℕ} (hq : q + 1 < s.length)
    (hn : s.length = n) (hn' : (Chord.swapAt s q).length = n) (P P' : Fin n) (hP : P.val = q)
    (hP' : P'.val = q + 1) :
    lettersOf (Chord.swapAt s q) hn' = lettersOf s hn ∘ Equiv.swap P P' := by
  funext x
  have h := Chord.getElem?_swapAt s hq x.val
  rw [← swap_val_eq_tau P P' hP hP' x, List.getElem?_eq_getElem (by rw [hn']; exact x.2),
    List.getElem?_eq_getElem (by rw [hn]; exact (Equiv.swap P P' x).2)] at h
  simp only [lettersOf, Function.comp_apply]
  rw [Option.some.inj h]

theorem matchingOf_swapAt {s : List (ℕ × α)} {q n : ℕ} (hv : Valid s) (hq : q + 1 < s.length)
    (hn : s.length = n) (hvt : Valid (Chord.swapAt s q)) (hn' : (Chord.swapAt s q).length = n) (P P' : Fin n)
    (hP : P.val = q) (hP' : P'.val = q + 1) :
    matchingOf hvt hn' = Equiv.swap P P' * matchingOf hv hn * Equiv.swap P P' := by
  refine Equiv.ext fun x => (Chord.same_iff_matchingOf hvt hn' _ _).1 ?_
  rw [Chord.same_swapAt hq, ← swap_val_eq_tau P P' hP hP', ← swap_val_eq_tau P P' hP hP']
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_self]
  exact (Chord.same_iff_matchingOf hv hn _ _).2 rfl

/-- The matching of a pairing with dual letters at the ends of its arcs is a pairing in the sense
of `UDot.IsMatching`. -/
theorem isMatching_lettersOf {s : List (ℕ × Letter I)} {n : ℕ} (hv : Valid s)
    (hl : Lettered Letter.dual s) (hn : s.length = n) :
    UDot.IsMatching (lettersOf s hn) (matchingOf hv hn) := by
  intro p
  have hs := (Chord.same_iff_matchingOf hv hn p (matchingOf hv hn p)).2 rfl
  refine ⟨(Chord.isMatching_matchingOf hv hn).1 p, ?_⟩
  have key : ∀ i j : Fin n, Same s i j → (i : ℕ) < j →
      lettersOf s hn j = (lettersOf s hn i).dual := by
    intro i j hij hlt
    have := hl i j hij hlt
    rw [List.getElem?_eq_getElem (by rw [hn]; exact j.2),
      List.getElem?_eq_getElem (by rw [hn]; exact i.2)] at this
    exact Option.some.inj this
  rcases lt_or_gt_of_ne (show (p : ℕ) ≠ matchingOf hv hn p from hs.1) with h | h
  · rw [key _ _ hs h]; exact ⟨rfl, rfl⟩
  · rw [key _ _ hs.symm h]; simp [Letter.dual]

theorem wR_lettersOf (μ : X) {s : List (ℕ × Letter I)} {n : ℕ} (hn : s.length = n) (c : Fin n)
    (i : I) : wR C (RD.ellOf μ) (lettersOf s hn) c i =
      RD.pair (RD.iY i) (wt RD μ ((s.map Prod.snd).drop (c.val + 1))) := by
  have key : ∀ (u : List (Letter I)) (n : ℕ) (hu : u.length = n) (L : Fin n → Letter I)
      (hL : ∀ p : Fin n, L p = u[p.val]'(by rw [hu]; exact p.2)) (c : Fin n),
      wR C (RD.ellOf μ) L c i = wl C (RD.ellOf μ) (u.drop (c.val + 1)) i := by
    intro u n hu
    subst hu
    intro L hL c
    have : L = fun p : Fin u.length => u.get p := funext fun p => hL p
    subst this
    exact wR_get C _ u c i
  rw [key (s.map Prod.snd) n (by rw [List.length_map, hn]) _ (fun p => by simp [lettersOf]) c,
    wl_ellOf_eq]

end Transport

/-! ## The degree of the canonical diagram -/

section CanonDeg

open StringDiagrams.Chord (lettersOf matchingOf rmAt)

theorem lettersOf_eq_of_split {s : List (ℕ × Letter I)} {n : ℕ} (hn : s.length = n)
    {u w : List (Letter I)} {x y : Letter I} (hsplit : s.map Prod.snd = u ++ x :: y :: w)
    (P P' : Fin n) (hP : P.val = u.length) (hP' : P'.val = u.length + 1) :
    lettersOf s hn P = x ∧ lettersOf s hn P' = y := by
  have e : ∀ (i : ℕ) (hi : i < s.length), (s[i]).2 = (s.map Prod.snd)[i]'(by simpa using hi) :=
    fun i hi => by simp
  simp only [lettersOf]
  rw [e, e]
  simp only [List.getElem_of_eq hsplit, hP, hP']
  simp

/-- **The degree of the canonical diagram of a pairing** (KL III §2.2, §3.2.3): for a pairing `s`
with dual letters at the ends of its arcs, the degree of the diagram `chL [] (canon s)` of `U`
with rightmost region `μ` is the degree `mdeg` (computed by KL III's rules) of the matching of
`s` with its letters. -/
theorem sdegSum_canon (μ : X) : ∀ (N : ℕ) {s : List (ℕ × Letter I)}, s.length + Chord.cr s < N →
    ∀ (hv : Valid s), Lettered Letter.dual s → ∀ {n : ℕ} (hn : s.length = n),
    sdegSum RD μ (chL [] (canon s)) = mdeg C (RD.ellOf μ) (lettersOf s hn) (matchingOf hv hn) := by
  intro N
  induction N with
  | zero => intro s h; omega
  | succ N ih =>
  intro s hN hv hl n hn
  by_cases hadj : ∃ r, Same s r (r + 1)
  · classical
    obtain ⟨r, hr, hmin⟩ : ∃ r, Same s r (r + 1) ∧ ∀ r' < r, ¬ Same s r' (r' + 1) :=
      ⟨Nat.find hadj, Nat.find_spec hadj, fun _ => Nat.find_min hadj⟩
    have hl2 : r + 2 ≤ s.length := hr.lt_right
    have htl : (rmAt s r).length = s.length - 2 := Chord.length_rmAt s hl2
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hm : (rmAt s r).length = m := by omega
    have hp : r ≤ m := by omega
    have hvt : Valid (rmAt s r) := hv.rmAt hr
    have hlt : Lettered Letter.dual (rmAt s r) := hl.rmAt hl2
    have hmeas : (rmAt s r).length + Chord.cr (rmAt s r) < N := by
      have := Chord.cr_rmAt_le (s := s) hl2; omega
    have IH := ih hmeas hvt hlt hm
    have hch : chL [] (canon s) = chL [] (canon (rmAt s r)) ++
        mvL ((rmAt s r).map Prod.snd) (.cup r (s[r]'hr.lt_left).2) := by
      rw [Chord.canon_adj hv hr hmin, chL_append, (canon_letters hvt hlt).2]; simp [chL]
    have htw : (rmAt s r).map Prod.snd =
        (s.map Prod.snd).take r ++ (s.map Prod.snd).drop (r + 2) := by
      rw [Chord.map_rmAt]; rfl
    rw [hch, mvL_cup_eq _ htw (by simp; omega), sdegSum_append, IH]
    have hσ := isMatching_lettersOf hv hl hn
    have h01 : matchingOf hv hn (rmP0 r hp) = rmP1 r hp :=
      (Chord.same_iff_matchingOf hv hn _ _).1 hr
    have hc : (lettersOf s hn (rmP1 r hp)).2 = (lettersOf s hn (rmP0 r hp)).2 := by
      rw [← h01]; exact hσ.col _
    have hs : (lettersOf s hn (rmP1 r hp)).1 = !(lettersOf s hn (rmP0 r hp)).1 := by
      rw [← h01]; exact hσ.sign _
    rw [mdeg_rmRes C hp hc hs _ _ hσ h01, ← lettersOf_rmAt hl2 hn hm,
      ← matchingOf_rmAt hv hr hn hm hvt hp hσ h01]
    congr 1
    simp only [sdegSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, sdeg,
      cupDeg, wR_lettersOf]
    rfl
  · have hno : ∀ r, ¬ Same s r (r + 1) := fun r hr => hadj ⟨r, hr⟩
    by_cases hne : s = []
    · subst hne; subst hn
      simp [Chord.canon_nil, chL, mdeg]
    obtain ⟨q, ho, hcl, hq, -⟩ := Chord.canon_cross hv hno hne
    have hilv := Chord.ilv_of_opn_cls hv (hno q) ho hcl
    have hql := hilv.lt
    have hvt : Valid (Chord.swapAt s q) := hv.swapAt hql
    have hlt : Lettered Letter.dual (Chord.swapAt s q) := hl.swapAt hql (hno q)
    have hmeas : (Chord.swapAt s q).length + Chord.cr (Chord.swapAt s q) < N := by
      rw [Chord.length_swapAt]; have := Chord.cr_swapAt_lt hv hilv; omega
    have hn' : (Chord.swapAt s q).length = n := by rw [Chord.length_swapAt, hn]
    have IH := ih hmeas hvt hlt hn'
    have hch : chL [] (canon s) = chL [] (canon (Chord.swapAt s q)) ++
        mvL ((Chord.swapAt s q).map Prod.snd) (.cross q) := by
      rw [hq, chL_append, (canon_letters hvt hlt).2]; simp [chL]
    obtain ⟨u, x, y, w, hsplit, hu⟩ :=
      exists_split_cross (l := s.map Prod.snd) (p := q) (by simpa using hql)
    have htw : (Chord.swapAt s q).map Prod.snd = u ++ y :: x :: w := by
      rw [Chord.map_swapAt, hsplit, ← hu, swapAt_mid]
    let P : Fin n := ⟨q, by omega⟩
    let P' : Fin n := ⟨q + 1, by omega⟩
    rw [hch, mvL_cross_eq htw hu.symm, sdegSum_append, sdegSum_map_whL, sdegSum_xLay, IH,
      lettersOf_swapAt hql hn hn' P P' rfl rfl, matchingOf_swapAt hv hql hn hvt hn' P P' rfl rfl]
    have hσ := isMatching_lettersOf hv hl hn
    have h1 : P' < matchingOf hv hn P := by
      obtain ⟨j, hj, hs⟩ := ho
      have e := (Chord.same_iff_matchingOf hv hn P ⟨j, by rw [← hn]; exact hs.lt_right⟩).1 hs
      rw [e, Fin.lt_def]
      have : j ≠ q + 1 := fun h => hno q (h ▸ hs)
      show q + 1 < j; omega
    have h2 : matchingOf hv hn P' < P := by
      obtain ⟨j, hj, hs⟩ := hcl
      have e := (Chord.same_iff_matchingOf hv hn P' ⟨j, by rw [← hn]; exact hs.lt_right⟩).1 hs
      rw [e, Fin.lt_def]
      have : j ≠ q := fun h => hno q (h ▸ hs).symm
      show j < q; omega
    rw [mdeg_swap_cross C hσ rfl h1 h2]
    obtain ⟨hx, hy⟩ := lettersOf_eq_of_split hn hsplit P P' hu.symm (show q + 1 = u.length + 1 by rw [hu])
    rw [hx, hy, C.symm x.2 y.2]

end CanonDeg

end Categorification.KL3.Diagram
