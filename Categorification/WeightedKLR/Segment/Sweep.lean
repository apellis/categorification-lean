/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Segment.Blocks
import Categorification.WeightedKLR.Segment.Extension
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-!
# Moving the start of a segment inside its chamber

Let `p`, `p'` be generic points in the same chamber and `q` a generic point, with `p → q` and
`p' → q` simple. Moving the start along `P s = p + s (p' - p)`, the crossing times of two
hyperplanes `g`, `g'` agree exactly at the zero of the function
`s ↦ pairFun f q g g' (P s)`, which is affine in `s`. At such an *event* the hyperplanes crossed
at a common time `c` form a block whose crossing order is reversed; the point `P e + c (q - P e)`
lies on exactly the hyperplanes of the block. If no point of the triangle `p, p', q` lies on
hyperplanes whose linear parts span more than a plane, each reversal is a `Flip`
(`Segment.flip_of_block`), and the words of `p → q` and `p' → q` are related by flips
(`Segment.reflTransGen_flip_sweep`).
-/

namespace Categorification.WeightedKLR.Segment

section Scalar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

lemma neg_iff_neg_of_mul_pos {x y : 𝕜} (h : 0 < x * y) : x < 0 ↔ y < 0 := by
  constructor
  · intro hx; by_contra hy; nlinarith [not_lt.1 hy]
  · intro hy; by_contra hx; nlinarith [not_lt.1 hx]

lemma mul_neg_iff_of_mul_pos_of_mul_pos {x x' y y' : 𝕜} (hx : 0 < x * x') (hy : 0 < y * y') :
    x * y < 0 ↔ x' * y' < 0 :=
  neg_iff_neg_of_mul_pos (by
    have := mul_pos hx hy
    linarith [show x * x' * (y * y') = (x * y) * (x' * y') by ring])

/-- An affine function of `s` without zeros on `[u, v]` has the same sign at `u` and `v`. -/
lemma mul_pos_of_forall_ne_zero {α β u v : 𝕜} (huv : u ≤ v)
    (h : ∀ s, u ≤ s → s ≤ v → α + s * β ≠ 0) : 0 < (α + u * β) * (α + v * β) := by
  have hu := h u le_rfl huv
  have hv := h v huv le_rfl
  by_contra hc
  have hneg : (α + u * β) * (α + v * β) < 0 :=
    lt_of_le_of_ne (not_lt.1 hc) (mul_ne_zero hu hv)
  have ht0 := tau_pos hneg
  have ht1 := tau_lt_one hneg
  set t := (α + u * β) / ((α + u * β) - (α + v * β))
  have hz := (val_eq_zero_iff (t := t) (sub_ne_zero.1 (sub_ne_zero_of_mul_neg hneg))).2 rfl
  refine h (u + t * (v - u)) (by nlinarith [mul_nonneg ht0.le (sub_nonneg.2 huv)])
    (by nlinarith [mul_nonneg (sub_nonneg.2 ht1.le) (sub_nonneg.2 huv)]) ?_
  linear_combination hz

/-- An affine function of `s` vanishing at `e` and not at `a < e` changes sign across `e`. -/
lemma mul_neg_of_eq_zero {α β a e b : 𝕜} (hae : a < e) (heb : e < b) (he : α + e * β = 0)
    (ha : α + a * β ≠ 0) : (α + a * β) * (α + b * β) < 0 := by
  have hα : α = -(e * β) := by linarith
  subst hα
  have hβ : β ≠ 0 := by rintro rfl; simp at ha
  rw [show (-(e * β) + a * β) * (-(e * β) + b * β) = (a - e) * (b - e) * (β * β) by ring]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith))
    (mul_self_pos.2 hβ)

end Scalar

variable {ι 𝕜 H : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype H] [DecidableEq H] {f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜}

section Pair

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
lemma pairFun_segPt (q p p' : ι → 𝕜) (g g' : H) (s : 𝕜) :
    pairFun f q g g' (segPt p p' s) =
      pairFun f q g g' p + s * (pairFun f q g g' p' - pairFun f q g g' p) := by
  simp only [pairFun_apply, apply_segPt]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
lemma pairFun_swap (q u : ι → 𝕜) (g g' : H) : pairFun f q g' g u = -pairFun f q g g' u := by
  simp only [pairFun_apply]; ring

omit [Fintype H] [DecidableEq H] in
lemma crossTime_eq_iff_pairFun {u q : ι → 𝕜} {g g' : H} (hg : Separates f u q g)
    (hg' : Separates f u q g') : crossTime f u q g = crossTime f u q g' ↔ pairFun f q g g' u = 0 := by
  rw [crossTime_eq_iff (ne_of_separates hg) (ne_of_separates hg'), pairFun_apply]
  constructor <;> intro e <;> linarith

omit [Fintype H] [DecidableEq H] in
lemma crossTime_lt_iff_pairFun {u q : ι → 𝕜} (hu : Generic f u) (hq : Generic f q) {g g' : H}
    (hg : Separates f u q g) (hg' : Separates f u q g') :
    crossTime f u q g < crossTime f u q g' ↔ pairFun f q g g' u * (f g u * f g' u) < 0 := by
  rw [crossTime_lt_iff ((separates_iff_mul_neg (hu g) (hq g)).1 hg)
    ((separates_iff_mul_neg (hu g') (hq g')).1 hg'),
    show pairFun f q g g' u = f g' u * f g q - f g u * f g' q by rw [pairFun_apply]; ring]

end Pair

variable [Fintype ι]

omit [Fintype H] [DecidableEq H] in
/-- Two distinct hyperplanes through a common point have independent linear parts. -/
lemma two_le_finrank_span (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0) {x : ι → 𝕜}
    {g g' : H} (hne : g ≠ g') (hg : f g x = 0) (hg' : f g' x = 0) {T : Set H} (hgT : g ∈ T)
    (hg'T : g' ∈ T) :
    2 ≤ Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (f h).linear) '' T)) := by
  have hli : LinearIndependent 𝕜 ![(f g).linear, (f g').linear] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hconst : ∀ y, s * f g y + t * f g' y = 0 := by
      intro y
      have := (s • f g + t • f g').apply_eq_of_linear_eq_zero
        (by rw [AffineMap.add_linear, AffineMap.smul_linear, AffineMap.smul_linear]; exact hst)
        y x
      simpa [hg, hg'] using this
    obtain ⟨y, hy1, hy2⟩ := hdist g' g (Ne.symm hne)
    obtain ⟨z, hz1, hz2⟩ := hdist g g' hne
    have hs := hconst y
    rw [hy1, mul_zero, add_zero] at hs
    have ht := hconst z
    rw [hz1, mul_zero, zero_add] at ht
    exact ⟨(mul_eq_zero.1 hs).resolve_right hy2, (mul_eq_zero.1 ht).resolve_right hz2⟩
  have h2 : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range ![(f g).linear, (f g').linear])) = 2 :=
    (finrank_span_eq_card hli).trans (Fintype.card_fin 2)
  rw [← h2]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨g, hgT, rfl⟩
  · exact ⟨g', hg'T, rfl⟩

omit [Fintype H] in
/-- **A block of simultaneous crossings is a flip.** Along a segment `u → q`, let `B` be the
hyperplanes crossed at time `c` (at least two) and `A` those crossed before. If the hyperplanes
through the points of the segment have linear parts spanning at most a plane, reversing `B` is
a flip. -/
lemma flip_of_block (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0) {u q : ι → 𝕜}
    (hu : Generic f u) (hq : Generic f q) {A B C : List H} {c : 𝕜} (hBn : B.Nodup)
    (hB2 : 2 ≤ B.length) (hA : ∀ x, x ∈ A ↔ Separates f u q x ∧ crossTime f u q x < c)
    (hB : ∀ x, x ∈ B ↔ Separates f u q x ∧ crossTime f u q x = c)
    (htri : ∀ t, 0 ≤ t → t ≤ 1 → Module.finrank 𝕜
      (Submodule.span 𝕜 ((fun h => (f h).linear) '' {h | f h (segPt u q t) = 0})) ≤ 2) :
    Flip f (signs f u) (A ++ B ++ C) (A ++ B.reverse ++ C) := by
  obtain ⟨g, g', l, rfl⟩ : ∃ g g' l, B = g :: g' :: l := by
    match B, hB2 with
    | g :: g' :: l, _ => exact ⟨g, g', l, rfl⟩
  have hgg' : g ≠ g' := fun e => (List.nodup_cons.1 hBn).1 (e ▸ List.mem_cons_self)
  obtain ⟨hsg, hcg⟩ := (hB g).1 List.mem_cons_self
  have hc0 : 0 ≤ c := hcg ▸ (crossTime_pos hu hq hsg).le
  have hc1 : c ≤ 1 := hcg ▸ (crossTime_lt_one hu hq hsg).le
  set x := segPt u q c
  have hzero : ∀ h, f h x = 0 ↔ h ∈ g :: g' :: l := by
    intro h
    constructor
    · intro hx
      exact (hB h).2 (separates_of_apply_segPt_eq_zero (hu h) (hq h) hc0 hc1 hx)
    · intro hh
      obtain ⟨hs, e⟩ := (hB h).1 hh
      have := apply_segPt_crossTime (ne_of_separates hs)
      rwa [e] at this
  have hsgn : ∀ h, h ∉ g :: g' :: l → signs f x h = flipSigns (signs f u) A h := by
    intro h hh
    have hne : Separates f u q h → crossTime f u q h ≠ c := fun hs e => hh ((hB h).2 ⟨hs, e⟩)
    have key := (sign_segPt (hu h) (hq h) hc0 hc1 hne).2
    rw [← hA h] at key
    simp only [signs, flipSigns]
    rw [← decide_iff_not]
    exact decide_eq_decide.2 key
  have hset : {h | f h x = 0} = {h | h ∈ g :: g' :: l} := Set.ext hzero
  refine ⟨A, g :: g' :: l, C, rfl, rfl, hB2, ⟨x, hzero, hsgn⟩, le_antisymm ?_ ?_⟩
  · rw [← hset]; exact htri c hc0 hc1
  · exact two_le_finrank_span hdist hgg' ((hzero g).2 List.mem_cons_self)
      ((hzero g').2 (List.mem_cons_of_mem _ List.mem_cons_self)) List.mem_cons_self
      (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **A single event.** If between `a` and `b` the crossing times of two hyperplanes agree only
at `e`, the words at `a` and `b` are related by flips. -/
lemma sweep_event (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0) {p p' q : ι → 𝕜}
    (hp : Generic f p) (hp' : Generic f p') (hpp : signs f p = signs f p') (hq : Generic f q)
    {a e b : 𝕜} (ha : 0 ≤ a) (hae : a < e) (heb : e < b) (hb : b ≤ 1)
    (hev : ∀ g g', Separates f p q g → Separates f p q g' → g ≠ g' → ∀ s, a ≤ s → s ≤ b →
      pairFun f q g g' (segPt p p' s) = 0 → s = e)
    (htri : ∀ t, 0 ≤ t → t ≤ 1 → Module.finrank 𝕜 (Submodule.span 𝕜
      ((fun h => (f h).linear) '' {h | f h (segPt (segPt p p' e) q t) = 0})) ≤ 2) :
    Relation.ReflTransGen (Flip f (signs f p)) (word f (segPt p p' a) q)
      (word f (segPt p p' b) q) := by
  classical
  have he0 : 0 ≤ e := by linarith
  have he1 : e ≤ 1 := by linarith
  have ha1 : a ≤ 1 := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hch : ∀ s, 0 ≤ s → s ≤ 1 → Generic f (segPt p p' s) ∧ signs f (segPt p p' s) = signs f p :=
    fun s h0 h1 => segPt_chamber hp hp' hpp h0 h1
  have hsep : ∀ s, 0 ≤ s → s ≤ 1 → ∀ g, Separates f (segPt p p' s) q g ↔ Separates f p q g :=
    fun s h0 h1 g => (separates_congr_left (hch s h0 h1).2 g)
  have hD : ∀ s s', 0 ≤ s → s ≤ 1 → 0 ≤ s' → s' ≤ 1 → ∀ g g',
      0 < (f g (segPt p p' s) * f g' (segPt p p' s)) *
        (f g (segPt p p' s') * f g' (segPt p p' s')) := by
    intro s s' h0 h1 h0' h1' g g'
    have e := (hch s h0 h1).2.trans (hch s' h0' h1').2.symm
    have k1 := mul_pos_of_signs_eq (hch s h0 h1).1 (hch s' h0' h1').1 e g
    have k2 := mul_pos_of_signs_eq (hch s h0 h1).1 (hch s' h0' h1').1 e g'
    have := mul_pos k1 k2
    linarith [show (f g (segPt p p' s) * f g' (segPt p p' s)) *
        (f g (segPt p p' s') * f g' (segPt p p' s')) =
      (f g (segPt p p' s) * f g (segPt p p' s')) *
        (f g' (segPt p p' s) * f g' (segPt p p' s')) by ring]
  -- the pair functions are affine in `s`
  have hm : ∀ g g' s, pairFun f q g g' (segPt p p' s) =
      pairFun f q g g' p + s * (pairFun f q g g' p' - pairFun f q g g' p) :=
    fun g g' s => pairFun_segPt q p p' g g' s
  have hnz : ∀ g g', Separates f p q g → Separates f p q g' → g ≠ g' → ∀ s, a ≤ s → s ≤ b →
      s ≠ e → pairFun f q g g' (segPt p p' s) ≠ 0 :=
    fun g g' hg hg' hne s h0 h1 hse h0' => hse (hev g g' hg hg' hne s h0 h1 h0')
  have hsimple : ∀ s, a ≤ s → s ≤ b → s ≠ e → Simple f (segPt p p' s) q := by
    intro s h0 h1 hse
    refine ⟨(hch s (by linarith) (by linarith)).1, hq, fun g g' hg hg' hne e' => ?_⟩
    rw [crossTime_eq_iff_pairFun hg hg'] at e'
    exact hnz g g' ((hsep s (by linarith) (by linarith) g).1 hg)
      ((hsep s (by linarith) (by linarith) g').1 hg') hne s h0 h1 hse e'
  have hord : ∀ s, 0 ≤ s → s ≤ 1 → ∀ g g', Separates f p q g → Separates f p q g' →
      (crossTime f (segPt p p' s) q g < crossTime f (segPt p p' s) q g' ↔
        pairFun f q g g' (segPt p p' s) * (f g (segPt p p' s) * f g' (segPt p p' s)) < 0) :=
    fun s h0 h1 g g' hg hg' => crossTime_lt_iff_pairFun (hch s h0 h1).1 hq
      ((hsep s h0 h1 g).2 hg) ((hsep s h0 h1 g').2 hg')
  set κ : H → 𝕜 := fun g => crossTime f (segPt p p' e) q g with hκ
  -- pairs crossed at different times at the event keep their order
  have hdiff : ∀ g g', Separates f p q g → Separates f p q g' → g ≠ g' → κ g ≠ κ g' →
      ∀ s, a ≤ s → s ≤ b →
        (crossTime f (segPt p p' s) q g < crossTime f (segPt p p' s) q g' ↔ κ g < κ g') := by
    intro g g' hg hg' hne hκne s h0 h1
    have hme : pairFun f q g g' (segPt p p' e) ≠ 0 := fun h0' =>
      hκne ((crossTime_eq_iff_pairFun ((hsep e he0 he1 g).2 hg) ((hsep e he0 he1 g').2 hg')).2
        h0')
    have hroot : ∀ r, a ≤ r → r ≤ b → pairFun f q g g' p +
        r * (pairFun f q g g' p' - pairFun f q g g' p) ≠ 0 := fun r h0' h1' hr => by
      rw [← hm] at hr
      have := hev g g' hg hg' hne r h0' h1' hr
      subst this
      exact hme hr
    have hpos : 0 < pairFun f q g g' (segPt p p' s) * pairFun f q g g' (segPt p p' e) := by
      rw [hm, hm]
      rcases le_total s e with hse | hse
      · exact mul_pos_of_forall_ne_zero hse fun r h0' h1' =>
          hroot r (by linarith) (by linarith)
      · rw [mul_comm]
        exact mul_pos_of_forall_ne_zero hse fun r h0' h1' =>
          hroot r (by linarith) (by linarith)
    rw [hord s (by linarith) (by linarith) g g' hg hg', hκ]
    simp only
    rw [hord e he0 he1 g g' hg hg']
    exact mul_neg_iff_of_mul_pos_of_mul_pos hpos (hD s e (by linarith) (by linarith) he0 he1 g g')
  -- pairs crossed at the same time at the event are reversed
  have hsame : ∀ g g', Separates f p q g → Separates f p q g' → g ≠ g' → κ g = κ g' →
      (crossTime f (segPt p p' a) q g < crossTime f (segPt p p' a) q g' ↔
        crossTime f (segPt p p' b) q g' < crossTime f (segPt p p' b) q g) := by
    intro g g' hg hg' hne hκe
    have hme : pairFun f q g g' (segPt p p' e) = 0 :=
      (crossTime_eq_iff_pairFun ((hsep e he0 he1 g).2 hg) ((hsep e he0 he1 g').2 hg')).1 hκe
    have hma := hnz g g' hg hg' hne a le_rfl (hae.le.trans heb.le) hae.ne
    have hneg : pairFun f q g g' (segPt p p' a) * pairFun f q g g' (segPt p p' b) < 0 := by
      rw [hm] at hme hma ⊢
      rw [hm]
      exact mul_neg_of_eq_zero hae heb hme hma
    rw [hord a ha ha1 g g' hg hg', hord b hb0 hb g' g hg' hg, pairFun_swap q (segPt p p' b) g g',
      show f g' (segPt p p' b) * f g (segPt p p' b) = f g (segPt p p' b) * f g' (segPt p p' b)
        from mul_comm _ _]
    exact mul_neg_iff_of_mul_pos_of_mul_pos (by rw [mul_neg]; exact neg_pos.2 hneg) (hD a b ha ha1 hb0 hb g g')
  have hsa := hsimple a le_rfl (by linarith) hae.ne
  have hsb := hsimple b (by linarith) le_rfl heb.ne'
  have hmema : ∀ x, x ∈ word f (segPt p p' a) q ↔ Separates f p q x := fun x => by
    rw [mem_word, hsep a ha ha1]
  have hmemb : ∀ x, x ∈ word f (segPt p p' b) q ↔ Separates f p q x := fun x => by
    rw [mem_word, hsep b hb0 hb]
  have key := reflTransGen_reverse_blocks κ (Separates f p q)
    (fun x y => Separates f p q x ∧ Separates f p q y ∧
      crossTime f (segPt p p' a) q x < crossTime f (segPt p p' a) q y)
    (fun x y => Separates f p q x ∧ Separates f p q y ∧
      crossTime f (segPt p p' b) q x < crossTime f (segPt p p' b) q y)
    (fun x y h h' => lt_asymm h.2.2 h'.2.2) (fun x y h h' => lt_asymm h.2.2 h'.2.2)
    (fun x y ⟨hx, hy, hlt⟩ => by
      by_contra hc
      rw [not_le] at hc
      have hxy : x ≠ y := fun e' => by subst e'; exact lt_irrefl _ hlt
      exact lt_asymm hlt ((hdiff y x hy hx (Ne.symm hxy) hc.ne a le_rfl
        (hae.le.trans heb.le)).2 hc))
    (fun x y ⟨hx, hy, hlt⟩ => by
      by_contra hc
      rw [not_le] at hc
      have hxy : x ≠ y := fun e' => by subst e'; exact lt_irrefl _ hlt
      exact lt_asymm hlt ((hdiff y x hy hx (Ne.symm hxy) hc.ne b (hae.le.trans heb.le)
        le_rfl).2 hc))
    (fun x y hxy => by
      by_cases e' : x = y
      · subst e'
        exact iff_of_false (fun h => lt_irrefl _ h.2.2) (fun h => lt_irrefl _ h.2.2)
      · exact ⟨fun ⟨hx, hy, h⟩ => ⟨hy, hx, (hsame x y hx hy e' hxy).1 h⟩,
          fun ⟨hy, hx, h⟩ => ⟨hx, hy, (hsame x y hx hy e' hxy).2 h⟩⟩)
    (Flip f (signs f p))
    (fun A B C c hBn hB2 hA hB => by
      rw [← (hch e he0 he1).2]
      exact flip_of_block hdist (hch e he0 he1).1 hq hBn hB2
        (fun x => by rw [hsep e he0 he1]; exact hA x)
        (fun x => by rw [hsep e he0 he1]; exact hB x) htri)
    _ (word f (segPt p p' a) q) (word f (segPt p p' b) q) [] le_rfl
    ((pairwise_word hsa).imp_of_mem fun hx hy h => ⟨(hmema _).1 hx, (hmema _).1 hy, h⟩)
    ((pairwise_word hsb).imp_of_mem fun hx hy h => ⟨(hmemb _).1 hx, (hmemb _).1 hy, h⟩)
    (fun x => by rw [hmema, hmemb])
    (fun x => by simp [hmema])
    (fun x hx => by simp at hx)
  simpa using key

/-- **Moving the start inside its chamber.** If `p → q` and `p' → q` are simple, `p`, `p'` lie
in the same chamber, and no point of the triangle `p, p', q` lies on hyperplanes whose linear
parts span more than a plane, the two words are related by flips. -/
theorem reflTransGen_flip_sweep (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0)
    {p p' q : ι → 𝕜} (hpp : signs f p = signs f p') (hs : Simple f p q) (hs' : Simple f p' q)
    (htri : ∀ s t, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → Module.finrank 𝕜 (Submodule.span 𝕜
      ((fun h => (f h).linear) '' {h | f h (segPt (segPt p p' s) q t) = 0})) ≤ 2) :
    Relation.ReflTransGen (Flip f (signs f p)) (word f p q) (word f p' q) := by
  classical
  obtain ⟨hp, hq, hs2⟩ := hs
  obtain ⟨hp', -, hs2'⟩ := hs'
  set E : Set 𝕜 := ⋃ z : H × H, {s | Separates f p q z.1 ∧ Separates f p q z.2 ∧ z.1 ≠ z.2 ∧
    pairFun f q z.1 z.2 (segPt p p' s) = 0} with hEdef
  have hmemE : ∀ s, s ∈ E ↔ ∃ g g', Separates f p q g ∧ Separates f p q g' ∧ g ≠ g' ∧
      pairFun f q g g' (segPt p p' s) = 0 := fun s => by
    simp only [hEdef, Set.mem_iUnion, Set.mem_ofPred_eq, Prod.exists]
  have hp0 : ∀ g g', Separates f p q g → Separates f p q g' → g ≠ g' →
      pairFun f q g g' p ≠ 0 := fun g g' hg hg' hne h0 =>
    hs2 g g' hg hg' hne ((crossTime_eq_iff_pairFun hg hg').2 h0)
  have hE : E.Finite := by
    refine Set.finite_iUnion fun z => Set.Subsingleton.finite ?_
    rintro s₁ ⟨hg, hg', hne, h₁⟩ s₂ ⟨-, -, -, h₂⟩
    rw [pairFun_segPt] at h₁ h₂
    have hβ : pairFun f q z.1 z.2 p' - pairFun f q z.1 z.2 p ≠ 0 := fun hβ => by
      rw [hβ, mul_zero, add_zero] at h₁
      exact hp0 _ _ hg hg' hne h₁
    have : (s₁ - s₂) * (pairFun f q z.1 z.2 p' - pairFun f q z.1 z.2 p) = 0 := by
      linear_combination h₁ - h₂
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hβ)
  have h0E : (0 : 𝕜) ∉ E := by
    rw [hmemE]; rintro ⟨g, g', hg, hg', hne, h0⟩
    rw [segPt_zero] at h0
    exact hp0 g g' hg hg' hne h0
  have h1E : (1 : 𝕜) ∉ E := by
    rw [hmemE]; rintro ⟨g, g', hg, hg', hne, h0⟩
    rw [segPt_one] at h0
    have hsepp : ∀ g, Separates f p q g ↔ Separates f p' q g := separates_congr_left hpp
    exact hs2' g g' ((hsepp g).1 hg) ((hsepp g').1 hg') hne
      ((crossTime_eq_iff_pairFun ((hsepp g).1 hg) ((hsepp g').1 hg')).2 h0)
  have hloc : ∀ a e b : 𝕜, 0 ≤ a → a < e → e < b → b ≤ 1 →
      (∀ s, a ≤ s → s ≤ b → s ∈ E → s = e) →
      Relation.ReflTransGen (Flip f (signs f p)) (word f (segPt p p' a) q)
        (word f (segPt p p' b) q) := fun a e b ha hae heb hb hev =>
    sweep_event hdist hp hp' hpp hq ha hae heb hb
      (fun g g' hg hg' hne s h0 h1 hz => hev s h0 h1 ((hmemE s).2 ⟨g, g', hg, hg', hne, hz⟩))
      (fun t h0 h1 => htri e t (by linarith) (by linarith) h0 h1)
  set Ef := hE.toFinset
  have hEf : ∀ s, s ∈ Ef ↔ s ∈ E := fun s => hE.mem_toFinset
  have main : ∀ n : ℕ, ∀ a b : 𝕜, 0 ≤ a → a < b → b ≤ 1 → a ∉ E → b ∉ E →
      (Ef.filter (fun s => a < s ∧ s < b)).card ≤ n →
      Relation.ReflTransGen (Flip f (signs f p)) (word f (segPt p p' a) q)
        (word f (segPt p p' b) q) := by
    intro n
    induction n with
    | zero =>
      intro a b ha hab hb haE hbE hn
      have hF : Ef.filter (fun s => a < s ∧ s < b) = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hn)
      refine hloc a ((a + b) / 2) b ha (by linarith) (by linarith) hb fun s h0 h1 hsE => ?_
      rcases h0.lt_or_eq with h0 | rfl
      · rcases h1.lt_or_eq with h1 | rfl
        · have : s ∈ Ef.filter (fun s => a < s ∧ s < b) :=
            Finset.mem_filter.2 ⟨(hEf s).2 hsE, h0, h1⟩
          rw [hF] at this; simp at this
        · exact absurd hsE hbE
      · exact absurd hsE haE
    | succ n ih =>
      intro a b ha hab hb haE hbE hn
      set F := Ef.filter (fun s => a < s ∧ s < b) with hFdef
      rcases F.eq_empty_or_nonempty with hF | hF
      · refine hloc a ((a + b) / 2) b ha (by linarith) (by linarith) hb fun s h0 h1 hsE => ?_
        rcases h0.lt_or_eq with h0 | rfl
        · rcases h1.lt_or_eq with h1 | rfl
          · have : s ∈ F := Finset.mem_filter.2 ⟨(hEf s).2 hsE, h0, h1⟩
            rw [hF] at this; simp at this
          · exact absurd hsE hbE
        · exact absurd hsE haE
      set e := F.min' hF with hedef
      have heF : e ∈ F := F.min'_mem hF
      obtain ⟨heE, hae, heb⟩ := Finset.mem_filter.1 heF
      set F2 := insert b (Ef.filter (fun s => e < s ∧ s < b)) with hF2
      have hF2n : F2.Nonempty := ⟨b, Finset.mem_insert_self _ _⟩
      set m := F2.min' hF2n with hmdef
      have hmF2 : m ∈ F2 := F2.min'_mem hF2n
      have hem : e < m := by
        rcases Finset.mem_insert.1 hmF2 with h | h
        · rw [h]; exact heb
        · exact (Finset.mem_filter.1 h).2.1
      have hmb : m ≤ b := F2.min'_le b (Finset.mem_insert_self _ _)
      set c := (e + m) / 2 with hc
      have hec : e < c := by linarith
      have hcm : c < m := by linarith
      have hnoev : ∀ s, e < s → s < m → s ∉ E := fun s h1 h2 hsE => by
        have : s ∈ F2 := Finset.mem_insert_of_mem
          (Finset.mem_filter.2 ⟨(hEf s).2 hsE, h1, lt_of_lt_of_le h2 hmb⟩)
        exact absurd (F2.min'_le s this) (not_le.2 h2)
      have hleft := hloc a e c ha hae hec (by linarith) fun s h0 h1 hsE => by
        rcases lt_trichotomy s e with hse | hse | hse
        · rcases h0.lt_or_eq with h0 | rfl
          · have : s ∈ F := Finset.mem_filter.2 ⟨(hEf s).2 hsE, h0, by linarith⟩
            exact absurd (F.min'_le s this) (not_le.2 hse)
          · exact absurd hsE haE
        · exact hse
        · exact absurd hsE (hnoev s hse (by linarith))
      have hright := ih c b (by linarith) (by linarith) hb (hnoev c hec hcm) hbE (by
        have hsub : Ef.filter (fun s => c < s ∧ s < b) ⊂ F := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨e, heF, fun h => by
              have := (Finset.mem_filter.1 h).2.1
              linarith⟩
          · intro s hs
            obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hs
            exact Finset.mem_filter.2 ⟨h1, by linarith, h3⟩
        have := Finset.card_lt_card hsub
        omega)
      exact hleft.trans hright
  have := main _ 0 1 le_rfl one_pos le_rfl h0E h1E le_rfl
  rwa [segPt_zero, segPt_one] at this

end Categorification.WeightedKLR.Segment
