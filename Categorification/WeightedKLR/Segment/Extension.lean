/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Segment.Perturb

/-!
# Extending a word by one hyperplane

Let `e` and `e'` be generic points whose chambers differ only across the hyperplane `h`, and
let `p` be a generic point on the same side of `h` as `e`. Then there are simple segments
`p₀ → q` and `p₀ → q'`, with `p₀`, `q`, `q'` in the chambers of `p`, `e`, `e'`, whose words
differ by appending `h`: the second segment crosses the hyperplanes of the first in the same
order and then crosses `h` (`Segment.exists_word_append`).

The points `q`, `q'` are taken close to the point `x` where the segment from `e` to `e'` meets
`h`, and `p₀` is chosen in the chamber of `p` so that the segment from `p₀` to `x` meets no two
hyperplanes at the same time. This is the geometric input to the inductive step in the
spanning part of the basis theorem for weighted KLR algebras (B. Webster, arXiv:1209.2463v4,
proof of Theorem 2.8), where a diagram is extended by one crossing.
-/

namespace Categorification.WeightedKLR.Segment

section Scalar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {a b c d A : 𝕜}

lemma mul_pos_of_mul_pos_of_mul_pos (h1 : 0 < a * b) (h2 : 0 < b * c) : 0 < a * c := by
  have h : 0 < (a * c) * (b * b) := by
    have := mul_pos h1 h2
    linarith [show (a * b) * (b * c) = (a * c) * (b * b) by ring]
  exact pos_of_mul_pos_left h (mul_self_nonneg b)

lemma mul_neg_of_mul_neg_of_mul_pos (h1 : a * b < 0) (h2 : 0 < b * c) : a * c < 0 := by
  have h : (a * c) * (b * b) < 0 := by
    have := mul_neg_of_neg_of_pos h1 h2
    linarith [show (a * b) * (b * c) = (a * c) * (b * b) by ring]
  by_contra hc
  nlinarith [mul_nonneg (not_lt.1 hc) (mul_self_nonneg b)]

lemma mul_neg_iff_of_mul_pos (h : 0 < c * d) : d * A < 0 ↔ c * A < 0 := by
  constructor
  · intro hd
    have := mul_neg_of_mul_neg_of_mul_pos (a := A) (b := d) (c := c) (by linarith [mul_comm d A])
      (by linarith [mul_comm c d])
    linarith [mul_comm A c]
  · intro hc
    have := mul_neg_of_mul_neg_of_mul_pos (a := A) (b := c) (c := d) (by linarith [mul_comm c A]) h
    linarith [mul_comm A d]

end Scalar

variable {ι 𝕜 H : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype H] [DecidableEq H] {f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜}

omit [Fintype H] [DecidableEq H] in
lemma signs_eq_of_mul_pos {p q : ι → 𝕜} (h : ∀ g, 0 < f g p * f g q) : signs f p = signs f q :=
  funext fun g => decide_eq_decide.2 (pos_iff_of_mul_pos (h g))

omit [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
lemma generic_of_mul_pos {p q : ι → 𝕜} (h : ∀ g, 0 < f g p * f g q) : Generic f q :=
  fun g e => by simpa [e] using h g

omit [Fintype H] [DecidableEq H] in
/-- The order of two crossing times along a segment, by the sign of a cross-multiplied
expression. -/
lemma crossTime_lt_iff {p q : ι → 𝕜} {g g' : H} (hg : f g p * f g q < 0)
    (hg' : f g' p * f g' q < 0) :
    crossTime f p q g < crossTime f p q g' ↔
      (f g' p * f g q - f g p * f g' q) * (f g p * f g' p) < 0 := by
  have h1 := sub_ne_zero_of_mul_neg hg
  have h2 := sub_ne_zero_of_mul_neg hg'
  have hga : f g p ≠ 0 := by rintro e; simp [e] at hg
  have hga' : f g' p ≠ 0 := by rintro e; simp [e] at hg'
  have key : crossTime f p q g - crossTime f p q g' =
      ((f g' p * f g q - f g p * f g' q) * (f g p * f g' p)) /
        (((f g p - f g q) * (f g' p - f g' q)) * (f g p * f g' p)) := by
    rw [crossTime, crossTime, mul_div_mul_right _ _ (mul_ne_zero hga hga')]
    field_simp
    ring
  have hP : 0 < ((f g p - f g q) * (f g' p - f g' q)) * (f g p * f g' p) := by
    rw [show ((f g p - f g q) * (f g' p - f g' q)) * (f g p * f g' p) =
      (f g p * (f g p - f g q)) * (f g' p * (f g' p - f g' q)) by ring]
    exact mul_pos (mul_sub_pos hg) (mul_sub_pos hg')
  rw [← sub_neg, key, div_lt_iff₀ hP, zero_mul]

omit [Fintype H] [DecidableEq H] in
/-- If the cross-multiplied expressions of all pairs of hyperplanes have prescribed nonzero
signs, the segment is simple and its crossing order is given by those signs. -/
lemma simple_of_pair_sign {p q : ι → 𝕜} (hp : Generic f p) (hq : Generic f q) (c : H → H → 𝕜)
    (hN : ∀ g g', g ≠ g' → 0 < c g g' * (f g' p * f g q - f g p * f g' q)) :
    Simple f p q ∧ ∀ g g', Separates f p q g → Separates f p q g' → g ≠ g' →
      (crossTime f p q g < crossTime f p q g' ↔ c g g' * (f g p * f g' p) < 0) := by
  refine ⟨⟨hp, hq, fun g g' hg hg' hne e => ?_⟩, fun g g' hg hg' hne => ?_⟩
  · rw [crossTime_eq_iff (ne_of_separates hg) (ne_of_separates hg')] at e
    have := hN g g' hne
    rw [show f g' p * f g q - f g p * f g' q = 0 by linarith, mul_zero] at this
    exact lt_irrefl _ this
  · rw [crossTime_lt_iff ((separates_iff_mul_neg (hp g) (hq g)).1 hg)
      ((separates_iff_mul_neg (hp g') (hq g')).1 hg')]
    exact mul_neg_iff_of_mul_pos (hN g g' hne)

omit [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
lemma separates_of_signs_ne {p q : ι → 𝕜} {h : H} (hne : signs f p h ≠ signs f q h) :
    Separates f p q h := fun hc => hne (decide_eq_decide.2 (Iff.of_eq hc))

omit [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
lemma not_separates_of_signs_eq {p q : ι → 𝕜} {h : H} (he : signs f p h = signs f q h) :
    ¬Separates f p q h := fun hc => hc (propext (decide_eq_decide.1 he))

/-- **Extension by one hyperplane.** Let `e`, `e'` be generic points whose chambers differ
exactly across `h`, and let `p` be generic, on the side of `h` of `e`. There are simple
segments `p₀ → q` and `p₀ → q'` with `p₀`, `q`, `q'` in the chambers of `p`, `e`, `e'` such
that the word of the second is the word of the first followed by `h`. -/
theorem exists_word_append (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0)
    {p e e' : ι → 𝕜} {h : H} (hp : Generic f p) (he : Generic f e) (he' : Generic f e')
    (hh : signs f e h ≠ signs f e' h) (hother : ∀ g, g ≠ h → signs f e g = signs f e' g)
    (hph : signs f p h = signs f e h) :
    ∃ p₀ q q', signs f p₀ = signs f p ∧ signs f q = signs f e ∧ signs f q' = signs f e' ∧
      Simple f p₀ q ∧ Simple f p₀ q' ∧ word f p₀ q' = word f p₀ q ++ [h] := by
  classical
  -- the point `x` where the segment from `e` to `e'` meets `h`
  have hsep : Separates f e e' h := separates_of_signs_ne hh
  have hpos : ∀ g, g ≠ h → 0 < f g e * f g e' := fun g hg =>
    mul_pos_of_pos_iff (he g) (he' g) (decide_eq_decide.1 (hother g hg))
  set τ := crossTime f e e' h
  set x := segPt e e' τ with hxdef
  have hx0 : f h x = 0 := apply_segPt_crossTime (ne_of_separates hsep)
  have hτ0 : 0 < τ := crossTime_pos he he' hsep
  have hτ1 : τ < 1 := crossTime_lt_one he he' hsep
  have hxe : ∀ g, g ≠ h → 0 < f g e * f g x := fun g hg => by
    rw [hxdef, apply_segPt]; exact mul_val_pos (hpos g hg) hτ0.le hτ1.le
  have hxe' : ∀ g, g ≠ h → 0 < f g e' * f g x := fun g hg => by
    rw [hxdef, segPt_swap, apply_segPt]
    exact mul_val_pos (by rw [mul_comm]; exact hpos g hg) (by linarith) (by linarith)
  have hxne : ∀ g, g ≠ h → f g x ≠ 0 := fun g hg e0 => by simpa [e0] using hxe g hg
  clear_value x
  -- the point `p₀`
  obtain ⟨p₀, hp₀, hsp, hav⟩ := exists_chamber_avoid hp
    (Set.range fun z : {z : H × H // z.1 ≠ z.2} => pairFun f x z.1.1 z.1.2)
    (Set.finite_range _) (by
      rintro _ ⟨⟨⟨a, b⟩, hab⟩, rfl⟩
      by_cases ha : a = h
      · subst ha
        obtain ⟨y, hy1, hy2⟩ := hdist b a (Ne.symm hab)
        exact ⟨y, by rw [pairFun_apply, hy1]; simpa using ⟨hxne b (Ne.symm hab), hy2⟩⟩
      · obtain ⟨y, hy1, hy2⟩ := hdist a b hab
        exact ⟨y, by rw [pairFun_apply, hy1]; simpa using ⟨hxne a ha, hy2⟩⟩)
  have hph₀ : signs f p₀ h = signs f e h := by rw [hsp, hph]
  -- the cross-multiplied expressions at `x`
  set c : H → H → 𝕜 := fun g g' => f g' p₀ * f g x - f g p₀ * f g' x with hc
  have hc0 : ∀ g g', g ≠ g' → c g g' ≠ 0 := fun g g' hne e0 => by
    have := hav _ ⟨⟨(g', g), Ne.symm hne⟩, rfl⟩
    rw [pairFun_apply] at this
    exact this (by rw [hc] at e0; linarith)
  have hsmall : ∀ y : ι → 𝕜, ∃ δ, 0 < δ ∧ ∀ ε, 0 ≤ ε → ε < δ → ∀ g g', g ≠ g' →
      0 < c g g' * (f g' p₀ * f g (segPt x y ε) - f g p₀ * f g' (segPt x y ε)) := by
    intro y
    obtain ⟨δ, hδ, hδs⟩ := exists_pos_small (Finset.univ : Finset {z : H × H // z.1 ≠ z.2})
      (fun z => c z.1.1 z.1.2)
      (fun z => f z.1.2 p₀ * (f z.1.1 y - f z.1.1 x) - f z.1.1 p₀ * (f z.1.2 y - f z.1.2 x))
      (fun z _ => hc0 _ _ z.2)
    refine ⟨δ, hδ, fun ε h0 hε g g' hne => ?_⟩
    have := hδs ε h0 hε ⟨(g, g'), hne⟩ (Finset.mem_univ _)
    rw [apply_segPt, apply_segPt]
    convert this using 2
    simp only [hc]
    ring
  obtain ⟨δ₁, hδ₁, hs₁⟩ := hsmall e
  obtain ⟨δ₂, hδ₂, hs₂⟩ := hsmall e'
  set ε := min (min δ₁ δ₂) 1 / 2 with hε
  have hm : 0 < min (min δ₁ δ₂) 1 := lt_min (lt_min hδ₁ hδ₂) one_pos
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by linarith [min_le_right (min δ₁ δ₂) 1]
  have hεδ₁ : ε < δ₁ := by
    linarith [min_le_left (min δ₁ δ₂) 1, min_le_left δ₁ δ₂]
  have hεδ₂ : ε < δ₂ := by
    linarith [min_le_left (min δ₁ δ₂) 1, min_le_right δ₁ δ₂]
  -- the endpoints `q`, `q'` lie in the chambers of `e`, `e'`
  have hend : ∀ y : ι → 𝕜, Generic f y → (∀ g, g ≠ h → 0 < f g y * f g x) →
      ∀ g, 0 < f g y * f g (segPt x y ε) := by
    intro y hy hyx g
    rw [apply_segPt]
    by_cases hg : g = h
    · subst hg
      rw [hx0, zero_add, sub_zero]
      nlinarith [mul_self_pos.2 (hy g)]
    · exact mul_pos_of_mul_pos_of_mul_pos (hyx g hg)
        (mul_val_pos (by rw [mul_comm]; exact hyx g hg) hε0.le hε1)
  set q := segPt x e ε
  set q' := segPt x e' ε
  have hqe := hend e he hxe
  have hqe' := hend e' he' hxe'
  have hsq : signs f q = signs f e := (signs_eq_of_mul_pos hqe).symm
  have hsq' : signs f q' = signs f e' := (signs_eq_of_mul_pos hqe').symm
  obtain ⟨hS, hord⟩ := simple_of_pair_sign hp₀ (generic_of_mul_pos hqe) c
    (hs₁ ε hε0.le hεδ₁)
  obtain ⟨hS', hord'⟩ := simple_of_pair_sign hp₀ (generic_of_mul_pos hqe') c
    (hs₂ ε hε0.le hεδ₂)
  refine ⟨p₀, q, q', hsp, hsq, hsq', hS, hS', ?_⟩
  -- separation along the two segments
  have hnh : ¬Separates f p₀ q h := by
    rw [separates_congr_right hsq]; exact not_separates_of_signs_eq hph₀
  have hyh : Separates f p₀ q' h := by
    rw [separates_congr_right hsq']
    exact separates_of_signs_ne fun e0 => hh (hph₀.symm.trans e0)
  have hsame : ∀ g, g ≠ h → (Separates f p₀ q g ↔ Separates f p₀ q' g) := fun g hg => by
    rw [separates_congr_right hsq, separates_congr_right hsq']
    unfold Separates
    rw [propext (decide_eq_decide.1 (hother g hg))]
  have hxneg : ∀ g, Separates f p₀ q g → f g p₀ * f g x < 0 := fun g hg => by
    have hgh : g ≠ h := fun e0 => hnh (e0 ▸ hg)
    rw [separates_congr_right hsq, separates_iff_mul_neg (hp₀ g) (he g)] at hg
    exact mul_neg_of_mul_neg_of_mul_pos hg (hxe g hgh)
  refine word_eq_of_pairwise hS' ?_ fun g => ?_
  · rw [List.pairwise_append]
    refine ⟨(pairwise_word hS).imp_of_mem fun {g g'} hg hg' hlt => ?_, List.pairwise_singleton _ _,
      fun g hg g' hg' => ?_⟩
    · have hgg' : g ≠ g' := fun e0 => (lt_irrefl _ (e0 ▸ hlt))
      have sg := mem_word.1 hg
      have sg' := mem_word.1 hg'
      have hgh : g ≠ h := fun e0 => hnh (e0 ▸ sg)
      have hgh' : g' ≠ h := fun e0 => hnh (e0 ▸ sg')
      exact (hord' g g' ((hsame g hgh).1 sg) ((hsame g' hgh').1 sg') hgg').2
        ((hord g g' sg sg' hgg').1 hlt)
    · rw [List.mem_singleton] at hg'
      rw [hg']
      have sg := mem_word.1 hg
      have hgh : g ≠ h := fun e0 => hnh (e0 ▸ sg)
      refine (hord' g _ ((hsame g hgh).1 sg) hyh hgh).2 ?_
      have hxn := hxneg g sg
      have hph0 := hp₀ h
      simp only [hc, hx0, mul_zero, sub_zero]
      nlinarith [mul_self_pos.2 hph0, mul_neg_of_neg_of_pos hxn (mul_self_pos.2 hph0)]
  · rw [List.mem_append, List.mem_singleton, mem_word]
    by_cases hg : g = h
    · rw [hg]; exact iff_of_true (Or.inr rfl) hyh
    · rw [← hsame g hg]; exact ⟨fun h1 => h1.resolve_right hg, Or.inl⟩

end Categorification.WeightedKLR.Segment
