/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Crossing orders of segments in an affine hyperplane arrangement

Let `f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜` be a finite family of affine functions on `𝕜^ι`, `𝕜` an ordered
field, defining an arrangement of hyperplanes `f h = 0`. A segment from a generic point `p` to a
generic point `q` crosses exactly the hyperplanes separating `p` and `q`, each once, at the time
`f h p / (f h p - f h q)`. When these times are distinct (a *simple* segment) the hyperplanes
crossed, in order, form the *word* of the segment.

The files `Segment/*.lean` record how words change: the words of two simple segments with
endpoints in the same chambers are related by *flips*, reversals of a block of hyperplanes
through a common point whose intersection has codimension two. This is the geometric input to
the spanning part of the basis theorem for weighted KLR algebras (B. Webster,
arXiv:1209.2463v4, proof of Theorem 2.8): two diagrams given by straight-line galleries are
related by the local relations at codimension-two flats.

## Main definitions

* `Segment.Generic f p`: `p` lies on no hyperplane.
* `Segment.signs f p`: the side of each hyperplane on which `p` lies.
* `Segment.crossTime f p q h`, `Segment.Separates f p q h`.
* `Segment.Simple f p q`: generic endpoints and distinct crossing times.
* `Segment.word f p q`: the hyperplanes crossed by the segment, in order.
* `Segment.Flip f σ w w'`: `w'` is obtained from `w` by reversing a block through a common point
  whose hyperplanes have a two-dimensional span of linear parts; the point lies on the side of
  every other hyperplane reached from the sign vector `σ` after crossing the hyperplanes before
  the block.

## Main results (this file)

* `Segment.mem_word`, `Segment.nodup_word`, `Segment.pairwise_word`: the word of a simple
  segment lists the separating hyperplanes once each, in increasing order of crossing time.
* `Segment.crossTime_pos`, `Segment.crossTime_lt_one`.
* `Segment.sign_segPt`: the side of a hyperplane at a point of a segment.
* `Segment.word_eq_of_pairwise`, `Segment.word_swap`: characterization of the word, and the
  word of the reversed segment.
-/

namespace Categorification.WeightedKLR.Segment

/-! ### Scalar lemmas -/

section Scalar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {a b t : 𝕜}

lemma mul_neg_of_ne_sign (ha : a ≠ 0) (hb : b ≠ 0) (h : (0 < a) ≠ (0 < b)) : a * b < 0 := by
  rcases ha.lt_or_gt with ha | ha <;> rcases hb.lt_or_gt with hb | hb
  · exact (h (propext (iff_of_false (not_lt.2 ha.le) (not_lt.2 hb.le)))).elim
  · exact mul_neg_of_neg_of_pos ha hb
  · exact mul_neg_of_pos_of_neg ha hb
  · exact (h (propext (iff_of_true ha hb))).elim

lemma ne_sign_iff (ha : a ≠ 0) (hb : b ≠ 0) : (0 < a) ≠ (0 < b) ↔ a * b < 0 := by
  refine ⟨mul_neg_of_ne_sign ha hb, fun h e => ?_⟩
  rcases ha.lt_or_gt with ha | ha
  · have hb' : b < 0 := lt_of_not_ge fun hb' =>
      (not_lt.2 ha.le) (e ▸ lt_of_le_of_ne hb' (Ne.symm hb))
    nlinarith
  · have hb' : 0 < b := e ▸ ha
    nlinarith

lemma pos_iff_of_mul_pos (h : 0 < a * b) : (0 < a ↔ 0 < b) := by
  constructor
  · intro ha; exact pos_of_mul_pos_right h ha.le
  · intro hb; exact pos_of_mul_pos_left h hb.le

lemma mul_pos_of_pos_iff (ha : a ≠ 0) (hb : b ≠ 0) (h : 0 < a ↔ 0 < b) : 0 < a * b := by
  rcases ha.lt_or_gt with ha | ha
  · have : b < 0 := lt_of_le_of_ne (not_lt.1 fun hb' => (not_lt.2 ha.le) (h.2 hb')) hb
    exact mul_pos_of_neg_of_neg ha this
  · exact mul_pos ha (h.1 ha)

lemma tau_pos (h : a * b < 0) : 0 < a / (a - b) := by
  rcases lt_or_gt_of_ne (show a ≠ 0 by rintro rfl; simp at h) with ha | ha
  · have hb : 0 < b := by nlinarith
    exact div_pos_of_neg_of_neg ha (by linarith)
  · have hb : b < 0 := by nlinarith
    exact div_pos ha (by linarith)

lemma tau_lt_one (h : a * b < 0) : a / (a - b) < 1 := by
  rcases lt_or_gt_of_ne (show a ≠ 0 by rintro rfl; simp at h) with ha | ha
  · have hb : 0 < b := by nlinarith
    rw [div_lt_one_of_neg (by linarith)]; linarith
  · have hb : b < 0 := by nlinarith
    rw [div_lt_one (by linarith)]; linarith

lemma sub_ne_zero_of_mul_neg (h : a * b < 0) : a - b ≠ 0 := by
  intro e; have : a = b := sub_eq_zero.1 e; subst this; nlinarith

/-- On a segment whose endpoint values have the same sign, the value keeps that sign. -/
lemma mul_val_pos (hs : 0 < a * b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 < a * (a + t * (b - a)) := by
  have ha : a ≠ 0 := by rintro rfl; simp at hs
  rcases ht1.lt_or_eq with ht1 | rfl
  · have : 0 < (1 - t) * (a * a) := mul_pos (by linarith) (mul_self_pos.2 ha)
    nlinarith [mul_nonneg ht0 hs.le]
  · simpa using hs

lemma val_eq_mul (h : a * b < 0) : a + t * (b - a) = (a - b) * (a / (a - b) - t) := by
  have := sub_ne_zero_of_mul_neg h
  field_simp; ring

lemma mul_sub_pos (h : a * b < 0) : 0 < a * (a - b) := by
  nlinarith [mul_self_nonneg a, show a ≠ 0 by rintro rfl; simp at h, mul_self_pos.2
    (show a ≠ 0 by rintro rfl; simp at h)]

/-- The sign of an affine function of `t ∈ [0,1]` with nonzero endpoint values. -/
lemma val_sign (ha : a ≠ 0) (hb : b ≠ 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hne : a * b < 0 → a / (a - b) ≠ t) :
    a + t * (b - a) ≠ 0 ∧ (0 < a + t * (b - a) ↔ (0 < a ↔ ¬(a * b < 0 ∧ a / (a - b) < t))) := by
  by_cases hab : a * b < 0
  · rw [val_eq_mul hab]
    have h1 := mul_sub_pos hab
    have h2 : a / (a - b) - t ≠ 0 := sub_ne_zero.2 (hne hab)
    refine ⟨mul_ne_zero (sub_ne_zero_of_mul_neg hab) h2, ?_⟩
    simp only [hab, true_and]
    rcases lt_or_gt_of_ne h2 with h3 | h3
    · have : t > a / (a - b) := by linarith
      simp only [this, not_true_eq_false, iff_false, not_lt]
      constructor
      · intro hp
        by_contra ha'; simp only [not_le] at ha'
        have : 0 < a - b := pos_of_mul_pos_right h1 ha'.le
        nlinarith
      · intro ha'
        have : a - b < 0 := neg_of_mul_pos_right h1 ha'
        nlinarith
    · have : ¬ (a / (a - b) < t) := by linarith
      simp only [this, not_false_eq_true, iff_true]
      constructor
      · intro hp
        by_contra ha'; simp only [not_lt] at ha'
        have : a - b < 0 := neg_of_mul_pos_right h1 ha'
        nlinarith
      · intro ha'
        have : 0 < a - b := pos_of_mul_pos_right h1 ha'.le
        nlinarith
  · have hs : 0 < a * b := lt_of_le_of_ne (not_lt.1 hab) (mul_ne_zero ha hb).symm
    have := mul_val_pos hs ht0 ht1
    simp only [hab, false_and, not_false_eq_true, iff_true]
    exact ⟨fun e => by simp [e] at this, (pos_iff_of_mul_pos this).symm⟩

lemma val_eq_zero_iff (h : a ≠ b) : a + t * (b - a) = 0 ↔ t = a / (a - b) := by
  rw [eq_div_iff (sub_ne_zero.2 h)]
  constructor <;> intro e <;> linear_combination -e

end Scalar

variable {ι 𝕜 H : Type*} [Fintype ι] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype H] [DecidableEq H] (f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜)

/-- A point on no hyperplane. -/
def Generic (p : ι → 𝕜) : Prop := ∀ h, f h p ≠ 0

/-- The side of each hyperplane on which a point lies. -/
def signs (p : ι → 𝕜) : H → Bool := fun h => decide (0 < f h p)

/-- The hyperplane `h` separates `p` and `q`. -/
def Separates (p q : ι → 𝕜) (h : H) : Prop := (0 < f h p) ≠ (0 < f h q)

instance (p q : ι → 𝕜) (h : H) : Decidable (Separates f p q h) := by
  unfold Separates; infer_instance

/-- The time at which the segment from `p` to `q` meets the hyperplane `h`. -/
def crossTime (p q : ι → 𝕜) (h : H) : 𝕜 := f h p / (f h p - f h q)

/-- A simple segment: generic endpoints and distinct crossing times. -/
def Simple (p q : ι → 𝕜) : Prop :=
  Generic f p ∧ Generic f q ∧ ∀ h g, Separates f p q h → Separates f p q g → h ≠ g →
    crossTime f p q h ≠ crossTime f p q g

/-- The hyperplanes crossed by the segment from `p` to `q`, ordered by crossing time. -/
noncomputable def word (p q : ι → 𝕜) : List H :=
  ((Finset.univ.filter (Separates f p q)).toList).insertionSort
    (fun h g => crossTime f p q h ≤ crossTime f p q g)

/-- The sign vector `σ` with the entries in `l` flipped. -/
def flipSigns (σ : H → Bool) (l : List H) : H → Bool := fun h => xor (σ h) (decide (h ∈ l))

/-- The point at time `t` of the segment from `p` to `q`. -/
def segPt (p q : ι → 𝕜) (t : 𝕜) : ι → 𝕜 := p + t • (q - p)

/-- `w'` is obtained from `w` by reversing a block `B` of at least two hyperplanes which are
exactly the hyperplanes through some point `x`, and whose linear parts span a plane. Off the
block, `x` lies on the sides given by the sign vector `σ` flipped along the hyperplanes before
the block. -/
def Flip (σ : H → Bool) (w w' : List H) : Prop :=
  ∃ a B c : List H, w = a ++ B ++ c ∧ w' = a ++ B.reverse ++ c ∧ 2 ≤ B.length ∧
    (∃ x : ι → 𝕜, (∀ h, f h x = 0 ↔ h ∈ B) ∧ ∀ h, h ∉ B → signs f x h = flipSigns σ a h) ∧
    Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (f h).linear) '' {h | h ∈ B})) = 2

/-- A step between pairs of points: the new segment is simple, its endpoints lie in the
chambers of the old ones, and its word is obtained from the old word by a sequence of flips
(possibly none). -/
def SegStep (x y : (ι → 𝕜) × (ι → 𝕜)) : Prop :=
  Simple f y.1 y.2 ∧ signs f y.1 = signs f x.1 ∧ signs f y.2 = signs f x.2 ∧
    Relation.ReflTransGen (Flip f (signs f x.1)) (word f x.1 x.2) (word f y.1 y.2)


/-! ### Values along a segment -/

omit [Fintype ι] [Fintype H] [DecidableEq H] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma apply_segPt (h : H) (p q : ι → 𝕜) (t : 𝕜) :
    f h (segPt p q t) = f h p + t * (f h q - f h p) := by
  have e : segPt p q t = AffineMap.lineMap p q t := by
    rw [AffineMap.lineMap_apply_module, segPt, smul_sub, sub_smul, one_smul]; abel
  rw [e, AffineMap.apply_lineMap, AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
  ring

variable {f}

section Lemmas

variable {p q : ι → 𝕜} {h : H} {t : 𝕜}

omit [Fintype ι] [Fintype H] [DecidableEq H] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma segPt_zero (p q : ι → 𝕜) : segPt p q 0 = p := by simp [segPt]

omit [Fintype ι] [Fintype H] [DecidableEq H] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma segPt_one (p q : ι → 𝕜) : segPt p q 1 = q := by simp [segPt]

omit [Fintype ι] [Fintype H] [DecidableEq H] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma segPt_swap (p q : ι → 𝕜) (t : 𝕜) : segPt q p t = segPt p q (1 - t) := by
  simp only [segPt, sub_smul, one_smul, smul_sub]; abel

omit [Fintype ι] [Fintype H] [DecidableEq H] [IsStrictOrderedRing 𝕜] in
lemma separates_comm : Separates f p q h ↔ Separates f q p h := ne_comm

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma separates_iff_mul_neg (hp : f h p ≠ 0) (hq : f h q ≠ 0) :
    Separates f p q h ↔ f h p * f h q < 0 := ne_sign_iff hp hq

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma not_separates_iff (hp : f h p ≠ 0) (hq : f h q ≠ 0) :
    ¬ Separates f p q h ↔ 0 < f h p * f h q := by
  rw [separates_iff_mul_neg hp hq, not_lt]
  exact ⟨fun e => lt_of_le_of_ne e (mul_ne_zero hp hq).symm, le_of_lt⟩

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma crossTime_pos (hp : Generic f p) (hq : Generic f q) (hs : Separates f p q h) :
    0 < crossTime f p q h :=
  tau_pos ((separates_iff_mul_neg (hp h) (hq h)).1 hs)

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma crossTime_lt_one (hp : Generic f p) (hq : Generic f q) (hs : Separates f p q h) :
    crossTime f p q h < 1 :=
  tau_lt_one ((separates_iff_mul_neg (hp h) (hq h)).1 hs)

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma apply_segPt_eq_zero_iff (hne : f h p ≠ f h q) :
    f h (segPt p q t) = 0 ↔ t = crossTime f p q h := by
  rw [apply_segPt]; exact val_eq_zero_iff hne

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma apply_segPt_crossTime (hne : f h p ≠ f h q) :
    f h (segPt p q (crossTime f p q h)) = 0 :=
  (apply_segPt_eq_zero_iff hne).2 rfl

omit [Fintype ι] [Fintype H] [DecidableEq H] [IsStrictOrderedRing 𝕜] in
lemma ne_of_separates (hs : Separates f p q h) : f h p ≠ f h q := fun e => hs (by rw [e])

omit [Fintype ι] [Fintype H] [DecidableEq H] in
/-- The side of `h` at a point of the segment from `p` to `q`: the side of `p`, flipped once
the segment has crossed `h`. -/
lemma sign_segPt (hp : f h p ≠ 0) (hq : f h q ≠ 0) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hne : Separates f p q h → crossTime f p q h ≠ t) :
    f h (segPt p q t) ≠ 0 ∧
      (0 < f h (segPt p q t) ↔ (0 < f h p ↔ ¬(Separates f p q h ∧ crossTime f p q h < t))) := by
  rw [apply_segPt, separates_iff_mul_neg hp hq]
  exact val_sign hp hq ht0 ht1 fun hs => hne ((separates_iff_mul_neg hp hq).2 hs)

omit [Fintype ι] [Fintype H] [DecidableEq H] in
/-- A point of the segment lies on `h` only at the crossing time of a separating `h`. -/
lemma separates_of_apply_segPt_eq_zero (hp : f h p ≠ 0) (hq : f h q ≠ 0) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hx : f h (segPt p q t) = 0) :
    Separates f p q h ∧ crossTime f p q h = t := by
  by_contra hc
  exact (sign_segPt hp hq ht0 ht1 fun hs e => hc ⟨hs, e⟩).1 hx

omit [Fintype ι] [Fintype H] in
lemma decide_iff_not (A P : Prop) [Decidable A] [Decidable P] :
    decide (A ↔ ¬ P) = xor (decide A) (decide P) := by
  by_cases hA : A <;> by_cases hP : P <;> simp [hA, hP]

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma signs_segPt (hp : Generic f p) (hq : Generic f q) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hne : ∀ h, Separates f p q h → crossTime f p q h ≠ t) :
    Generic f (segPt p q t) ∧ ∀ h, signs f (segPt p q t) h =
      xor (signs f p h) (decide (Separates f p q h ∧ crossTime f p q h < t)) := by
  refine ⟨fun h => (sign_segPt (hp h) (hq h) ht0 ht1 (hne h)).1, fun h => ?_⟩
  simp only [signs]
  rw [← decide_iff_not]
  exact decide_eq_decide.2 (sign_segPt (hp h) (hq h) ht0 ht1 (hne h)).2

omit [Fintype ι] [Fintype H] [DecidableEq H] in
/-- Points of a segment between two points of a chamber lie in that chamber. -/
lemma mul_apply_segPt_pos (hs : 0 < f h p * f h q) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < f h p * f h (segPt p q t) := by
  rw [apply_segPt]; exact mul_val_pos hs ht0 ht1

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma mul_pos_of_signs_eq {p' : ι → 𝕜} (hp : Generic f p) (hp' : Generic f p')
    (he : signs f p = signs f p') (h : H) : 0 < f h p * f h p' :=
  mul_pos_of_pos_iff (hp h) (hp' h) (by simpa [signs] using congrFun he h)

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma segPt_chamber {p' : ι → 𝕜} (hp : Generic f p) (hp' : Generic f p')
    (he : signs f p = signs f p') (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Generic f (segPt p p' t) ∧ signs f (segPt p p' t) = signs f p := by
  have key := fun h => mul_apply_segPt_pos (mul_pos_of_signs_eq hp hp' he h) ht0 ht1
  refine ⟨fun h e => by simpa [e] using key h, funext fun h => ?_⟩
  simp only [signs]
  exact decide_eq_decide.2 (pos_iff_of_mul_pos (key h)).symm

omit [Fintype ι] [Fintype H] [DecidableEq H] [IsStrictOrderedRing 𝕜] in
lemma separates_congr_left {p' : ι → 𝕜} (he : signs f p = signs f p') (h : H) :
    Separates f p q h ↔ Separates f p' q h := by
  have : (0 < f h p) ↔ (0 < f h p') := by simpa [signs] using congrFun he h
  simp only [Separates, this]

omit [Fintype ι] [Fintype H] [DecidableEq H] [IsStrictOrderedRing 𝕜] in
lemma separates_congr_right {q' : ι → 𝕜} (he : signs f q = signs f q') (h : H) :
    Separates f p q h ↔ Separates f p q' h := by
  rw [separates_comm, separates_congr_left he, separates_comm]

/-! ### The word of a segment -/

omit [Fintype ι] [DecidableEq H] [IsStrictOrderedRing 𝕜] in
lemma mem_word : h ∈ word f p q ↔ Separates f p q h := by
  simp [word, List.mem_insertionSort]

omit [Fintype ι] [DecidableEq H] [IsStrictOrderedRing 𝕜] in
lemma nodup_word : (word f p q).Nodup :=
  (List.perm_insertionSort _ _).nodup_iff.2 (Finset.nodup_toList _)

omit [Fintype ι] [DecidableEq H] [IsStrictOrderedRing 𝕜] in
lemma pairwise_word_le :
    (word f p q).Pairwise (fun h g => crossTime f p q h ≤ crossTime f p q g) := by
  have : Std.Total (fun h g : H => crossTime f p q h ≤ crossTime f p q g) :=
    ⟨fun _ _ => le_total _ _⟩
  have : IsTrans H (fun h g : H => crossTime f p q h ≤ crossTime f p q g) :=
    ⟨fun _ _ _ => le_trans⟩
  exact List.pairwise_insertionSort _ _

omit [Fintype ι] [DecidableEq H] [IsStrictOrderedRing 𝕜] in
/-- The word of a simple segment is strictly sorted by crossing time. -/
lemma pairwise_word (hs : Simple f p q) :
    (word f p q).Pairwise (fun h g => crossTime f p q h < crossTime f p q g) := by
  refine ((pairwise_word_le (f := f) (p := p) (q := q)).and nodup_word).imp_of_mem ?_
  intro a b ha hb ⟨hle, hne⟩
  exact lt_of_le_of_ne hle (hs.2.2 a b (mem_word.1 ha) (mem_word.1 hb) hne)

omit [Fintype ι] [Fintype H] [DecidableEq H] [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] in
lemma _root_.List.nodup_of_pairwise_asymm {α : Type*} {R : α → α → Prop}
    (hR : ∀ a b, R a b → ¬ R b a) {l : List α} (hl : l.Pairwise R) : l.Nodup :=
  hl.imp fun {a b} hab (e : a = b) => by subst e; exact hR a a hab hab

omit [Fintype ι] [Fintype H] [DecidableEq H] [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] in
/-- Two lists strictly sorted by the same asymmetric relation, with the same members, are
equal. -/
lemma _root_.List.eq_of_pairwise_asymm {α : Type*} {R : α → α → Prop}
    (hR : ∀ a b, R a b → ¬ R b a) {l₁ l₂ : List α} (h₁ : l₁.Pairwise R) (h₂ : l₂.Pairwise R)
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  List.Perm.eq_of_pairwise (fun a b _ _ hab hba => (hR a b hab hba).elim) h₁ h₂
    ((List.perm_ext_iff_of_nodup (List.nodup_of_pairwise_asymm hR h₁)
      (List.nodup_of_pairwise_asymm hR h₂)).2 h)

omit [Fintype ι] [DecidableEq H] [IsStrictOrderedRing 𝕜] in
/-- The word of a simple segment is the unique list of the separating hyperplanes sorted by
crossing time. -/
lemma word_eq_of_pairwise (hs : Simple f p q) {l : List H}
    (hl : l.Pairwise (fun h g => crossTime f p q h < crossTime f p q g))
    (hm : ∀ h, h ∈ l ↔ Separates f p q h) : word f p q = l :=
  List.eq_of_pairwise_asymm (fun _ _ h₁ h₂ => lt_asymm h₁ h₂) (pairwise_word hs) hl
    fun h => by rw [mem_word, hm]

omit [Fintype ι] [Fintype H] [DecidableEq H] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma crossTime_swap (hne : f h p ≠ f h q) : crossTime f q p h = 1 - crossTime f p q h := by
  have h1 : f h p - f h q ≠ 0 := sub_ne_zero.2 hne
  have h2 : f h q - f h p ≠ 0 := sub_ne_zero.2 hne.symm
  simp only [crossTime]
  field_simp
  ring

omit [Fintype ι] [Fintype H] [DecidableEq H] in
lemma Simple.swap (hs : Simple f p q) : Simple f q p := by
  refine ⟨hs.2.1, hs.1, fun h g hh hg hne e => hs.2.2 h g (separates_comm.2 hh)
    (separates_comm.2 hg) hne ?_⟩
  rw [crossTime_swap (ne_of_separates (separates_comm.2 hh)),
    crossTime_swap (ne_of_separates (separates_comm.2 hg))] at e
  linarith

omit [Fintype ι] [DecidableEq H] in
/-- The word of the reversed segment is the reversed word. -/
lemma word_swap (hs : Simple f p q) : word f q p = (word f p q).reverse := by
  refine word_eq_of_pairwise hs.swap ?_ fun h => by rw [List.mem_reverse, mem_word,
    separates_comm]
  rw [List.pairwise_reverse]
  refine (pairwise_word hs).imp_of_mem fun ha hb hab => ?_
  rw [crossTime_swap (ne_of_separates (mem_word.1 ha)),
    crossTime_swap (ne_of_separates (mem_word.1 hb))]
  linarith

omit [Fintype ι] [Fintype H] in
lemma flipSigns_congr {σ : H → Bool} {l l' : List H} (h : ∀ x, x ∈ l ↔ x ∈ l') :
    flipSigns σ l = flipSigns σ l' := by
  funext x; simp [flipSigns, h x]

omit [Fintype ι] [IsStrictOrderedRing 𝕜] in
/-- Crossing the whole word of a segment moves from the chamber of `p` to that of `q`. -/
lemma flipSigns_word :
    flipSigns (signs f p) (word f p q) = signs f q := by
  funext h
  simp only [flipSigns, signs, mem_word, Separates]
  by_cases h1 : 0 < f h p <;> by_cases h2 : 0 < f h q <;> simp [h1, h2]

end Lemmas

/-! ### Flips -/

section Flips

variable {σ : H → Bool} {w w' : List H}

omit [Fintype ι] [Fintype H] [IsStrictOrderedRing 𝕜] in
lemma Flip.perm (hf : Flip f σ w w') : w.Perm w' := by
  obtain ⟨a, B, c, rfl, rfl, -⟩ := hf
  exact ((List.reverse_perm B).symm.append_left a).append_right c

omit [Fintype ι] [Fintype H] [IsStrictOrderedRing 𝕜] in
lemma Flip.reverse (hf : Flip f σ w w') (hw : w.Nodup) :
    Flip f (flipSigns σ w) w.reverse w'.reverse := by
  obtain ⟨a, B, c, rfl, rfl, hl, ⟨x, hx, hxs⟩, hr⟩ := hf
  refine ⟨c.reverse, B.reverse, a.reverse, by simp, by simp, by simpa using hl,
    ⟨x, fun h => by rw [hx, List.mem_reverse], fun h hh => ?_⟩,
    by rwa [show {h | h ∈ B.reverse} = {h | h ∈ B} by ext; simp]⟩
  rw [List.mem_reverse] at hh
  rw [hxs h hh]
  have hd : h ∈ a → h ∉ c := by
    intro ha hc
    rw [List.nodup_append, List.nodup_append] at hw
    exact hw.2.2 h (List.mem_append_left _ ha) h hc rfl
  simp only [flipSigns, List.mem_append, List.mem_reverse, hh]
  by_cases ha : h ∈ a <;> by_cases hc : h ∈ c <;> simp_all

omit [Fintype ι] [Fintype H] [IsStrictOrderedRing 𝕜] in
lemma reflTransGen_flip_perm (hr : Relation.ReflTransGen (Flip f σ) w w') : w.Perm w' := by
  induction hr with
  | refl => exact List.Perm.refl _
  | tail _ h ih => exact ih.trans h.perm

omit [Fintype ι] [Fintype H] [IsStrictOrderedRing 𝕜] in
/-- Reversing a chain of flips. -/
lemma reflTransGen_flip_reverse (hr : Relation.ReflTransGen (Flip f σ) w w') (hw : w.Nodup) :
    Relation.ReflTransGen (Flip f (flipSigns σ w)) w.reverse w'.reverse := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail v v' hv h ih =>
    have hp := reflTransGen_flip_perm hv
    refine ih.tail ?_
    rw [flipSigns_congr (σ := σ) (fun x => hp.mem_iff)]
    exact h.reverse (hp.nodup_iff.1 hw)

end Flips

end Categorification.WeightedKLR.Segment
