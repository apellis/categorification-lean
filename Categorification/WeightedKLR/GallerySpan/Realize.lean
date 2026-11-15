/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Gallery
import Categorification.WeightedKLR.GallerySpan.Bridge
import Categorification.WeightedKLR.Segment.Perturb

/-!
# Words whose prefixes are chambers

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.8.

A word `w` of hyperplanes is *good* from a sign vector `σ` (`GoodWord σ w`) if it has no
repetitions and flipping `σ` along every prefix of `w` gives a full chamber. Along a good word
the gallery `C.flips w` crosses one hyperplane at each step, and ends at the chamber
`flipSigns C.1 w` (`FullChamber.flips_val`). The word of a simple segment is good
(`goodWord_word`), and goodness is preserved by flips (`GoodWord.flip`), hence along the flip
chains joining the words of two simple segments between the same chambers.

## Main definitions

* `Realizable σ`: the sign vector `σ` is that of a generic configuration.
* `GoodWord σ w`.

## Main results

* `realizable_near`: perturbing a point `x` towards `y` realizes the signs of `y` on the
  hyperplanes through `x` and those of `x` elsewhere.
* `GoodWord.cons`, `GoodWord.append`, `FullChamber.flips_val`.
* `goodWord_word`, `GoodWord.flip`, `GoodWord.reflTransGen`.
-/

namespace Categorification.WeightedKLR

open Segment FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- A sign vector realized by a generic configuration. -/
def Realizable (σ : Hyp Γ ν → Bool) : Prop := ∃ p, IsGeneric Γ p ∧ fullSigns p = σ

/-- A word without repetitions all of whose prefixes flip `σ` to a full chamber. -/
def GoodWord (σ : Hyp Γ ν → Bool) (w : List (Hyp Γ ν)) : Prop :=
  w.Nodup ∧ ∀ j, Realizable (flipSigns σ (w.take j))

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem flipSigns_nil (σ : Hyp Γ ν → Bool) : flipSigns σ [] = σ := by
  funext x; simp [flipSigns]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem flipSigns_flipSign {σ : Hyp Γ ν → Bool} {h : Hyp Γ ν} {l : List (Hyp Γ ν)}
    (hl : h ∉ l) : flipSigns (flipSign σ h) l = flipSigns σ (h :: l) := by
  funext x
  simp only [flipSigns, flipSign, List.mem_cons]
  by_cases hx : x = h
  · subst hx; simp [hl]
  · simp [hx]

/-! ### Perturbation -/

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Hyp.val_two_smul_sub (h : Hyp Γ ν) (x y : Strand ν → 𝕜) :
    h.val (2 • x - y) = 2 * h.val x - h.val y := by
  rw [Hyp.val_eq, Hyp.val_eq, Hyp.val_eq]
  simp only [Pi.sub_apply, Pi.smul_apply]
  ring

/-- Perturbing `x` towards `y`: the signs of `y` on the hyperplanes through `x`, those of `x`
elsewhere. -/
theorem realizable_near {x y : Strand ν → 𝕜} {S : Hyp Γ ν → Prop} [DecidablePred S]
    (hx : ∀ h, h.val x = 0 ↔ S h) (hy : ∀ h, S h → h.val y ≠ 0) :
    Realizable (fun h => if S h then fullSigns y h else fullSigns x h) := by
  obtain ⟨t, ht0, -, ht⟩ := exists_pos_small (fun h : Hyp Γ ν => h.val x)
    (fun h => h.val y - h.val x) (fun h => h.val y - h.val x)
  have := fullSigns_eq_of (z := (1 - t) • x + t • y)
    (σ := fun h => if S h then fullSigns y h else fullSigns x h) fun h => by
      rw [Hyp.val_segment]
      by_cases hS : S h
      · simp only [(hx h).2 hS, hS, ↓reduceIte]
        simp only [sub_zero, zero_add, fullSigns, decide_eq_true_eq]
        exact ⟨mul_ne_zero ht0.ne' (hy h hS), mul_pos_iff_of_pos_left ht0⟩
      · simp only [hS, ↓reduceIte]
        have ha : h.val x ≠ 0 := fun e => hS ((hx h).1 e)
        obtain ⟨h1, h2⟩ := pos_add_iff_of_abs_lt ha (ht h ha).1
        simp only [fullSigns, decide_eq_true_eq]
        exact ⟨h2, h1⟩
  exact ⟨_, this.1, this.2⟩

/-- Reflecting a chamber through a point `x`: the signs on the hyperplanes through `x` are
reversed, the others are those of `x`. -/
theorem realizable_reflect {x : Strand ν → 𝕜} {S : Hyp Γ ν → Prop} [DecidablePred S]
    (hx : ∀ h, h.val x = 0 ↔ S h) {τ : Hyp Γ ν → Bool} (hτ : Realizable τ) :
    Realizable (fun h => if S h then !τ h else fullSigns x h) := by
  obtain ⟨y, hy, rfl⟩ := hτ
  have hv : ∀ h, S h → h.val (2 • x - y) = -h.val y := fun h hS => by
    rw [Hyp.val_two_smul_sub, (hx h).2 hS]; ring
  convert realizable_near hx (y := 2 • x - y) (fun h hS => by
    rw [hv h hS]; exact neg_ne_zero.2 (hy h)) using 2 with h
  by_cases hS : S h
  · simp only [hS, ↓reduceIte, fullSigns, hv h hS]
    rcases lt_or_gt_of_ne (hy h) with hn | hn
    · simp [not_lt.2 hn.le, neg_pos.2 hn]
    · simp [hn, not_lt.2 (neg_neg_of_pos hn).le]
  · simp only [hS, ↓reduceIte]

/-! ### Good words -/

omit [IsStrictOrderedRing 𝕜] in
theorem GoodWord.cons {C : FullChamber Γ ν} {h : Hyp Γ ν} {w : List (Hyp Γ ν)}
    (hw : GoodWord C.1 (h :: w)) :
    (C.flipH h).1 = flipSign C.1 h ∧ C.Adjacent (C.flipH h) h ∧ GoodWord (C.flipH h).1 w := by
  have hr : ∃ p, IsGeneric Γ p ∧ fullSigns p = flipSign C.1 h := by
    have := hw.2 1
    rwa [List.take_succ_cons, List.take_zero, ← flipSigns_flipSign List.not_mem_nil,
      flipSigns_nil] at this
  have e : (C.flipH h).1 = flipSign C.1 h := by rw [flipH_of hr]
  refine ⟨e, adjacent_iff_eq_flipSign.2 e, (List.nodup_cons.1 hw.1).2, fun j => ?_⟩
  have := hw.2 (j + 1)
  rwa [List.take_succ_cons, ← flipSigns_flipSign fun hm =>
    (List.nodup_cons.1 hw.1).1 (List.mem_of_mem_take hm), ← e] at this

omit [IsStrictOrderedRing 𝕜] in
theorem GoodWord.append {C : FullChamber Γ ν} {a b : List (Hyp Γ ν)}
    (hw : GoodWord C.1 (a ++ b)) : GoodWord (C.flips a).1 b := by
  induction a generalizing C with
  | nil => exact hw
  | cons h a ih => exact ih (GoodWord.cons hw).2.2

omit [IsStrictOrderedRing 𝕜] in
theorem GoodWord.of_append {σ : Hyp Γ ν → Bool} {a b : List (Hyp Γ ν)}
    (hw : GoodWord σ (a ++ b)) : GoodWord σ a := by
  refine ⟨(List.nodup_append.1 hw.1).1, fun j => ?_⟩
  have := hw.2 (min j a.length)
  rw [List.take_append, Nat.sub_eq_zero_of_le (min_le_right _ _), List.take_zero,
    List.append_nil] at this
  have e : a.take (min j a.length) = a.take j := by
    rcases le_total j a.length with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, List.take_of_length_le h, List.take_length]
  rwa [e] at this

omit [IsStrictOrderedRing 𝕜] in
/-- Along a good word, the gallery ends at the flipped sign vector. -/
theorem FullChamber.flips_val {C : FullChamber Γ ν} {w : List (Hyp Γ ν)}
    (hw : GoodWord C.1 w) : (C.flips w).1 = flipSigns C.1 w := by
  induction w generalizing C with
  | nil => exact (flipSigns_nil _).symm
  | cons h w ih =>
    obtain ⟨e, -, hw'⟩ := hw.cons
    rw [flips_cons, ih hw', e, flipSigns_flipSign (List.nodup_cons.1 hw.1).1]

omit [IsStrictOrderedRing 𝕜] in
/-- Two good words with the same hyperplanes end at the same chamber. -/
theorem FullChamber.flips_eq_of_perm {C : FullChamber Γ ν} {w w' : List (Hyp Γ ν)}
    (hw : GoodWord C.1 w) (hw' : GoodWord C.1 w') (hp : w.Perm w') :
    C.flips w = C.flips w' :=
  Subtype.ext (by rw [flips_val hw, flips_val hw', flipSigns_congr fun x => hp.mem_iff])

/-! ### Words of simple segments and flips -/

/-- The word of a simple segment is good. -/
theorem goodWord_word {p q : Strand ν → 𝕜} (hs : Simple (hypAff (Γ := Γ)) p q) :
    GoodWord (fullSigns p) (word (hypAff (Γ := Γ)) p q) := by
  refine ⟨nodup_word, fun j => ?_⟩
  obtain ⟨t, -, -, hg, hsg⟩ := exists_prefix_chamber hs j
  exact ⟨_, hg, hsg⟩

/-- Flips preserve good words. -/
theorem GoodWord.flip {σ : Hyp Γ ν → Bool} {w w' : List (Hyp Γ ν)} (hw : GoodWord σ w)
    (hf : Flip (hypAff (Γ := Γ)) σ w w') : GoodWord σ w' := by
  classical
  refine ⟨hf.perm.nodup_iff.1 hw.1, fun j => ?_⟩
  obtain ⟨a, B, c, rfl, rfl, -, ⟨x, hx0, hxs⟩, -⟩ := hf
  have hnd := hw.1
  rw [List.append_assoc, List.nodup_append] at hnd
  obtain ⟨-, hBc, haBc⟩ := hnd
  have hBnd : B.Nodup := (List.nodup_append.1 hBc).1
  have hsame : ∀ l : List (Hyp Γ ν), (∀ y, y ∈ l ↔ y ∈ (a ++ B ++ c).take j) →
      Realizable (flipSigns σ l) := fun l hl => by
    rw [flipSigns_congr hl]; exact hw.2 j
  rw [List.append_assoc, List.take_append, List.take_append]
  by_cases hj : j ≤ a.length
  · refine hsame _ fun y => ?_
    rw [List.append_assoc, List.take_append, List.take_append]
    simp [Nat.sub_eq_zero_of_le hj]
  rw [List.take_of_length_le (by omega : a.length ≤ j)]
  set i := j - a.length
  by_cases hi : B.length ≤ i
  · refine hsame _ fun y => ?_
    rw [List.append_assoc, List.take_append, List.take_append,
      List.take_of_length_le (by omega : a.length ≤ j), List.take_of_length_le hi,
      List.take_of_length_le (by simpa using hi)]
    simp [i]
  push Not at hi
  rw [Nat.sub_eq_zero_of_le (by first | omega | (simp only [List.length_reverse]; omega)),
    List.take_zero, List.append_nil]
  set m := B.length - i
  have hτ : Realizable (flipSigns σ (a ++ B.take m)) := by
    have := hw.2 (a.length + m)
    rwa [List.append_assoc, List.take_append, List.take_of_length_le (by omega),
      Nat.add_sub_cancel_left, List.take_append, Nat.sub_eq_zero_of_le (by omega),
      List.take_zero, List.append_nil] at this
  have hB : ∀ h, h.val x = 0 ↔ h ∈ B := hx0
  have hr := realizable_reflect hB hτ
  convert hr using 1
  funext h
  have hrev : h ∈ B.reverse.take i ↔ h ∈ B.drop m := by
    rw [List.take_reverse, List.mem_reverse]
  by_cases hhB : h ∈ B
  · have ha : h ∉ a := fun ha => haBc h ha h (List.mem_append_left _ hhB) rfl
    have hdisj : h ∈ B.take m ↔ h ∉ B.drop m := by
      constructor
      · exact fun h1 h2 => List.disjoint_take_drop hBnd le_rfl h1 h2
      · intro h2
        rw [← List.take_append_drop m B, List.mem_append] at hhB
        exact hhB.resolve_right h2
    simp only [flipSigns, List.mem_append, ha, false_or, hrev, hhB, ↓reduceIte]
    by_cases h2 : h ∈ B.drop m <;> simp [h2, hdisj]
  · have h1 : h ∉ B.drop m := fun h2 => hhB (List.mem_of_mem_drop h2)
    simp only [hhB, ↓reduceIte]
    rw [show fullSigns x h = flipSigns σ a h from hxs h hhB]
    simp only [flipSigns, List.mem_append, hrev, h1, or_false]
    congr 1; exact decide_eq_decide.2 Iff.rfl

theorem GoodWord.reflTransGen {σ : Hyp Γ ν → Bool} {w w' : List (Hyp Γ ν)} (hw : GoodWord σ w)
    (hr : Relation.ReflTransGen (Flip (hypAff (Γ := Γ)) σ) w w') : GoodWord σ w' := by
  induction hr with
  | refl => exact hw
  | tail _ hf ih => exact ih.flip hf

end Categorification.WeightedKLR
