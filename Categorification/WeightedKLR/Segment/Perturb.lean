/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Segment
import Mathlib.Order.Interval.Set.Infinite

/-!
# Perturbing points inside a chamber

A chamber of an arrangement over an ordered field is not covered by finitely many affine
hyperplanes: a point can be moved inside its chamber off any finite family of affine functions
that are not identically zero. As a first application, every pair of chambers is joined by a
simple segment (`Segment.exists_simple`), and every prefix of the word of a simple segment is
the set of hyperplanes crossed up to some time (`Segment.exists_prefix_chamber`).

These are the general-position arguments in the proof of the basis theorem for weighted KLR
algebras (B. Webster, arXiv:1209.2463v4, proof of Theorem 2.13).
-/

namespace Categorification.WeightedKLR.Segment

section Field

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- In an open interval there is a point avoiding the roots of finitely many affine functions
`t ↦ a i + t * b i` that are not identically zero. -/
lemma exists_avoid {κ : Type*} (s : Finset κ) (a b : κ → 𝕜)
    (hab : ∀ i ∈ s, a i ≠ 0 ∨ b i ≠ 0) {lo hi : 𝕜} (h : lo < hi) :
    ∃ t, lo < t ∧ t < hi ∧ ∀ i ∈ s, a i + t * b i ≠ 0 := by
  classical
  obtain ⟨t, ⟨h1, h2⟩, ht⟩ :=
    (Set.Ioo_infinite h).exists_notMem_finset (s.image fun i => -a i / b i)
  refine ⟨t, h1, h2, fun i hi e => ?_⟩
  by_cases hb : b i = 0
  · rw [hb, mul_zero, add_zero] at e
    rcases hab i hi with h | h <;> contradiction
  · exact ht (Finset.mem_image.2 ⟨i, hi, by rw [div_eq_iff hb]; linarith⟩)

/-- Finitely many nonzero linear forms have a common nonzero value. -/
lemma exists_forall_apply_ne_zero {V : Type*} [AddCommGroup V] [Module 𝕜 V] {κ : Type*}
    (s : Finset κ) (L : κ → V →ₗ[𝕜] 𝕜) : ∃ v, ∀ i ∈ s, L i ≠ 0 → L i v ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨v, hv⟩ := ih
    by_cases hLj : L j = 0
    · refine ⟨v, fun i hi hne => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact (hne hLj).elim
      · exact hv i hi hne
    obtain ⟨w, hw⟩ : ∃ w, L j w ≠ 0 := by
      by_contra hc
      exact hLj (LinearMap.ext fun w => by simpa using not_not.1 (not_exists.1 hc w))
    obtain ⟨t, -, -, ht⟩ := exists_avoid ((insert j s).filter (fun i => L i ≠ 0))
      (fun i => L i v) (fun i => L i w) (fun i hi => by
        obtain ⟨hi, hne⟩ := Finset.mem_filter.1 hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact Or.inr hw
        · exact Or.inl (hv i hi hne)) zero_lt_one
    refine ⟨v + t • w, fun i hi hne => ?_⟩
    simpa [map_add, map_smul, smul_eq_mul] using ht i (Finset.mem_filter.2 ⟨hi, hne⟩)

/-- Perturbations by small amounts keep the signs of finitely many nonzero values. -/
lemma exists_pos_small {κ : Type*} (s : Finset κ) (c d : κ → 𝕜) (hc : ∀ i ∈ s, c i ≠ 0) :
    ∃ δ, 0 < δ ∧ ∀ ε, 0 ≤ ε → ε < δ → ∀ i ∈ s, 0 < c i * (c i + ε * d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert j s hj ih =>
    obtain ⟨δ₀, hδ₀, h₀⟩ := ih fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hcj : c j ≠ 0 := hc j (Finset.mem_insert_self _ _)
    have hpos : 0 < |c j| / (|d j| + 1) := div_pos (abs_pos.2 hcj) (by positivity)
    refine ⟨min δ₀ (|c j| / (|d j| + 1)), lt_min hδ₀ hpos, fun ε hε0 hε i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · have hε' : ε < |c i| / (|d i| + 1) := lt_of_lt_of_le hε (min_le_right _ _)
      have h1 : ε * |d i| < |c i| := by
        rw [lt_div_iff₀ (by positivity)] at hε'
        nlinarith [abs_nonneg (d i)]
      have h2 : |c i * (ε * d i)| < c i * c i := by
        rw [abs_mul, abs_mul, abs_of_nonneg hε0, ← abs_mul_abs_self (c i)]
        exact mul_lt_mul_of_pos_left h1 (abs_pos.2 hcj)
      nlinarith [neg_abs_le (c i * (ε * d i))]
    · exact h₀ ε hε0 (lt_of_lt_of_le hε (min_le_left _ _)) i hi

end Field

section Affine

variable {ι 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma _root_.AffineMap.apply_add_smul (ℓ : (ι → 𝕜) →ᵃ[𝕜] 𝕜) (q v : ι → 𝕜) (t : 𝕜) :
    ℓ (q + t • v) = ℓ q + t * ℓ.linear v := by
  rw [add_comm q, ← vadd_eq_add, AffineMap.map_vadd, vadd_eq_add, map_smul, smul_eq_mul,
    add_comm]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma _root_.AffineMap.apply_eq_of_linear_eq_zero (ℓ : (ι → 𝕜) →ᵃ[𝕜] 𝕜) (h : ℓ.linear = 0)
    (x y : ι → 𝕜) : ℓ x = ℓ y := by
  have := ℓ.linearMap_vsub x y
  rw [h, LinearMap.zero_apply, vsub_eq_sub] at this
  exact (sub_eq_zero.1 this.symm)

/-- A point can be moved off finitely many affine functions that are not identically zero,
keeping the strict signs of finitely many affine functions nonzero at it. -/
lemma exists_perturb {κ : Type*} [Fintype κ] (g : κ → (ι → 𝕜) →ᵃ[𝕜] 𝕜) (q : ι → 𝕜)
    (hq : ∀ j, g j q ≠ 0) (L : Set ((ι → 𝕜) →ᵃ[𝕜] 𝕜)) (hL : L.Finite)
    (hL0 : ∀ ℓ ∈ L, ∃ y, ℓ y ≠ 0) :
    ∃ q', (∀ j, 0 < g j q * g j q') ∧ ∀ ℓ ∈ L, ℓ q' ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := exists_forall_apply_ne_zero hL.toFinset (fun ℓ => ℓ.linear)
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_small Finset.univ (fun j => g j q)
    (fun j => (g j).linear v) (fun j _ => hq j)
  obtain ⟨t, ht0, htδ, ht⟩ := exists_avoid hL.toFinset (fun ℓ => ℓ q) (fun ℓ => ℓ.linear v)
    (fun ℓ hℓ => by
      rw [Set.Finite.mem_toFinset] at hℓ
      by_cases h0 : ℓ.linear = 0
      · left
        obtain ⟨y, hy⟩ := hL0 ℓ hℓ
        rwa [ℓ.apply_eq_of_linear_eq_zero h0 q y]
      · exact Or.inr (hv ℓ (hL.mem_toFinset.2 hℓ) h0)) hδ
  refine ⟨q + t • v, fun j => ?_, fun ℓ hℓ => ?_⟩
  · rw [AffineMap.apply_add_smul]
    exact hsmall t ht0.le htδ j (Finset.mem_univ _)
  · rw [AffineMap.apply_add_smul]
    exact ht ℓ (hL.mem_toFinset.2 hℓ)

end Affine

section Arrangement

variable {ι 𝕜 H : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype H] [DecidableEq H] {f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜}

omit [DecidableEq H] in
/-- A generic point can be moved inside its chamber off finitely many affine functions that
are not identically zero. -/
lemma exists_chamber_avoid {q : ι → 𝕜} (hq : Generic f q) (L : Set ((ι → 𝕜) →ᵃ[𝕜] 𝕜))
    (hL : L.Finite) (hL0 : ∀ ℓ ∈ L, ∃ y, ℓ y ≠ 0) :
    ∃ q', Generic f q' ∧ signs f q' = signs f q ∧ ∀ ℓ ∈ L, ℓ q' ≠ 0 := by
  obtain ⟨q', h1, h2⟩ := exists_perturb f q hq L hL hL0
  refine ⟨q', fun h e => by simpa [e] using h1 h, funext fun h => ?_, h2⟩
  simp only [signs]
  exact decide_eq_decide.2 (pos_iff_of_mul_pos (h1 h)).symm

omit [Fintype H] [DecidableEq H] in
/-- Two crossing times along a segment agree exactly when a cross-multiplied identity holds. -/
lemma crossTime_eq_iff {p q : ι → 𝕜} {h g : H} (hh : f h p ≠ f h q) (hg : f g p ≠ f g q) :
    crossTime f p q h = crossTime f p q g ↔ f h p * f g q = f g p * f h q := by
  rw [crossTime, crossTime, div_eq_div_iff (sub_ne_zero.2 hh) (sub_ne_zero.2 hg)]
  constructor <;> intro e <;> linear_combination -e

/-- The affine function vanishing at `y` exactly when the segment from `p` to `y` meets `h` and
`g` at the same time. -/
def pairFun (f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜) (p : ι → 𝕜) (h g : H) : (ι → 𝕜) →ᵃ[𝕜] 𝕜 :=
  f h p • f g - f g p • f h

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
lemma pairFun_apply (p y : ι → 𝕜) (h g : H) :
    pairFun f p h g y = f h p * f g y - f g p * f h y := by
  simp [pairFun]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
lemma pairFun_ne_zero (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0) {p : ι → 𝕜}
    (hp : Generic f p) {h g : H} (hne : h ≠ g) : ∃ y, pairFun f p h g y ≠ 0 := by
  obtain ⟨y, hy1, hy2⟩ := hdist h g hne
  exact ⟨y, by rw [pairFun_apply, hy1]; simpa using ⟨hp h, hy2⟩⟩

omit [Fintype H] [DecidableEq H] in
/-- The segment from `p` to `q` is simple as soon as `q` avoids every `pairFun f p h g`. -/
lemma simple_of_pairFun {p q : ι → 𝕜} (hp : Generic f p) (hq : Generic f q)
    (hpair : ∀ h g, h ≠ g → pairFun f p h g q ≠ 0) : Simple f p q := by
  refine ⟨hp, hq, fun h g hh hg hne e => hpair h g hne ?_⟩
  rw [crossTime_eq_iff (ne_of_separates hh) (ne_of_separates hg)] at e
  rw [pairFun_apply]; linarith

omit [DecidableEq H] in
/-- Any two chambers are joined by a simple segment. -/
theorem exists_simple (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0) {p q : ι → 𝕜}
    (hp : Generic f p) (hq : Generic f q) :
    ∃ p' q', Simple f p' q' ∧ signs f p' = signs f p ∧ signs f q' = signs f q := by
  obtain ⟨q', hq', hs, hav⟩ := exists_chamber_avoid hq
    (Set.range fun x : {x : H × H // x.1 ≠ x.2} => pairFun f p x.1.1 x.1.2)
    (Set.finite_range _) (by
      rintro _ ⟨x, rfl⟩
      exact pairFun_ne_zero hdist hp x.2)
  exact ⟨p, q', simple_of_pairFun hp hq' fun h g hne => hav _ ⟨⟨(h, g), hne⟩, rfl⟩, rfl, hs⟩

omit [DecidableEq H] in
lemma exists_between_finsets {S₁ S₂ : Finset 𝕜} (h₁ : S₁.Nonempty) (h₂ : S₂.Nonempty)
    (h : ∀ x ∈ S₁, ∀ y ∈ S₂, x < y) : ∃ t, (∀ x ∈ S₁, x < t) ∧ ∀ y ∈ S₂, t < y := by
  have hlt := h _ (S₁.max'_mem h₁) _ (S₂.min'_mem h₂)
  refine ⟨(S₁.max' h₁ + S₂.min' h₂) / 2, fun x hx => ?_, fun y hy => ?_⟩
  · have := S₁.le_max' x hx; linarith
  · have := S₂.min'_le y hy; linarith

/-- Every prefix of the word of a simple segment is the set of hyperplanes crossed before
some time `t`; the point at time `t` is generic and lies in the corresponding chamber. -/
theorem exists_prefix_chamber {p q : ι → 𝕜} (hs : Simple f p q) (j : ℕ) :
    ∃ t, 0 < t ∧ t < 1 ∧ Generic f (segPt p q t) ∧
      signs f (segPt p q t) = flipSigns (signs f p) ((word f p q).take j) := by
  classical
  set w := word f p q with hw
  have hsplit : w = w.take j ++ w.drop j := (List.take_append_drop j w).symm
  have hpw := pairwise_word hs
  rw [← hw, hsplit, List.pairwise_append] at hpw
  obtain ⟨t, ht1, ht2⟩ := exists_between_finsets (S₁ := insert 0 ((w.take j).map
      (crossTime f p q)).toFinset) (S₂ := insert 1 ((w.drop j).map (crossTime f p q)).toFinset)
    ⟨0, Finset.mem_insert_self _ _⟩ ⟨1, Finset.mem_insert_self _ _⟩ (by
      intro x hx y hy
      simp only [Finset.mem_insert, List.mem_toFinset, List.mem_map] at hx hy
      have hmem : ∀ h ∈ w, 0 < crossTime f p q h ∧ crossTime f p q h < 1 := fun h hh =>
        ⟨crossTime_pos hs.1 hs.2.1 (mem_word.1 hh), crossTime_lt_one hs.1 hs.2.1
          (mem_word.1 hh)⟩
      rcases hx with rfl | ⟨a, ha, rfl⟩ <;> rcases hy with rfl | ⟨b, hb, rfl⟩
      · exact zero_lt_one
      · exact (hmem b (List.mem_of_mem_drop hb)).1
      · exact (hmem a (List.mem_of_mem_take ha)).2
      · exact hpw.2.2 a ha b hb)
  have h0t : 0 < t := ht1 0 (Finset.mem_insert_self _ _)
  have ht1' : t < 1 := ht2 1 (Finset.mem_insert_self _ _)
  have hA : ∀ h ∈ w.take j, crossTime f p q h < t := fun h hh =>
    ht1 _ (Finset.mem_insert_of_mem (List.mem_toFinset.2 (List.mem_map_of_mem hh)))
  have hB : ∀ h ∈ w.drop j, t < crossTime f p q h := fun h hh =>
    ht2 _ (Finset.mem_insert_of_mem (List.mem_toFinset.2 (List.mem_map_of_mem hh)))
  have hmemw : ∀ h, Separates f p q h → h ∈ w.take j ∨ h ∈ w.drop j := fun h hh => by
    rw [← List.mem_append, ← hsplit]; exact mem_word.2 hh
  have hne : ∀ h, Separates f p q h → crossTime f p q h ≠ t := fun h hh e => by
    rcases hmemw h hh with hh | hh
    · exact (hA h hh).ne e
    · exact (hB h hh).ne' e
  obtain ⟨hgen, hsg⟩ := signs_segPt hs.1 hs.2.1 h0t.le ht1'.le hne
  refine ⟨t, h0t, ht1', hgen, funext fun h => ?_⟩
  rw [hsg, flipSigns]
  congr 1
  refine decide_eq_decide.2 ⟨fun ⟨hh, hlt⟩ => ?_, fun hh => ⟨mem_word.1
    (List.mem_of_mem_take hh), hA h hh⟩⟩
  rcases hmemw h hh with hh | hh
  · exact hh
  · exact absurd hlt (not_lt.2 (hB h hh).le)

end Arrangement

end Categorification.WeightedKLR.Segment
