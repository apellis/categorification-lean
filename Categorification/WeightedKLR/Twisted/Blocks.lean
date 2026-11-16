/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Twisted.Arrangement
import Categorification.WeightedKLR.GallerySpan.Flip
import Categorification.WeightedKLR.GalleryRep

/-!
# Blocks of the arrangement of the twisted algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.5, the category
`P` before Proposition 2.20, read as the gallery algebra of the arrangement of walls
`x_b - x_a - ϑ_e` and diagonals `x_b - x_a` on the space of pairs `(x, ϑ)`.

All hyperplanes of this arrangement are linear, and three distinct hyperplanes whose linear
functions span a space of dimension two satisfy a linear relation with nonzero coefficients
(`twRel_of_finrank`). Such a triple is either three diagonals on the three pairs of three
strands, or a diagonal `d` with a wall `W` and the wall `W.comap d.refl` (`twTriple_of_finrank`).
The second case contains the triangles of the fibrewise arrangement and, when `W` lies on the two
strands of `d`, the **loop block**: a loop `e` at the colour of `d`, the wall where one strand
meets the ghost of the other, and the same wall with the strands exchanged
(`Wall.comap_refl_of_isPair`, `Wall.comap_refl_ne_of_isPair`). Nothing about `Γ` is assumed: no
condition (†) and no condition on loops of weight zero.

Blocks have at most three hyperplanes (`twBlock_length_le`), and two hyperplanes through a point
on no other hyperplane are independent (`twIndependent_of_pair`).

The hexagon relations of a block `{d, W, W.comap d.refl}` in the polynomial representation are
`hypOp_mid_diag` and `hypOp_end_diag` at the strands `d.fst, d.snd`; they make no assumption on
the position of `W`, so they hold for the loop block, where the correction term of the diagonal
crossed in the middle is the divided difference of the polynomial of the loop.

## Main results

* `TwRel`, `twRel_of_finrank`: the linear relation of three hyperplanes of a block.
* `TwTriple`, `twTriple_of_finrank`: the classification of three hyperplanes of a block.
* `twIndependent_of_pair`, `twBlock_length_le`.
-/

namespace Categorification.WeightedKLR

open Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace Hyp

/-! ### Evaluation at coordinate vectors -/

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem linear_single_apply (h : Hyp Γ ν) (s : Strand ν) :
    (hypAff h).linear (Pi.single s (1 : 𝕜)) =
      (if s = h.hi then 1 else 0) - (if s = h.lo then 1 else 0) := by
  rw [hypAff_linear_apply]
  simp [Pi.single_apply, eq_comm]

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem edgeVal_zero (h : Hyp Γ ν) : h.edgeVal (0 : Γ.E → 𝕜) = 0 := by
  rcases h with w | d <;> rfl

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- On positions alone, the hyperplane `h` of the big arrangement is the linear part of `h`. -/
theorem twVal_elim_zero (h : Hyp Γ ν) (y : Strand ν → 𝕜) :
    h.twVal (Sum.elim y 0) = (hypAff h).linear y := by
  rw [← twLin_apply, twLin_elim, edgeVal_zero, sub_zero]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem twVal_single_inr_inl (w : Wall Γ ν) (e : Γ.E) :
    Hyp.twVal (Sum.inl w : Hyp Γ ν) (Pi.single (.inr e) (1 : 𝕜)) =
      -(if w.edge = e then 1 else 0) := by
  rw [twVal_single_inr]
  simp [edgeVal, Pi.single_apply]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem twVal_single_inr_inr (d : Diag ν) (e : Γ.E) :
    Hyp.twVal (Sum.inr d : Hyp Γ ν) (Pi.single (.inr e) (1 : 𝕜)) = 0 := by
  rw [twVal_single_inr]
  simp [edgeVal]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem linear_single_sq {h : Hyp Γ ν} {s : Strand ν} (hs : Mem s h) :
    (hypAff h).linear (Pi.single s (1 : 𝕜)) ^ 2 = 1 := by
  rw [linear_single_apply]
  have := h.lo_ne_hi
  rcases hs with rfl | rfl
  · simp [this]
  · simp [Ne.symm this]

end Hyp

/-! ### The linear relation of three hyperplanes of a block -/

/-- Three hyperplanes of the big arrangement whose linear functions satisfy a linear relation
with nonzero coefficients. -/
def TwRel (h₁ h₂ h₃ : Hyp Γ ν) : Prop :=
  ∃ a b c : 𝕜, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    ∀ z, a * h₁.twVal z + b * h₂.twVal z + c * h₃.twVal z = 0

namespace TwRel

variable {h₁ h₂ h₃ : Hyp Γ ν}

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem swap₁₂ (hr : TwRel h₁ h₂ h₃) : TwRel h₂ h₁ h₃ := by
  obtain ⟨a, b, c, ha, hb, hc, e⟩ := hr
  exact ⟨b, a, c, hb, ha, hc, fun z => by linear_combination e z⟩

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem swap₂₃ (hr : TwRel h₁ h₂ h₃) : TwRel h₁ h₃ h₂ := by
  obtain ⟨a, b, c, ha, hb, hc, e⟩ := hr
  exact ⟨a, c, b, ha, hc, hb, fun z => by linear_combination e z⟩

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem rotate (hr : TwRel h₁ h₂ h₃) : TwRel h₂ h₃ h₁ := hr.swap₁₂.swap₂₃

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A single wall cannot be a combination of two diagonals. -/
theorem not_wall_diag_diag {W : Wall Γ ν} {d d' : Diag ν}
    (hr : TwRel (.inl W) (.inr d) (.inr d')) : False := by
  obtain ⟨a, b, c, ha, -, -, e⟩ := hr
  have := e (Pi.single (.inr W.edge) 1)
  rw [Hyp.twVal_single_inr_inl, Hyp.twVal_single_inr_inr, Hyp.twVal_single_inr_inr] at this
  simp only [ite_true, mul_zero, add_zero, mul_neg, mul_one, neg_eq_zero] at this
  exact ha this

end TwRel

/-! ### Two walls and a diagonal -/

omit [DecidableEq I] in
/-- If the signed indicator of `(r', t')` is that of `(r, t)` plus a nonzero multiple of that
of `(p, q)`, then `(r', t')` is `(r, t)` relabelled by the transposition of `p` and `q`. -/
theorem pair_eq_swap_of_indicator {α : Type*} [DecidableEq α] {r t r' t' p q : α}
    (hrt : r ≠ t) (hr't' : r' ≠ t') (hpq : p ≠ q) {γ : 𝕜} (hγ : γ ≠ 0)
    (H : ∀ s, ((if s = t' then (1 : 𝕜) else 0) - if s = r' then 1 else 0) =
      ((if s = t then 1 else 0) - if s = r then 1 else 0) +
        γ * ((if s = q then 1 else 0) - if s = p then 1 else 0)) :
    r' = swap p q r ∧ t' = swap p q t := by
  have hone : ∀ s, ((if s = t' then (1 : 𝕜) else 0) - if s = r' then 1 else 0) = 1 → s = t' := by
    intro s hs
    by_contra hne
    split_ifs at hs <;> first | exact hne ‹_› | norm_num at hs
  have hneg : ∀ s, ((if s = t' then (1 : 𝕜) else 0) - if s = r' then 1 else 0) = -1 →
      s = r' := by
    intro s hs
    by_contra hne
    split_ifs at hs <;> first | exact hne ‹_› | norm_num at hs
  have Lt : ((if t' = t' then (1 : 𝕜) else 0) - if t' = r' then 1 else 0) = 1 := by
    simp [Ne.symm hr't']
  have Lr : ((if r' = t' then (1 : 𝕜) else 0) - if r' = r' then 1 else 0) = -1 := by
    simp [hr't']
  by_cases htp : t = p
  · subst htp
    by_cases hrq : r = q
    · subst hrq
      -- `{r, t} = {p, q}`: both `t'` and `r'` lie in `{t, r}`
      have m₁ : t' = t ∨ t' = r := by
        by_contra hn
        push Not at hn
        have := H t'
        rw [Lt] at this
        simp [hn.1, hn.2] at this
      have m₂ : r' = t ∨ r' = r := by
        by_contra hn
        push Not at hn
        have := H r'
        rw [Lr] at this
        simp [hn.1, hn.2] at this
      rcases m₁ with rfl | rfl
      · exfalso
        have hr' : r' = r := m₂.resolve_left hr't'
        subst hr'
        have := H t'
        simp [hrt.symm] at this
        exact hγ this
      · have hr' : r' = t := m₂.resolve_right hr't'
        subst hr'
        exact ⟨(swap_apply_right _ _).symm, (swap_apply_left _ _).symm⟩
    · -- `t = p`, `r ∉ {p, q}`
      have hr' : r' = r := (hneg r (by rw [H r]; simp [hrt, hrq])).symm
      subst hr'
      refine ⟨(swap_apply_of_ne_of_ne hrt hrq).symm, ?_⟩
      rw [swap_apply_left]
      by_contra hn
      have := H q
      simp [Ne.symm hn, Ne.symm hrq, Ne.symm hpq] at this
      exact hγ this.symm
  by_cases htq : t = q
  · subst htq
    by_cases hrp : r = p
    · subst hrp
      have m₁ : t' = t ∨ t' = r := by
        by_contra hn
        push Not at hn
        have := H t'
        rw [Lt] at this
        simp [hn.1, hn.2] at this
      have m₂ : r' = t ∨ r' = r := by
        by_contra hn
        push Not at hn
        have := H r'
        rw [Lr] at this
        simp [hn.1, hn.2] at this
      rcases m₁ with rfl | rfl
      · exfalso
        have hr' : r' = r := m₂.resolve_left hr't'
        subst hr'
        have := H t'
        simp [hrt.symm] at this
        exact hγ this
      · have hr' : r' = t := m₂.resolve_right hr't'
        subst hr'
        exact ⟨(swap_apply_left _ _).symm, (swap_apply_right _ _).symm⟩
    · -- `t = q`, `r ∉ {p, q}`
      have hr' : r' = r := (hneg r (by rw [H r]; simp [hrt, hrp])).symm
      subst hr'
      refine ⟨(swap_apply_of_ne_of_ne hrp hrt).symm, ?_⟩
      rw [swap_apply_right]
      by_contra hn
      have := H p
      simp [Ne.symm hn, Ne.symm hrp, hpq] at this
      exact hγ this
  -- `t ∉ {p, q}`
  have ht' : t' = t := (hone t (by rw [H t]; simp [Ne.symm hrt, htp, htq])).symm
  subst ht'
  refine ⟨?_, (swap_apply_of_ne_of_ne htp htq).symm⟩
  by_cases hrp : r = p
  · subst hrp
    rw [swap_apply_left]
    by_contra hn
    have := H q
    simp [Ne.symm hn, Ne.symm htq, Ne.symm hpq] at this
    exact hγ this.symm
  by_cases hrq : r = q
  · subst hrq
    rw [swap_apply_right]
    by_contra hn
    have := H p
    simp [Ne.symm hn, Ne.symm htp, hpq] at this
    exact hγ this
  exfalso
  have hr' : r' = r := (hneg r (by rw [H r]; simp [hrt, hrp, hrq])).symm
  subst hr'
  have := H q
  simp [Ne.symm htq, Ne.symm hrq, Ne.symm hpq] at this
  exact hγ this.symm


namespace Hyp

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem linear_single_inl (W : Wall Γ ν) (s : Strand ν) :
    (hypAff (Sum.inl W : Hyp Γ ν)).linear (Pi.single s (1 : 𝕜)) =
      (if s = W.tgt then 1 else 0) - (if s = W.src then 1 else 0) :=
  linear_single_apply _ s

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem linear_single_inr (d : Diag ν) (s : Strand ν) :
    (hypAff (Sum.inr d : Hyp Γ ν)).linear (Pi.single s (1 : 𝕜)) =
      (if s = d.snd then 1 else 0) - (if s = d.fst then 1 else 0) :=
  linear_single_apply _ s

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Either `h` has a strand off `g`, or `g` lies on the two strands of `h`. -/
theorem exists_mem_not_mem_or_isPair (h g : Hyp Γ ν) :
    (∃ s, Mem s h ∧ ¬Mem s g) ∨ g.IsPair h.lo h.hi := by
  by_cases hn : ∃ s, Mem s h ∧ ¬Mem s g
  · exact .inl hn
  · push Not at hn
    exact .inr (isPair_of_forall_mem hn)

end Hyp

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The wall `W` relabelled by a permutation `g` has the strands of `W` moved by `g⁻¹`. -/
theorem Wall.comap_ext {W W' : Wall Γ ν} {g : ColPerm ν} (he : W'.edge = W.edge)
    (hs : W'.src = g.1⁻¹ W.src) (ht : W'.tgt = g.1⁻¹ W.tgt) : W' = W.comap g := by
  apply Subtype.ext
  show (W'.edge, W'.src, W'.tgt) = (W.edge, g.1⁻¹ W.src, g.1⁻¹ W.tgt)
  rw [he, hs, ht]

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Diag.refl_inv_apply (d : Diag ν) (s : Strand ν) :
    d.refl.1⁻¹ s = swap d.fst d.snd s := by
  show (swap d.fst d.snd)⁻¹ s = _
  rw [swap_inv]

namespace TwRel

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The edge coordinate of a relation at the edge `e`. -/
theorem edge_eval {h₁ h₂ h₃ : Hyp Γ ν} {a b c : 𝕜}
    (e : ∀ z, a * h₁.twVal z + b * h₂.twVal z + c * h₃.twVal z = 0) (f : Γ.E) :
    a * h₁.edgeVal (Pi.single f 1) + b * h₂.edgeVal (Pi.single f 1) +
      c * h₃.edgeVal (Pi.single f 1) = 0 := by
  have := e (Pi.single (.inr f) 1)
  rw [Hyp.twVal_single_inr, Hyp.twVal_single_inr, Hyp.twVal_single_inr] at this
  linear_combination -this

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The position part of a relation. -/
theorem strand_eval {h₁ h₂ h₃ : Hyp Γ ν} {a b c : 𝕜}
    (e : ∀ z, a * h₁.twVal z + b * h₂.twVal z + c * h₃.twVal z = 0) (y : Strand ν → 𝕜) :
    a * (hypAff h₁).linear y + b * (hypAff h₂).linear y + c * (hypAff h₃).linear y = 0 := by
  have := e (Sum.elim y 0)
  rwa [Hyp.twVal_elim_zero, Hyp.twVal_elim_zero, Hyp.twVal_elim_zero] at this

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem edgeVal_inl (W : Wall Γ ν) (f : Γ.E) :
    Hyp.edgeVal (Sum.inl W : Hyp Γ ν) (Pi.single f (1 : 𝕜)) = if W.edge = f then 1 else 0 := by
  simp [Hyp.edgeVal, Pi.single_apply]

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem edgeVal_inr (d : Diag ν) (f : Γ.E) :
    Hyp.edgeVal (Sum.inr d : Hyp Γ ν) (Pi.single f (1 : 𝕜)) = 0 := rfl

/-- Two walls and a diagonal with a linear relation: the second wall is the first relabelled by
the transposition of the strands of the diagonal. -/
theorem eq_comap_refl {W W' : Wall Γ ν} {d : Diag ν}
    (hr : TwRel (.inl W) (.inl W') (.inr d)) : W' = W.comap d.refl := by
  classical
  obtain ⟨a, b, c, ha, hb, hc, e⟩ := hr
  have E := edge_eval e W.edge
  rw [edgeVal_inl, edgeVal_inl, edgeVal_inr] at E
  have he : W'.edge = W.edge := by
    by_contra hn
    simp [hn] at E
    exact ha E
  simp only [he, ite_true, mul_one, mul_zero, add_zero] at E
  have H : ∀ s, ((if s = W'.tgt then (1 : 𝕜) else 0) - if s = W'.src then 1 else 0) =
      ((if s = W.tgt then 1 else 0) - if s = W.src then 1 else 0) +
        c / a * ((if s = d.snd then 1 else 0) - if s = d.fst then 1 else 0) := by
    intro s
    have S := strand_eval e (Pi.single s 1)
    rw [Hyp.linear_single_inl, Hyp.linear_single_inl, Hyp.linear_single_inr] at S
    have hb' : b = -a := by linear_combination E
    rw [hb'] at S
    field_simp
    linear_combination -S
  obtain ⟨hs, ht⟩ := pair_eq_swap_of_indicator W.2.2.2 W'.2.2.2 d.fst_ne_snd
    (div_ne_zero hc ha) H
  exact Wall.comap_ext he (by rw [Diag.refl_inv_apply]; exact hs)
    (by rw [Diag.refl_inv_apply]; exact ht)

end TwRel


omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem Wall.ext_of {W W' : Wall Γ ν} (he : W'.edge = W.edge) (hs : W'.src = W.src)
    (ht : W'.tgt = W.tgt) : W' = W := by
  apply Subtype.ext
  show (W'.edge, W'.src, W'.tgt) = (W.edge, W.src, W.tgt)
  rw [he, hs, ht]

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A second wall of the same edge on the two strands of a wall `W` is `W` or its reverse. -/
theorem Wall.rev_of_isPair {W W' : Wall Γ ν} (he : W'.edge = W.edge)
    (hp : Hyp.IsPair (Sum.inl W' : Hyp Γ ν) W.src W.tgt) (hne : W ≠ W') :
    W'.src = W.tgt ∧ W'.tgt = W.src := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (Wall.ext_of he h1 h2).symm hne
  · exact ⟨h1, h2⟩

namespace Hyp

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Distinct diagonals have a strand of one off the other. -/
theorem exists_mem_not_mem_inr {d d' : Diag ν} (hne : d ≠ d') :
    ∃ s, Mem s (Sum.inr d : Hyp Γ ν) ∧ ¬Mem s (Sum.inr d' : Hyp Γ ν) := by
  rcases exists_mem_not_mem_or_isPair (Sum.inr d : Hyp Γ ν) (Sum.inr d') with h | h
  · exact h
  · exact absurd (Diag.eq_of_isPair (Γ := Γ) (isPair_self _) h) hne

end Hyp

namespace TwRel

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The edges of three walls with a linear relation agree. -/
theorem edges_eq {W₁ W₂ W₃ : Wall Γ ν} (hr : TwRel (.inl W₁) (.inl W₂) (.inl W₃)) :
    W₂.edge = W₁.edge ∧ W₃.edge = W₁.edge := by
  obtain ⟨a, b, c, ha, hb, hc, e⟩ := hr
  have E₁ := edge_eval e W₁.edge
  have E₂ := edge_eval e W₂.edge
  have E₃ := edge_eval e W₃.edge
  simp only [edgeVal_inl] at E₁ E₂ E₃
  by_cases h2 : W₂.edge = W₁.edge <;> by_cases h3 : W₃.edge = W₁.edge
  · exact ⟨h2, h3⟩
  · exfalso
    simp [h2, Ne.symm h3] at E₃
    exact hc E₃
  · exfalso
    simp [h3, Ne.symm h2] at E₂
    exact hb E₂
  · exfalso
    simp [h2, h3] at E₁
    exact ha E₁

/-- Three distinct walls with a linear relation cannot have two on the same strands. -/
theorem not_three_walls_of_isPair {W₁ W₂ W₃ : Wall Γ ν}
    (hr : TwRel (.inl W₁) (.inl W₂) (.inl W₃)) (n₁₂ : W₁ ≠ W₂) (n₁₃ : W₁ ≠ W₃)
    (n₂₃ : W₂ ≠ W₃) (hp : Hyp.IsPair (Sum.inl W₂ : Hyp Γ ν) W₁.src W₁.tgt) : False := by
  obtain ⟨e₂, e₃⟩ := hr.edges_eq
  obtain ⟨hs₂, ht₂⟩ := Wall.rev_of_isPair e₂ hp n₁₂
  obtain ⟨a, b, c, ha, hb, hc, e⟩ := hr
  have hmem : ∀ s, Hyp.Mem s (Sum.inl W₃ : Hyp Γ ν) → Hyp.Mem s (Sum.inl W₁ : Hyp Γ ν) := by
    intro s hs
    by_contra hn
    have S := strand_eval e (Pi.single s 1)
    have F₂ : (hypAff (Sum.inl W₂ : Hyp Γ ν)).linear (Pi.single s (1 : 𝕜)) =
        -(hypAff (Sum.inl W₁ : Hyp Γ ν)).linear (Pi.single s 1) := by
      rw [Hyp.linear_single_inl, Hyp.linear_single_inl, hs₂, ht₂]
      ring
    rw [F₂, Hyp.linear_single_eq_zero hn] at S
    have : c * (hypAff (Sum.inl W₃ : Hyp Γ ν)).linear (Pi.single s 1) = 0 := by
      linear_combination S
    exact Hyp.linear_single_ne_zero hs ((mul_eq_zero.1 this).resolve_left hc)
  obtain ⟨hs₁, ht₁⟩ := Wall.rev_of_isPair e₃.symm
    (Hyp.isPair_of_forall_mem hmem) (Ne.symm n₁₃)
  exact n₂₃ (Wall.ext_of (e₃.trans e₂.symm) (by rw [hs₂, ← ht₁]) (by rw [ht₂, ← hs₁])).symm

omit [DecidableEq I] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The position part of a relation, solved for the third hyperplane. -/
theorem strand_rel {h₁ h₂ h₃ : Hyp Γ ν} {a b c : 𝕜} (hc : c ≠ 0)
    (e : ∀ z, a * h₁.twVal z + b * h₂.twVal z + c * h₃.twVal z = 0) (y : Strand ν → 𝕜) :
    (hypAff h₃).linear y = -a / c * (hypAff h₁).linear y + -b / c * (hypAff h₂).linear y := by
  have S := strand_eval e y
  field_simp
  linear_combination S

/-- Three distinct walls never satisfy a linear relation. -/
theorem not_three_walls {W₁ W₂ W₃ : Wall Γ ν} (hr : TwRel (.inl W₁) (.inl W₂) (.inl W₃))
    (n₁₂ : W₁ ≠ W₂) (n₁₃ : W₁ ≠ W₃) (n₂₃ : W₂ ≠ W₃) : False := by
  rcases Hyp.exists_mem_not_mem_or_isPair (Sum.inl W₁ : Hyp Γ ν) (Sum.inl W₂) with d₁₂ | p
  swap
  · exact hr.not_three_walls_of_isPair n₁₂ n₁₃ n₂₃ p
  rcases Hyp.exists_mem_not_mem_or_isPair (Sum.inl W₁ : Hyp Γ ν) (Sum.inl W₃) with d₁₃ | p
  swap
  · exact hr.swap₂₃.not_three_walls_of_isPair n₁₃ n₁₂ n₂₃.symm p
  rcases Hyp.exists_mem_not_mem_or_isPair (Sum.inl W₃ : Hyp Γ ν) (Sum.inl W₂) with d₃₂ | p
  swap
  · exact hr.rotate.swap₁₂.not_three_walls_of_isPair n₂₃.symm n₁₃.symm n₁₂.symm p
  obtain ⟨e₂, e₃⟩ := hr.edges_eq
  obtain ⟨a, b, c, ha, hb, hc, e⟩ := hr
  have E := edge_eval e W₁.edge
  simp only [edgeVal_inl, e₂, e₃, ite_true, mul_one] at E
  obtain ⟨u, v, w, p₁, p₂, p₃⟩ := Hyp.triangle_of_rel d₁₂ d₁₃ d₃₂ (strand_rel hc e)
  set α := -a / c
  set β := -b / c
  have hαβ : α + β = 1 := by
    simp only [α, β]
    field_simp
    linear_combination -E
  have v₁ : Hyp.Mem v (Sum.inl W₁ : Hyp Γ ν) := (p₁.mem_iff v).2 (Or.inr rfl)
  have v₂ : ¬Hyp.Mem v (Sum.inl W₂ : Hyp Γ ν) := fun hv =>
    ((p₂.mem_iff v).1 hv).elim (fun h => p₁.ne h.symm) (fun h => p₃.ne h)
  have v₃ : Hyp.Mem v (Sum.inl W₃ : Hyp Γ ν) := (p₃.mem_iff v).2 (Or.inl rfl)
  have w₁ : ¬Hyp.Mem w (Sum.inl W₁ : Hyp Γ ν) := fun hw =>
    ((p₁.mem_iff w).1 hw).elim (fun h => p₂.ne h.symm) (fun h => p₃.ne h.symm)
  have w₂ : Hyp.Mem w (Sum.inl W₂ : Hyp Γ ν) := (p₂.mem_iff w).2 (Or.inr rfl)
  have w₃ : Hyp.Mem w (Sum.inl W₃ : Hyp Γ ν) := (p₃.mem_iff w).2 (Or.inr rfl)
  have Rv := strand_rel hc e (Pi.single v 1)
  have Rw := strand_rel hc e (Pi.single w 1)
  rw [Hyp.linear_single_eq_zero v₂] at Rv
  rw [Hyp.linear_single_eq_zero w₁] at Rw
  have sv₁ := Hyp.linear_single_sq (𝕜 := 𝕜) v₁
  have sv₃ := Hyp.linear_single_sq (𝕜 := 𝕜) v₃
  have sw₂ := Hyp.linear_single_sq (𝕜 := 𝕜) w₂
  have sw₃ := Hyp.linear_single_sq (𝕜 := 𝕜) w₃
  have hα : α ^ 2 = 1 := by
    have : (hypAff (Sum.inl W₃ : Hyp Γ ν)).linear (Pi.single v 1) ^ 2 =
        α ^ 2 * (hypAff (Sum.inl W₁ : Hyp Γ ν)).linear (Pi.single v 1) ^ 2 := by
      rw [Rv]; ring
    rw [sv₃, sv₁] at this
    linear_combination -this
  have hβ : β ^ 2 = 1 := by
    have : (hypAff (Sum.inl W₃ : Hyp Γ ν)).linear (Pi.single w 1) ^ 2 =
        β ^ 2 * (hypAff (Sum.inl W₂ : Hyp Γ ν)).linear (Pi.single w 1) ^ 2 := by
      rw [Rw]; ring
    rw [sw₃, sw₂] at this
    linear_combination -this
  have h2 : 2 * α = 1 := by
    have : β = 1 - α := by linear_combination hαβ
    rw [this] at hβ
    linear_combination hα - hβ
  nlinarith

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Three distinct diagonals with a linear relation lie on the three pairs of three strands. -/
theorem triangle_diags {d₁ d₂ d₃ : Diag ν} (hr : TwRel (Sum.inr d₁ : Hyp Γ ν) (.inr d₂) (.inr d₃))
    (n₁₂ : d₁ ≠ d₂) (n₁₃ : d₁ ≠ d₃) (n₂₃ : d₂ ≠ d₃) :
    ∃ u v w, Hyp.IsPair (Sum.inr d₁ : Hyp Γ ν) u v ∧ Hyp.IsPair (Sum.inr d₂ : Hyp Γ ν) u w ∧
      Hyp.IsPair (Sum.inr d₃ : Hyp Γ ν) v w := by
  obtain ⟨a, b, c, -, -, hc, e⟩ := hr
  exact Hyp.triangle_of_rel (𝕜 := 𝕜) (Hyp.exists_mem_not_mem_inr n₁₂)
    (Hyp.exists_mem_not_mem_inr n₁₃) (Hyp.exists_mem_not_mem_inr n₂₃.symm) (strand_rel hc e)

end TwRel

/-! ### The shapes of the triples of a block -/

/-- The shapes of three distinct hyperplanes of the big arrangement satisfying a linear
relation: three diagonals on the three pairs of three strands, or a diagonal `d` with a wall `W`
and the wall `W.comap d.refl`, in any position. -/
def TwTriple (h₁ h₂ h₃ : Hyp Γ ν) : Prop :=
  (∃ d₁ d₂ d₃ : Diag ν, h₁ = .inr d₁ ∧ h₂ = .inr d₂ ∧ h₃ = .inr d₃ ∧
    ∃ u v w, h₁.IsPair u v ∧ h₂.IsPair u w ∧ h₃.IsPair v w) ∨
  (∃ (d : Diag ν) (W : Wall Γ ν), h₁ = .inr d ∧ h₂ = .inl W ∧ h₃ = .inl (W.comap d.refl)) ∨
  (∃ (d : Diag ν) (W : Wall Γ ν), h₁ = .inl W ∧ h₂ = .inr d ∧ h₃ = .inl (W.comap d.refl)) ∨
  (∃ (d : Diag ν) (W : Wall Γ ν), h₁ = .inl W ∧ h₂ = .inl (W.comap d.refl) ∧ h₃ = .inr d)

namespace TwRel

/-- Three distinct hyperplanes with a linear relation have one of the shapes of `TwTriple`. -/
theorem twTriple {h₁ h₂ h₃ : Hyp Γ ν} (hr : TwRel h₁ h₂ h₃) (n₁₂ : h₁ ≠ h₂) (n₁₃ : h₁ ≠ h₃)
    (n₂₃ : h₂ ≠ h₃) : TwTriple h₁ h₂ h₃ := by
  have ne : ∀ {d d' : Diag ν}, (Sum.inr d : Hyp Γ ν) ≠ .inr d' → d ≠ d' :=
    fun h e => h (congrArg _ e)
  have neW : ∀ {W W' : Wall Γ ν}, (Sum.inl W : Hyp Γ ν) ≠ .inl W' → W ≠ W' :=
    fun h e => h (congrArg _ e)
  rcases h₁ with W₁ | d₁ <;> rcases h₂ with W₂ | d₂ <;> rcases h₃ with W₃ | d₃
  · exact (hr.not_three_walls (neW n₁₂) (neW n₁₃) (neW n₂₃)).elim
  · exact .inr (.inr (.inr ⟨d₃, W₁, rfl, by rw [hr.eq_comap_refl], rfl⟩))
  · exact .inr (.inr (.inl ⟨d₂, W₁, rfl, rfl, by rw [hr.swap₂₃.eq_comap_refl]⟩))
  · exact (hr.not_wall_diag_diag).elim
  · exact .inr (.inl ⟨d₁, W₂, rfl, rfl, by rw [hr.rotate.eq_comap_refl]⟩)
  · exact (hr.swap₁₂.not_wall_diag_diag).elim
  · exact (hr.rotate.rotate.not_wall_diag_diag).elim
  · exact .inl ⟨d₁, d₂, d₃, rfl, rfl, rfl, hr.triangle_diags (ne n₁₂) (ne n₁₃) (ne n₂₃)⟩

end TwRel

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- In a triple of a block, the third hyperplane is a wall exactly when exactly one of the first
two is. -/
theorem TwTriple.isLeft_eq {h₁ h₂ h₃ : Hyp Γ ν} (ht : TwTriple h₁ h₂ h₃) :
    h₃.isLeft = xor h₁.isLeft h₂.isLeft := by
  rcases ht with ⟨_, _, _, rfl, rfl, rfl, -⟩ | ⟨_, _, rfl, rfl, rfl⟩ | ⟨_, _, rfl, rfl, rfl⟩ |
    ⟨_, _, rfl, rfl, rfl⟩ <;> rfl

/-! ### Linear relations from the dimension of a block -/

namespace Hyp

/-- The linear function of a hyperplane is not a multiple of that of another one. -/
theorem twLin_ne_smul {h g : Hyp Γ ν} (hne : h ≠ g) (c : 𝕜) : g.twLin ≠ c • h.twLin := by
  intro e
  obtain ⟨x, hx, hgx⟩ := twHdist h g hne
  rw [twAff_apply] at hx hgx
  apply hgx
  rw [← twLin_apply, e, LinearMap.smul_apply, twLin_apply, hx, smul_zero]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem twLin_ne_zero (h : Hyp Γ ν) : h.twLin ≠ 0 := by
  intro e
  rcases h with W | d
  · have := LinearMap.congr_fun e (Pi.single (.inr W.edge) 1)
    rw [twLin_apply, twVal_single_inr_inl, LinearMap.zero_apply] at this
    simp at this
  · have := LinearMap.congr_fun e (Pi.single (.inl d.snd) 1)
    rw [twLin_apply, twVal_inr, LinearMap.zero_apply] at this
    simp [d.fst_ne_snd.symm] at this

end Hyp

/-- In a span of linear functions of dimension two, three distinct hyperplanes satisfy a linear
relation with nonzero coefficients. -/
theorem twRel_of_finrank {B : List (Hyp Γ ν)}
    (hB : Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h : Hyp Γ ν => h.twLin) '' {h | h ∈ B})) = 2)
    {h₁ h₂ h₃ : Hyp Γ ν} (m₁ : h₁ ∈ B) (m₂ : h₂ ∈ B) (m₃ : h₃ ∈ B) (n₁₂ : h₁ ≠ h₂)
    (n₁₃ : h₁ ≠ h₃) (n₂₃ : h₂ ≠ h₃) : TwRel h₁ h₂ h₃ := by
  have hli : LinearIndependent 𝕜 ![h₁.twLin, h₂.twLin] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      rw [zero_smul, add_zero] at hab
      exact ⟨(smul_eq_zero.1 hab).resolve_right (Hyp.twLin_ne_zero h₁), rfl⟩
    · exfalso
      apply Hyp.twLin_ne_smul n₁₂ (-a / b)
      refine LinearMap.ext fun z => ?_
      have := LinearMap.congr_fun hab z
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        LinearMap.zero_apply] at this
      simp only [LinearMap.smul_apply, smul_eq_mul]
      field_simp
      linear_combination this
  have hle : Submodule.span 𝕜 (Set.range ![h₁.twLin, h₂.twLin]) ≤
      Submodule.span 𝕜 ((fun h : Hyp Γ ν => h.twLin) '' {h | h ∈ B}) := by
    rw [Matrix.range_cons_cons_empty]
    exact Submodule.span_mono (Set.insert_subset_iff.2
      ⟨⟨h₁, m₁, rfl⟩, Set.singleton_subset_iff.2 ⟨h₂, m₂, rfl⟩⟩)
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hli, hB]; rfl)
  have h3 : h₃.twLin ∈ Submodule.span 𝕜 (Set.range ![h₁.twLin, h₂.twLin]) :=
    heq ▸ Submodule.subset_span ⟨h₃, m₃, rfl⟩
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at h3
  obtain ⟨α, β, e⟩ := h3
  have hα : α ≠ 0 := by
    rintro rfl
    exact Hyp.twLin_ne_smul n₂₃ β (by rw [← e, zero_smul, zero_add])
  have hβ : β ≠ 0 := by
    rintro rfl
    exact Hyp.twLin_ne_smul n₁₃ α (by rw [← e, zero_smul, add_zero])
  refine ⟨α, β, -1, hα, hβ, by norm_num, fun z => ?_⟩
  have := LinearMap.congr_fun e z
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Hyp.twLin_apply] at this
  linear_combination this

/-- The classification of three distinct hyperplanes of a block of the big arrangement. -/
theorem twTriple_of_finrank {B : List (Hyp Γ ν)}
    (hB : Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h : Hyp Γ ν => h.twLin) '' {h | h ∈ B})) = 2)
    {h₁ h₂ h₃ : Hyp Γ ν} (m₁ : h₁ ∈ B) (m₂ : h₂ ∈ B) (m₃ : h₃ ∈ B) (n₁₂ : h₁ ≠ h₂)
    (n₁₃ : h₁ ≠ h₃) (n₂₃ : h₂ ≠ h₃) : TwTriple h₁ h₂ h₃ :=
  (twRel_of_finrank hB m₁ m₂ m₃ n₁₂ n₁₃ n₂₃).twTriple n₁₂ n₁₃ n₂₃

/-! ### The loop block -/

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- On the two strands of a diagonal `d`, the wall `W.comap d.refl` is `W` with its strands
exchanged: together with `d` they form the loop block, where one strand meets the ghost of the
other along a loop. -/
theorem Wall.comap_refl_of_isPair {W : Wall Γ ν} {d : Diag ν}
    (hp : Hyp.IsPair (Sum.inl W : Hyp Γ ν) d.fst d.snd) :
    (W.comap d.refl).src = W.tgt ∧ (W.comap d.refl).tgt = W.src := by
  show d.refl.1⁻¹ W.src = W.tgt ∧ d.refl.1⁻¹ W.tgt = W.src
  rw [Diag.refl_inv_apply, Diag.refl_inv_apply]
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · change W.src = d.fst at h1
    change W.tgt = d.snd at h2
    rw [h1, h2, swap_apply_left, swap_apply_right]
    exact ⟨rfl, rfl⟩
  · change W.src = d.snd at h1
    change W.tgt = d.fst at h2
    rw [h1, h2, swap_apply_left, swap_apply_right]
    exact ⟨rfl, rfl⟩

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- The two walls of the loop block are distinct. -/
theorem Wall.comap_refl_ne_of_isPair {W : Wall Γ ν} {d : Diag ν}
    (hp : Hyp.IsPair (Sum.inl W : Hyp Γ ν) d.fst d.snd) : W.comap d.refl ≠ W := by
  intro e
  have hs := (Wall.comap_refl_of_isPair hp).1
  rw [e] at hs
  exact W.2.2.2 hs

/-! ### Independence of two hyperplanes through a generic point of a flat -/

namespace Hyp

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Relabelling by the reflection of a diagonal through `z` preserves the hyperplanes
through `z`. -/
theorem twVal_comap_refl_eq_zero {d : Diag ν} {z : Strand ν ⊕ Γ.E → 𝕜}
    (hd : Hyp.twVal (Sum.inr d : Hyp Γ ν) z = 0) {h : Hyp Γ ν} (hh : h.twVal z = 0) :
    (h.comap d.refl).twVal z = 0 := by
  rw [twVal_eq] at hd hh ⊢
  have hc : Hyp.comap (Γ := Γ) d.refl h =
      Hyp.comap (Γ := Γ.withWeight (z ∘ Sum.inr)) d.refl h := by
    rcases h with w | d' <;> rfl
  rw [hc]
  exact comap_val_eq_zero (act_refl_of_val hd) hh

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
theorem IsPair.isPair_fst_snd {d : Diag ν} {h : Hyp Γ ν} {a b : Strand ν}
    (hd : Hyp.IsPair (Sum.inr d : Hyp Γ ν) a b) (hh : h.IsPair a b) : h.IsPair d.fst d.snd := by
  rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · change d.fst = a at h1
    change d.snd = b at h2
    rw [h1, h2]
    exact hh
  · change d.fst = b at h1
    change d.snd = a at h2
    rw [h1, h2]
    exact hh.symm

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A diagonal and another hyperplane through `z` sharing a strand give a third hyperplane
through `z`; on the two strands of the diagonal this is the reversed wall of the loop block. -/
theorem twExists_third_of_shared {z : Strand ν ⊕ Γ.E → 𝕜} {d : Diag ν} {h : Hyp Γ ν}
    (zd : Hyp.twVal (Sum.inr d : Hyp Γ ν) z = 0) (zh : h.twVal z = 0)
    (hne : (Sum.inr d : Hyp Γ ν) ≠ h) {a : Strand ν} (ad : Mem a (Sum.inr d : Hyp Γ ν))
    (ah : Mem a h) : ∃ g : Hyp Γ ν, g.twVal z = 0 ∧ g ≠ .inr d ∧ g ≠ h := by
  refine ⟨h.comap d.refl, twVal_comap_refl_eq_zero zd zh, ?_⟩
  obtain ⟨c, hca, pd⟩ := exists_other ad
  obtain ⟨b, hba, ph⟩ := exists_other ah
  by_cases hbc : b = c
  · subst hbc
    rcases h with W | d'
    · have hp := pd.isPair_fst_snd ph
      exact ⟨Sum.inl_ne_inr, fun e => Wall.comap_refl_ne_of_isPair hp (Sum.inl_injective e)⟩
    · exact absurd (congrArg Sum.inr (Diag.eq_of_isPair (Γ := Γ) pd ph)) hne
  have pg := comap_refl_isPair pd hba hbc ph
  exact ⟨IsPair.ne_of_not_mem pd pg.symm hba hbc, IsPair.ne_of_not_mem ph pg hca (Ne.symm hbc)⟩

end Hyp

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Two distinct hyperplanes of the big arrangement through a point on no other hyperplane are
independent: two walls, or two hyperplanes on disjoint strands. -/
theorem twIndependent_of_pair {z : Strand ν ⊕ Γ.E → 𝕜} {h₁ h₂ : Hyp Γ ν}
    (hz : ∀ h : Hyp Γ ν, h.twVal z = 0 ↔ h ∈ [h₁, h₂]) (hne : h₁ ≠ h₂) :
    h₁.Independent h₂ := by
  have z₁ := (hz h₁).2 (by simp)
  have z₂ := (hz h₂).2 (by simp)
  by_cases hl : h₁.isLeft ∧ h₂.isLeft
  · exact .inl hl
  by_cases hdj : Disjoint h₁.strands h₂.strands
  · exact .inr hdj
  exfalso
  obtain ⟨a, a₁, a₂⟩ := Finset.not_disjoint_iff.1 hdj
  rw [Hyp.mem_strands_iff] at a₁ a₂
  have third : ∀ (d : Diag ν) (h : Hyp Γ ν), Hyp.twVal (Sum.inr d : Hyp Γ ν) z = 0 →
      h.twVal z = 0 → (Sum.inr d : Hyp Γ ν) ≠ h → Hyp.Mem a (Sum.inr d : Hyp Γ ν) →
      Hyp.Mem a h → ({Sum.inr d, h} : Set (Hyp Γ ν)) = {h₁, h₂} → False := by
    intro d h zd zh n ad ah e
    obtain ⟨g, zg, g₁, g₂⟩ := Hyp.twExists_third_of_shared zd zh n ad ah
    have hg := (hz g).1 zg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    have : g ∈ ({h₁, h₂} : Set (Hyp Γ ν)) := by rcases hg with rfl | rfl <;> simp
    rw [← e] at this
    rcases this with rfl | rfl
    · exact g₁ rfl
    · exact g₂ rfl
  rcases h₁ with W₁ | d₁
  · rcases h₂ with W₂ | d₂
    · exact hl ⟨rfl, rfl⟩
    · exact third d₂ _ z₂ z₁ (Ne.symm hne) a₂ a₁ (Set.pair_comm _ _)
  · exact third d₁ h₂ z₁ z₂ hne a₁ a₂ rfl

/-- A block of the big arrangement, a set of hyperplanes whose linear functions span a space of
dimension two, has at most three hyperplanes. -/
theorem twBlock_length_le {B : List (Hyp Γ ν)}
    (hB : Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h : Hyp Γ ν => h.twLin) '' {h | h ∈ B})) = 2)
    (hn : B.Nodup) : B.length ≤ 3 := by
  match B, hB, hn with
  | [], _, _ => simp
  | [_], _, _ => simp
  | [_, _], _, _ => simp
  | [_, _, _], _, _ => simp
  | h₁ :: h₂ :: h₃ :: h₄ :: l, hB, hn =>
    exfalso
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    obtain ⟨⟨n₁₂, n₁₃, n₁₄, -⟩, ⟨n₂₃, n₂₄, -⟩, ⟨n₃₄, -⟩, -⟩ := hn
    have t₁₂₃ := twTriple_of_finrank hB (by simp) (by simp) (by simp) n₁₂ n₁₃ n₂₃
    have t₁₂₄ := twTriple_of_finrank hB (by simp) (by simp) (h₃ := h₄) (by simp) n₁₂ n₁₄ n₂₄
    have t₁₃₄ := twTriple_of_finrank hB (by simp) (by simp) (h₃ := h₄) (by simp) n₁₃ n₁₄ n₃₄
    have t₂₃₄ := twTriple_of_finrank hB (by simp) (by simp) (h₃ := h₄) (by simp) n₂₃ n₂₄ n₃₄
    have l₃ := t₁₂₃.isLeft_eq
    have l₄ := t₁₂₄.isLeft_eq
    have l₄' := t₁₃₄.isLeft_eq
    have l₄'' := t₂₃₄.isLeft_eq
    have l₁ : h₁.isLeft = false := by
      revert l₃ l₄ l₄' l₄''
      cases h₁.isLeft <;> cases h₂.isLeft <;> cases h₃.isLeft <;> cases h₄.isLeft <;> decide
    have l₂ : h₂.isLeft = false := by
      revert l₃ l₄ l₄' l₄''
      cases h₁.isLeft <;> cases h₂.isLeft <;> cases h₃.isLeft <;> cases h₄.isLeft <;> decide
    rcases t₁₂₃ with ⟨-, -, d₃, -, -, e₃, u, v, w, p₁, p₂, p₃⟩ | ⟨_, _, -, e, -⟩ |
      ⟨_, _, e, -, -⟩ | ⟨_, _, e, -, -⟩ <;> try simp [e] at l₁ l₂
    rcases t₁₂₄ with ⟨-, -, d₄, -, -, e₄, u', v', w', p₁', p₂', p₄⟩ | ⟨_, _, -, e, -⟩ |
      ⟨_, _, e, -, -⟩ | ⟨_, _, e, -, -⟩ <;> try simp [e] at l₁ l₂
    have hu : u' = u := by
      rcases (p₁.mem_iff u').1 ((p₁'.mem_iff u').2 (Or.inl rfl)) with e | e
      · exact e
      · exfalso
        subst e
        rcases (p₂.mem_iff u').1 ((p₂'.mem_iff u').2 (Or.inl rfl)) with e' | e'
        · exact p₁.ne e'.symm
        · exact p₃.ne e'
    subst hu
    have hv := p₁.right_unique p₁'
    have hw := p₂.right_unique p₂'
    subst hv hw
    rw [e₃] at p₃ n₃₄
    rw [e₄] at p₄ n₃₄
    exact n₃₄ (congrArg Sum.inr (Diag.eq_of_isPair (Γ := Γ) p₃ p₄))

end Categorification.WeightedKLR
