/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Segment.Sweep
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Simple segments between the same chambers are related by flips

Let `p → q` and `p' → q'` be simple segments with `p`, `p'` in one chamber and `q`, `q'` in
another. Their words are related by flips (`Segment.reflTransGen_segStep`). The proof moves
one endpoint at a time through an auxiliary point `q̃` of the chamber of `q`:
`(p, q) → (p, q̃) → (p', q̃) → (p', q')`. Each leg moves one endpoint inside its chamber
(`Segment.reflTransGen_flip_sweep`, applied to the reversed segment for the legs moving the
end). The point `q̃` is chosen so that both segments `p → q̃`, `p' → q̃` are simple, and so that
no point of the three triangles swept lies on hyperplanes whose linear parts span more than a
plane, except on the edge opposite `q̃`; there this follows from simplicity or from the edge
lying in a chamber.

This is the geometric input to the spanning part of the basis theorem for weighted KLR
algebras (B. Webster, arXiv:1209.2463v4, proof of Theorem 2.8).
-/

namespace Categorification.WeightedKLR.Segment

variable {ι 𝕜 H : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype H] [DecidableEq H] {f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜}

omit [Fintype H] [DecidableEq H] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma sum_smul_apply (T : Finset H) (c : H → 𝕜) (y : ι → 𝕜) :
    (∑ h ∈ T, c h • f h) y = ∑ h ∈ T, c h * f h y := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

omit [DecidableEq H] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- If the linear parts of the hyperplanes in `T` span more than a plane, some combination of
them vanishes at two given points without vanishing identically. -/
lemma exists_comb (T : Finset H) (u v : ι → 𝕜)
    (h3 : 2 < Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (f h).linear) '' (T : Set H)))) :
    ∃ c : H → 𝕜, ∑ h ∈ T, c h * f h u = 0 ∧ ∑ h ∈ T, c h * f h v = 0 ∧
      ∃ y, ∑ h ∈ T, c h * f h y ≠ 0 := by
  classical
  let A : (H → 𝕜) →ₗ[𝕜] 𝕜 × 𝕜 :=
    (∑ h ∈ T, f h u • LinearMap.proj h).prod (∑ h ∈ T, f h v • LinearMap.proj h)
  let B : (H → 𝕜) →ₗ[𝕜] ((ι → 𝕜) →ₗ[𝕜] 𝕜) :=
    ∑ h ∈ T, (LinearMap.proj h : (H → 𝕜) →ₗ[𝕜] 𝕜).smulRight (f h).linear
  have hA : ∀ c, A c = (∑ h ∈ T, c h * f h u, ∑ h ∈ T, c h * f h v) := by
    intro c
    simp [A, mul_comm]
  have hB : ∀ c w, B c w = ∑ h ∈ T, c h * (f h).linear w := by
    intro c w
    simp [B, LinearMap.sum_apply]
  by_contra hcon
  push Not at hcon
  have hker : LinearMap.ker A ≤ LinearMap.ker B := by
    intro c hc
    rw [LinearMap.mem_ker, hA, Prod.mk_eq_zero] at hc
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun w => ?_
    rw [hB, LinearMap.zero_apply]
    have h1 := hcon c hc.1 hc.2 (w + u)
    have h2 : ∑ h ∈ T, c h * f h (w + u) =
        ∑ h ∈ T, c h * (f h).linear w + ∑ h ∈ T, c h * f h u := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [show w + u = w +ᵥ u from rfl, AffineMap.map_vadd, vadd_eq_add]
      ring
    rw [h2, hc.1, add_zero] at h1
    exact h1
  have hrange : Module.finrank 𝕜 (LinearMap.range B) ≤ 2 := by
    have e1 := LinearMap.finrank_range_add_finrank_ker A
    have e2 := LinearMap.finrank_range_add_finrank_ker B
    have e3 := Submodule.finrank_mono hker
    have e4 : Module.finrank 𝕜 (LinearMap.range A) ≤ 2 :=
      (Submodule.finrank_le _).trans (by simp)
    omega
  have hspan : Submodule.span 𝕜 ((fun h => (f h).linear) '' (T : Set H)) ≤
      LinearMap.range B := by
    rw [Submodule.span_le]
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨Pi.single h 1, LinearMap.ext fun w => ?_⟩
    rw [hB]
    simp [Pi.single_apply, Finset.mem_coe.1 hh]
  exact absurd ((Submodule.finrank_mono hspan).trans hrange) (not_le.2 h3)

omit [DecidableEq H] in
/-- The hyperplanes through a point have linear parts spanning at most a plane, if the point is
an affine combination `α u + β v + γ w` with `γ ≠ 0`, and every family of hyperplanes whose
linear parts span more than a plane has a combination vanishing at `u` and `v` but not at
`w`. -/
lemma finrank_le_two_of_comb {u v w z : ι → 𝕜}
    (hav : ∀ T : Finset H,
      2 < Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (f h).linear) '' (T : Set H))) →
      ∃ c : H → 𝕜, ∑ h ∈ T, c h * f h u = 0 ∧ ∑ h ∈ T, c h * f h v = 0 ∧
        ∑ h ∈ T, c h * f h w ≠ 0)
    {α β γ : 𝕜} (hγ : γ ≠ 0) (hz : ∀ h, f h z = α * f h u + β * f h v + γ * f h w) :
    Module.finrank 𝕜
      (Submodule.span 𝕜 ((fun h => (f h).linear) '' {h | f h z = 0})) ≤ 2 := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  set T := Finset.univ.filter fun h => f h z = 0 with hT
  have hTc : (T : Set H) = {h | f h z = 0} := by ext; simp [hT]
  rw [← hTc] at hlt
  obtain ⟨c, hu, hv, hw⟩ := hav T hlt
  have hzero : ∑ h ∈ T, c h * f h z = 0 :=
    Finset.sum_eq_zero fun h hh => by rw [(Finset.mem_filter.1 hh).2, mul_zero]
  have hsum : ∑ h ∈ T, c h * f h z = α * ∑ h ∈ T, c h * f h u + β * ∑ h ∈ T, c h * f h v +
      γ * ∑ h ∈ T, c h * f h w := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ => by rw [hz]; ring
  rw [hzero, hu, hv, mul_zero, mul_zero, zero_add, zero_add] at hsum
  exact hw ((mul_eq_zero.1 hsum.symm).resolve_left hγ)

omit [DecidableEq H] in
/-- Through a point of a simple segment passes at most one hyperplane. -/
lemma finrank_le_two_of_simple {u v : ι → 𝕜} (hs : Simple f u v) {t : 𝕜} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    Module.finrank 𝕜
      (Submodule.span 𝕜 ((fun h => (f h).linear) '' {h | f h (segPt u v t) = 0})) ≤ 2 := by
  classical
  set T := Finset.univ.filter fun h => f h (segPt u v t) = 0 with hT
  have hTc : {h | f h (segPt u v t) = 0} = (T : Set H) := by ext; simp [hT]
  have hcard : T.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    have ha' := separates_of_apply_segPt_eq_zero (hs.1 a) (hs.2.1 a) ht0 ht1
      (Finset.mem_filter.1 ha).2
    have hb' := separates_of_apply_segPt_eq_zero (hs.1 b) (hs.2.1 b) ht0 ht1
      (Finset.mem_filter.1 hb).2
    by_contra hab
    exact hs.2.2 a b ha'.1 hb'.1 hab (ha'.2.trans hb'.2.symm)
  rw [hTc, ← Finset.coe_image]
  exact (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans (by omega))

omit [DecidableEq H] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype H] in
lemma finrank_le_two_of_generic {z : ι → 𝕜} (hz : Generic f z) :
    Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (f h).linear) '' {h | f h z = 0})) ≤ 2 := by
  have : {h | f h z = 0} = ∅ := Set.eq_empty_of_forall_notMem fun h e => hz h e
  rw [this, Set.image_empty, Submodule.span_empty, finrank_bot]
  omega

omit [DecidableEq H] in
/-- A point of a chamber can be moved inside it so that every family of hyperplanes whose
linear parts span more than a plane has a combination vanishing at the two points of each of
finitely many given pairs but not at the new point, while avoiding finitely many further
affine functions. -/
lemma exists_chamber_avoid_combs {q : ι → 𝕜} (hq : Generic f q)
    (P : Set ((ι → 𝕜) × (ι → 𝕜))) (hP : P.Finite) (L : Set ((ι → 𝕜) →ᵃ[𝕜] 𝕜))
    (hL : L.Finite) (hL0 : ∀ ℓ ∈ L, ∃ y, ℓ y ≠ 0) :
    ∃ q', Generic f q' ∧ signs f q' = signs f q ∧ (∀ ℓ ∈ L, ℓ q' ≠ 0) ∧
      ∀ uv ∈ P, ∀ T : Finset H,
        2 < Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (f h).linear) '' (T : Set H))) →
        ∃ c : H → 𝕜, ∑ h ∈ T, c h * f h uv.1 = 0 ∧ ∑ h ∈ T, c h * f h uv.2 = 0 ∧
          ∑ h ∈ T, c h * f h q' ≠ 0 := by
  classical
  set S : Set (Finset H × ((ι → 𝕜) × (ι → 𝕜))) := {x | x.2 ∈ P ∧
    2 < Module.finrank 𝕜 (Submodule.span 𝕜 ((fun h => (f h).linear) '' (x.1 : Set H)))}
    with hSdef
  have hS : S.Finite :=
    (Set.finite_univ.prod hP).subset fun x hx => ⟨Set.mem_univ _, hx.1⟩
  have := hS.to_subtype
  let c : S → H → 𝕜 := fun x => Classical.choose (exists_comb (f := f) x.1.1 x.1.2.1 x.1.2.2 x.2.2)
  have hc : ∀ x : S, ∑ h ∈ x.1.1, c x h * f h x.1.2.1 = 0 ∧
      ∑ h ∈ x.1.1, c x h * f h x.1.2.2 = 0 ∧ ∃ y, ∑ h ∈ x.1.1, c x h * f h y ≠ 0 :=
    fun x => Classical.choose_spec (exists_comb (f := f) x.1.1 x.1.2.1 x.1.2.2 x.2.2)
  let ℓ : S → (ι → 𝕜) →ᵃ[𝕜] 𝕜 := fun x => ∑ h ∈ x.1.1, c x h • f h
  obtain ⟨q', hq', hs, hav⟩ := exists_chamber_avoid hq (L ∪ Set.range ℓ)
    (hL.union (Set.finite_range _)) (by
      rintro m (hm | ⟨x, rfl⟩)
      · exact hL0 m hm
      · obtain ⟨y, hy⟩ := (hc x).2.2
        exact ⟨y, by rw [sum_smul_apply]; exact hy⟩)
  refine ⟨q', hq', hs, fun m hm => hav m (Or.inl hm), fun uv huv T hT => ?_⟩
  let x : S := ⟨(T, uv), huv, hT⟩
  refine ⟨c x, (hc x).1, (hc x).2.1, ?_⟩
  have := hav (ℓ x) (Or.inr ⟨x, rfl⟩)
  rwa [sum_smul_apply] at this

variable [Fintype ι]

/-- **Simple segments between the same two chambers are related by flips.** If `p → q` and
`p' → q'` are simple, with `p`, `p'` in one chamber and `q`, `q'` in one chamber, the word of
`p' → q'` is obtained from that of `p → q` by flips (through codimension-two flats), all taken
from the chamber of `p`. -/
theorem reflTransGen_flip_of_simple (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0)
    {p q p' q' : ι → 𝕜} (hs : Simple f p q) (hs' : Simple f p' q')
    (hpp : signs f p' = signs f p) (hqq : signs f q' = signs f q) :
    Relation.ReflTransGen (Flip f (signs f p)) (word f p q) (word f p' q') := by
  classical
  have hp := hs.1
  have hq := hs.2.1
  have hp' := hs'.1
  have hq' := hs'.2.1
  obtain ⟨r, hr, hrs, hpair, hav⟩ := exists_chamber_avoid_combs hq
    {(p, p'), (q, p), (q', p')} (by simp)
    (Set.range (fun x : {x : H × H // x.1 ≠ x.2} => pairFun f p x.1.1 x.1.2) ∪
      Set.range (fun x : {x : H × H // x.1 ≠ x.2} => pairFun f p' x.1.1 x.1.2))
    ((Set.finite_range _).union (Set.finite_range _)) (by
      rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact pairFun_ne_zero hdist hp x.2
      · exact pairFun_ne_zero hdist hp' x.2)
  have hsr : Simple f p r :=
    simple_of_pairFun hp hr fun h g hne => hpair _ (Or.inl ⟨⟨(h, g), hne⟩, rfl⟩)
  have hsr' : Simple f p' r :=
    simple_of_pairFun hp' hr fun h g hne => hpair _ (Or.inr ⟨⟨(h, g), hne⟩, rfl⟩)
  have hav1 := hav (q, p) (by simp)
  have hav2 := hav (p, p') (by simp)
  have hav3 := hav (q', p') (by simp)
  -- leg 1: move the end from `q` to `r`
  have leg1 : Relation.ReflTransGen (Flip f (signs f p)) (word f p q) (word f p r) := by
    have key := reflTransGen_flip_sweep hdist hrs.symm hs.swap hsr.swap
      fun s t hs0 hs1 ht0 ht1 => by
        by_cases hγ : (1 - t) * s = 0
        · rcases mul_eq_zero.1 hγ with h1 | h0
          · rw [show t = 1 by linarith, segPt_one]
            exact finrank_le_two_of_generic hp
          · rw [h0, segPt_zero]
            exact finrank_le_two_of_simple hs.swap ht0 ht1
        · refine finrank_le_two_of_comb hav1 hγ (α := (1 - t) * (1 - s)) (β := t) fun h => ?_
          simp only [apply_segPt]
          ring
    have key' := reflTransGen_flip_reverse key nodup_word
    rwa [flipSigns_word, word_swap hs, word_swap hsr, List.reverse_reverse,
      List.reverse_reverse] at key'
  -- leg 2: move the start from `p` to `p'`
  have leg2 : Relation.ReflTransGen (Flip f (signs f p)) (word f p r) (word f p' r) :=
    reflTransGen_flip_sweep hdist hpp.symm hsr hsr' fun s t hs0 hs1 ht0 ht1 => by
      by_cases ht : t = 0
      · rw [ht, segPt_zero]
        exact finrank_le_two_of_generic (segPt_chamber hp hp' hpp.symm hs0 hs1).1
      · refine finrank_le_two_of_comb hav2 ht (α := (1 - t) * (1 - s)) (β := (1 - t) * s)
          fun h => ?_
        simp only [apply_segPt]
        ring
  -- leg 3: move the end from `r` to `q'`
  have leg3 : Relation.ReflTransGen (Flip f (signs f p)) (word f p' r) (word f p' q') := by
    have hrq : signs f r = signs f q' := hrs.trans hqq.symm
    have key := reflTransGen_flip_sweep hdist hrq hsr'.swap hs'.swap
      fun s t hs0 hs1 ht0 ht1 => by
        by_cases hγ : (1 - t) * (1 - s) = 0
        · rcases mul_eq_zero.1 hγ with h1 | h1
          · rw [show t = 1 by linarith, segPt_one]
            exact finrank_le_two_of_generic hp'
          · rw [show s = 1 by linarith, segPt_one]
            exact finrank_le_two_of_simple hs'.swap ht0 ht1
        · refine finrank_le_two_of_comb hav3 hγ (α := (1 - t) * s) (β := t) fun h => ?_
          simp only [apply_segPt]
          ring
    have key' := reflTransGen_flip_reverse key nodup_word
    rwa [flipSigns_word, word_swap hsr', word_swap hs', List.reverse_reverse,
      List.reverse_reverse, hpp] at key'
  exact (leg1.trans leg2).trans leg3

/-- **The flip chain.** Two simple segments between the same chambers are joined by one segment
step. -/
theorem reflTransGen_segStep (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0)
    {p q p' q' : ι → 𝕜} (hs : Simple f p q) (hs' : Simple f p' q')
    (hpp : signs f p' = signs f p) (hqq : signs f q' = signs f q) :
    Relation.ReflTransGen (SegStep f) (p, q) (p', q') :=
  Relation.ReflTransGen.single ⟨hs', hpp, hqq, reflTransGen_flip_of_simple hdist hs hs' hpp hqq⟩

end Categorification.WeightedKLR.Segment
