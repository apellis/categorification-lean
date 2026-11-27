/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CoevaluationTrace

/-!
# The cut trace through a corner

Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3. A ring-theoretic criterion for the cut trace
`coevaluationTrace cut ⊆ eA` to be the unique maximal submodule. The complementary idempotent
`1 - l` of a corner `lAl ∋ e` is a sum of cut idempotents, and a ring map `Φ : A → B` kills the
cuts, is injective on the corner and onto `B`, and every nonzero element of `Φ(e) B` generates
`Φ(e)` on the right.

In the application `A` is the tensor product algebra with two red strands, `l` is the idempotent
of the loadings ending in the second red strand, and `Φ` erases both red strands.
-/

namespace Categorification.Stendhal

open MulOpposite

variable {A B : Type*} [Ring A] [Ring B] {e : A}

/-- The quotient by a proper submodule `T` of `eA` is simple exactly for `T`, once every vector
outside `T` generates `e` on the right. -/
theorem eq_iff_isSimpleModule_of_generates (he : IsIdempotentElem e)
    (T : Submodule Aᵐᵒᵖ (rIdeal e)) (hT : T ≠ ⊤)
    (hunit : ∀ x : rIdeal e, x ∉ T → ∃ b : A, x.val * b = e)
    (N : Submodule Aᵐᵒᵖ (rIdeal e)) :
    N = T ↔ IsSimpleModule Aᵐᵒᵖ (rIdeal e ⧸ N) := by
  let g : rIdeal e := ⟨e, he.eq⟩
  have hle (P : Submodule Aᵐᵒᵖ (rIdeal e)) (hp : P ≠ ⊤) : P ≤ T := by
    intro x hx
    by_contra hxT
    obtain ⟨b, hb⟩ := hunit x hxT
    have hg : g ∈ P := by
      have hb' : op b • x = g := Subtype.ext hb
      exact hb' ▸ P.smul_mem (op b) hx
    apply hp (eq_top_iff.mpr ?_)
    intro y _
    have hy : op y.val • g = y := Subtype.ext y.property
    exact hy ▸ P.smul_mem (op y.val) hg
  rw [isSimpleModule_iff_isCoatom, isCoatom_iff_ge_of_le]
  constructor
  · rintro rfl
    exact ⟨hT, fun P hp _ => hle P hp⟩
  · rintro ⟨hn, hmax⟩
    exact le_antisymm (hle N hn) (hmax _ hT (hle N hn))

/-- **The trace criterion through a corner** (Webster, arXiv:1309.3796v3, §7.1, Lemma 7.3).
Let `e` lie in the corner of an idempotent `l`, let `1 - l` be a finite sum of cut idempotents,
and let `Φ : A → B` be a surjective ring map killing the cuts and injective on `lAl`. If `Φ(e)`
is nonzero and every nonzero element of `Φ(e) B` generates `Φ(e)` on the right, then the cut
trace is the unique submodule of `eA` with simple quotient. -/
theorem coevaluationTrace_eq_iff_isSimpleModule_of_corner {J : Type*} {l : A}
    (he : IsIdempotentElem e) (hl : IsIdempotentElem l) (hel : e * l = e) (hle : l * e = e)
    (cut : J → A) (hcut : ∀ j, IsIdempotentElem (cut j))
    (s : Finset J) (hs : 1 - l = ∑ j ∈ s, cut j)
    (Φ : A →+* B) (hΦ : ∀ j, Φ (cut j) = 0)
    (hinj : ∀ y : A, l * y * l = y → Φ y = 0 → y = 0)
    (hsurj : Function.Surjective Φ)
    (hgen : ∀ y : B, Φ e * y = y → y ≠ 0 → ∃ c : B, y * c = Φ e)
    (hne : Φ e ≠ 0)
    (N : Submodule Aᵐᵒᵖ (rIdeal e)) :
    N = coevaluationTrace cut ↔ IsSimpleModule Aᵐᵒᵖ (rIdeal e ⧸ N) := by
  have hlx (x : rIdeal e) : l * x.val = x.val := by
    rw [← x.property, ← mul_assoc, hle]
  have hcorner (x : rIdeal e) (b : A) : l * (x.val * b * e) * l = x.val * b * e := by
    rw [mul_assoc l, mul_assoc (x.val * b) e l, hel, ← mul_assoc, ← mul_assoc, hlx]
  apply eq_iff_isSimpleModule_of_generates he
  · intro htop
    have hg : (⟨e, he.eq⟩ : rIdeal e) ∈ coevaluationTrace cut := htop ▸ Submodule.mem_top
    exact hne (coevaluationTrace_le_characterKernel cut Φ hΦ hg)
  · intro x hx
    have hΦx : Φ x.val ≠ 0 := by
      intro h0
      apply hx
      have hxl : x.val * l = 0 := by
        apply hinj
        · rw [← mul_assoc, hlx, mul_assoc, hl.eq]
        · rw [map_mul, h0, zero_mul]
      have hsum : x = ∑ j ∈ s, op (cut j) • x := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        change x.val = ∑ j ∈ s, x.val * cut j
        rw [← Finset.mul_sum, ← hs, mul_sub, mul_one, hxl, sub_zero]
      rw [hsum]
      refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨j, ?_⟩
      change x.val * cut j * cut j = x.val * cut j
      rw [mul_assoc, (hcut j).eq]
    obtain ⟨c, hc⟩ := hgen (Φ x.val) (by rw [← map_mul, x.property]) hΦx
    obtain ⟨b, rfl⟩ := hsurj c
    refine ⟨b * e, ?_⟩
    rw [← mul_assoc]
    apply sub_eq_zero.mp
    apply hinj
    · rw [mul_sub, sub_mul, hcorner, hle, hel]
    · rw [map_sub, map_mul, map_mul, hc, ← map_mul, he.eq, sub_self]

end Categorification.Stendhal
