/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GallerySpan.Spanning

/-!
# Straight-line galleries span, with the polynomial at the bottom

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.8 and
Theorem 2.13, spanning half, with the dots at the bottom of the diagram. Products in the gallery
algebra are composition (`x * y` is `y` followed by `x`), so the polynomial at the bottom is the
right-hand factor: the elements `r g E * segGallery P C E * poly f` span the gallery algebra.

The proof moves the polynomial of `GalleryAlgebra.span_segGallery` from the top to the bottom of
the gallery. A polynomial commutes with a step across a wall, and with a step across a diagonal
up to a correction without steps (`GalleryAlgebra.poly_mul_t_sub_mem`); so moving it through a
gallery with `n` steps costs an element with fewer than `n` steps
(`GalleryAlgebra.poly_mul_galList_sub_mem`), which is handled by induction on the number of
steps.

## Main results

* `GalleryAlgebra.span_segGallery_mul_poly`: for any choice of simple segments, the elements
  `r g E * segGallery P C E * poly f` span the gallery algebra.
* `GalleryAlgebra.span_segGallery_mul_monomial`: the same with `f` a monomial.
-/

namespace Categorification.WeightedKLR

open Segment FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

/-- A polynomial commutes with a step up to an element without steps. -/
theorem poly_mul_t_sub_mem (f : PolyRing ν k) (C C' : FullChamber Γ ν) :
    (poly f * t C C' - t C C' * poly f : GalleryAlgebra k Γ ν) ∈ stepFilt k Γ ν 0 := by
  by_cases hadj : ∃ h, C.Adjacent C' h
  · obtain ⟨h, hh⟩ := hadj
    cases h with
    | inl w => rw [t_mul_poly_inl hh, sub_self]; exact Submodule.zero_mem _
    | inr d =>
      rw [t_mul_poly_inr hh, sub_add_cancel_left]
      exact Submodule.neg_mem _
        (mul_mem_stepFilt (m := 0) (n := 0) (poly_mem_stepFilt _ 0) (r_mem_stepFilt _ _ 0))
  · push Not at hadj
    rw [t_eq_zero hadj, mul_zero, zero_mul, sub_zero]
    exact Submodule.zero_mem _

/-- Moving a polynomial from the top to the bottom of a gallery with at most `n + 1` steps
costs an element with at most `n` steps. -/
theorem poly_mul_galList_sub_mem (f : PolyRing ν k) (C : FullChamber Γ ν) (w : List (Hyp Γ ν))
    {n : ℕ} (hn : w.length ≤ n + 1) :
    (poly f * galList k C w - galList k C w * poly f : GalleryAlgebra k Γ ν) ∈
      stepFilt k Γ ν n := by
  induction w generalizing C n with
  | nil =>
    rw [galList_nil, e_mul_poly, sub_self]; exact Submodule.zero_mem _
  | cons h w ih =>
    simp only [List.length_cons] at hn
    rw [galList_cons]
    have hdec : poly f * (galList k (C.flipH h) w * t C (C.flipH h)) -
        galList k (C.flipH h) w * t C (C.flipH h) * poly f =
        (poly f * galList k (C.flipH h) w - galList k (C.flipH h) w * poly f) *
          t C (C.flipH h) +
        galList k (C.flipH h) w * (poly f * t C (C.flipH h) - t C (C.flipH h) * poly f) := by
      noncomm_ring
    rw [hdec]
    refine Submodule.add_mem _ ?_ ?_
    · rcases w with _ | ⟨h', w'⟩
      · rw [galList_nil, e_mul_poly, sub_self, zero_mul]; exact Submodule.zero_mem _
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp at hn; omega⟩
        exact mul_mem_stepFilt (ih _ (by simp at hn ⊢; omega)) (t_mem_stepFilt _ _ le_rfl)
    · exact stepFilt_mono (by omega)
        (mul_mem_stepFilt (galList_mem_stepFilt _ w) (poly_mul_t_sub_mem f _ _))

section Choice

variable (P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜))

/-- The span of `r g E * segGallery P C E * poly f` over the pairs with at most `m` steps. -/
noncomputable def segSpanBottom (m : ℕ) : Submodule k (GalleryAlgebra k Γ ν) :=
  Submodule.span k {x | ∃ (C E : FullChamber Γ ν) (g : ColPerm ν) (f : PolyRing ν k),
    segLength P C E ≤ m ∧ r g E * segGallery P C E * poly f = x}

variable {P}

theorem segSpanBottom_mono {m n : ℕ} (h : m ≤ n) :
    segSpanBottom (k := k) P m ≤ segSpanBottom P n :=
  Submodule.span_mono fun _ ⟨C, E, g, f, hl, hx⟩ => ⟨C, E, g, f, hl.trans h, hx⟩

theorem r_mul_mem_segSpanBottom {m : ℕ} (h : ColPerm ν) (D : FullChamber Γ ν)
    {x : GalleryAlgebra k Γ ν} (hx : x ∈ segSpanBottom P m) :
    r h D * x ∈ segSpanBottom P m := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨C, E, g, f, hl, rfl⟩ := hx
    rw [← mul_assoc, ← mul_assoc, r_mul_r_eq]
    split_ifs
    · exact Submodule.subset_span ⟨C, E, h * g, f, hl, rfl⟩
    · rw [zero_mul, zero_mul]; exact Submodule.zero_mem _
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

variable (hP : ∀ C E, IsChamberSegment C E (P C E))
include hP

/-- Every combination of `poly f * r g E * segGallery P C E` with at most `m` steps is a
combination of `r g E * segGallery P C E * poly f` with at most `m` steps. -/
theorem segSpan_le_segSpanBottom (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (m : ℕ) :
    segSpan (segGallery (k := k) P) (segLength P) m ≤ segSpanBottom P m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rw [segSpan, Submodule.span_le]
  rintro _ ⟨f, g, C, E, hl, rfl⟩
  -- move the polynomial below the relabelling
  have hf : f = MvPolynomial.rename g.1 (MvPolynomial.rename (g⁻¹).1 f) := by
    rw [MvPolynomial.rename_rename, Subgroup.coe_inv, ← Equiv.Perm.coe_mul, mul_inv_cancel]
    simp
  have hr : (poly f * r g E : GalleryAlgebra k Γ ν) =
      r g E * poly (MvPolynomial.rename (g⁻¹).1 f) := by
    conv_lhs => rw [hf]
    rw [r_mul_poly]
  rw [hr, mul_assoc]
  set f' := MvPolynomial.rename (g⁻¹).1 f
  have hdec : r g E * (poly f' * segGallery (k := k) P C E) =
      r g E * segGallery P C E * poly f' +
        r g E * (poly f' * segGallery P C E - segGallery P C E * poly f') := by
    noncomm_ring
  rw [hdec]
  refine Submodule.add_mem _ (Submodule.subset_span ⟨C, E, g, f', hl, rfl⟩)
    (r_mul_mem_segSpanBottom _ _ ?_)
  rcases Nat.eq_zero_or_pos (segLength P C E) with h0 | hpos
  · have hnil : word (hypAff (Γ := Γ)) (P C E).1 (P C E).2 = [] := List.eq_nil_of_length_eq_zero h0
    rw [segGallery, hnil, galList_nil, e_mul_poly, sub_self]
    exact Submodule.zero_mem _
  · have hmem := poly_mul_galList_sub_mem f' C (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2)
      (n := segLength P C E - 1) (by rw [← segLength]; omega)
    have hstep := stepFilt_le_segSpan (one_mem_segSpan (k := k) hP)
      (fun m hm C E E₁ hl => t_mul_segGallery_mem hP hD hZ m hm C E E₁ hl) _ hmem
    exact segSpanBottom_mono (by omega) (ih _ (by omega) hstep)

/-- **Webster, Theorem 2.13, spanning half, with the dots at the bottom.** Under (†) and the
absence of loops of weight `0`, for any choice of simple segments between the full chambers,
the elements `r g E * segGallery P C E * poly f` span the gallery algebra. Products are
composition, so `poly f` is at the bottom of the diagram, as in the basis of Webster,
arXiv:1209.2463v4, Theorem 2.8. -/
theorem span_segGallery_mul_poly (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    Submodule.span k {x : GalleryAlgebra k Γ ν | ∃ (C E : FullChamber Γ ν) (g : ColPerm ν)
      (f : PolyRing ν k), r g E * segGallery P C E * poly f = x} = ⊤ := by
  rw [eq_top_iff, ← span_segGallery hP hD hZ, Submodule.span_le]
  rintro _ ⟨f, g, C, E, rfl⟩
  have hgen := segSpan_le_segSpanBottom hP hD hZ (segLength P C E)
    (gen_mem_segSpan (seg := segGallery (k := k) P) (len := segLength P) f g le_rfl)
  refine Submodule.span_mono ?_ hgen
  rintro _ ⟨C', E', g', f', -, hx⟩
  exact ⟨C', E', g', f', hx⟩

/-- **Webster, Theorem 2.13, spanning half, with the dots at the bottom**, monomial form: the
elements `r g E * segGallery P C E * poly (monomial m 1)` span the gallery algebra. -/
theorem span_segGallery_mul_monomial (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) :
    Submodule.span k {x : GalleryAlgebra k Γ ν | ∃ (C E : FullChamber Γ ν) (g : ColPerm ν)
      (m : Strand ν →₀ ℕ), r g E * segGallery P C E * poly (MvPolynomial.monomial m 1) = x} =
      ⊤ := by
  rw [eq_top_iff, ← span_segGallery_mul_poly hP hD hZ, Submodule.span_le]
  rintro _ ⟨C, E, g, f, rfl⟩
  rw [f.as_sum, ← polyHom_apply, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [show MvPolynomial.monomial m (f.coeff m) = f.coeff m • MvPolynomial.monomial m 1 by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    map_smul, mul_smul_comm, polyHom_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨C, E, g, m, rfl⟩)

end Choice

end GalleryAlgebra

end Categorification.WeightedKLR
