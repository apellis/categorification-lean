/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Gallery
import Categorification.WeightedKLR.GalleryRep

/-!
# Central symmetric polynomials in the dots

The centrality input of roadmap A0 for Webster, *Weighted Khovanov–Lauda–Rouquier
algebras*, arXiv:1209.2463v4, Theorem 2.19. In the strand labelling of the gallery
algebra, a polynomial symmetric separately in each colour is fixed by every
`ColPerm`. The dot relations of Definition 2.4 imply that it commutes with every
generator, including ghost crossings and crossings at vertices with loops.

This is a supporting statement for the finite-dimensionality argument, not an
absolute-irreducibility statement. Neither the standing hypothesis nor (†) is
needed for centrality.
-/

noncomputable section

namespace Categorification.WeightedKLR

open MvPolynomial Equiv

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

omit [IsStrictOrderedRing 𝕜] in
private theorem stepFactor_eq_zero_of_invariant {f : PolyRing ν k}
    (hf : ∀ g : ColPerm ν, rename g.1 f = f) (C : FullChamber Γ ν) (d : Diag ν) :
    stepFactor Γ (d.left C) (d.right C) f = 0 := by
  have hs : rename (swap (d.left C) (d.right C)) f = f := by
    rw [Diag.swap_left_right]
    exact hf d.refl
  unfold stepFactor
  split
  · exact ddiff_eq_zero_of_rename_eq (d.left_ne_right C) hs
  · rw [hs, sub_self, mul_zero]

/-- The dot relations of Webster arXiv:1209.2463v4, Definition 2.4: a polynomial
fixed by all colour-preserving permutations commutes with each gallery step. -/
theorem t_mul_poly_of_invariant {f : PolyRing ν k}
    (hf : ∀ g : ColPerm ν, rename g.1 f = f) (C C' : FullChamber Γ ν) :
    (t C C' * poly f : GalleryAlgebra k Γ ν) = poly f * t C C' := by
  classical
  by_cases h : ∃ h : Hyp Γ ν, C.Adjacent C' h
  · obtain ⟨h, hh⟩ := h
    cases h with
    | inl w => exact t_mul_poly_inl hh f
    | inr d =>
      rw [t_mul_poly_inr hh, stepFactor_eq_zero_of_invariant hf]
      have hz : (poly (0 : PolyRing ν k) : GalleryAlgebra k Γ ν) = 0 :=
        (polyHom k Γ ν).map_zero
      rw [hz, zero_mul, add_zero]
  · rw [t_eq_zero (not_exists.1 h), zero_mul, mul_zero]

/-- The dot relations of Webster arXiv:1209.2463v4, Definition 2.4: symmetric
polynomials in the dots of each colour are central in the gallery algebra.
This requires neither the standing hypothesis, (†), nor loop-freeness. -/
theorem poly_mem_center {f : PolyRing ν k}
    (hf : ∀ g : ColPerm ν, rename g.1 f = f) :
    poly f ∈ Subalgebra.center k (GalleryAlgebra k Γ ν) := by
  rw [Subalgebra.mem_center_iff]
  intro x
  obtain ⟨a, rfl⟩ := mk_surjective x
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes]
    exact Algebra.commutes c (poly f : GalleryAlgebra k Γ ν)
  | grade1 g =>
    cases g with
    | idem C => exact (e_mul_poly C f)
    | poly p =>
      show poly p * poly f = poly f * poly p
      rw [poly_mul_poly, poly_mul_poly, mul_comm]
    | step C C' => exact t_mul_poly_of_invariant hf C C'
    | relabel g C =>
      show r g C * poly f = poly f * r g C
      rw [r_mul_poly, hf]
  | add a b ha hb =>
    rw [map_add, add_mul, mul_add, ha, hb]
  | mul a b ha hb =>
    rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]

end GalleryAlgebra

end Categorification.WeightedKLR
