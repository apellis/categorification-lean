/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockDecomp
import Categorification.WeightedKLR.Mackey.TypeFiltration

/-!
# Balancedness of the map of the middle parabolic

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19. For the layouts `a b c d` and `a c b d` and the shuffle type `c`,
the map `x ⊗ y ↦ e D ι(x) ψ_c ι(y) e C` is balanced over `W_a ⊗ W_b ⊗ W_c ⊗ W_d` up to lower
shuffle types: moving `(x_a x_b)(x_c x_d)` from the left of `y` to the right of `x`, where it
becomes `(x_a x_c)(x_b x_d)`, changes the value by an element of the step of the shuffle types
strictly below `c`.

## Main results

* `Juxtapose.galleryTensorHom_splitIdem_splitIdem`: the idempotent of the parabolic
  `(a b)(c d)` is the sum of the idempotents of the chambers `(A B)(C D)`.
* `Juxtapose.castGallery_galleryTensorHom_splitIdem_splitIdem`: the idempotent of the parabolic
  `(a c)(b d)` is the sum of the idempotents of the chambers `(A C)(B D)`.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra IsIdempotentElem

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace Juxtapose

variable {a b c d : I →₀ ℕ}

variable (Γ a b c d) in
/-- The quadruples of chambers `(A, B, C, D)` with `(A B)(C D)` rank-ordered. -/
noncomputable abbrev rankQuads :
    Finset (FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d) :=
  Finset.univ.filter fun q => (fourChamber a b c d q).IsRankOrdered

theorem rankQuads_eq_product :
    rankQuads Γ a b c d = Finset.univ.filter FullChamber.IsRankOrdered ×ˢ
      Finset.univ.filter FullChamber.IsRankOrdered ×ˢ
        Finset.univ.filter FullChamber.IsRankOrdered ×ˢ
          Finset.univ.filter FullChamber.IsRankOrdered := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    isRankOrdered_fourChamber_iff]

theorem isRankOrdered_of_mem_rankQuads
    {q : FullChamber Γ a × FullChamber Γ b × FullChamber Γ c × FullChamber Γ d}
    (hq : q ∈ rankQuads Γ a b c d) : (fourChamber a b c d q).IsRankOrdered :=
  (Finset.mem_filter.1 hq).2

/-- The idempotent of the parabolic `(a b)(c d)` is the sum of the idempotents of the
rank-ordered chambers `(A B)(C D)`. -/
theorem galleryTensorHom_splitIdem_splitIdem :
    (galleryTensorHom k Γ (a + b) (c + d) (splitIdem k Γ a b ⊗ₜ splitIdem k Γ c d)).1 =
      ∑ q ∈ rankQuads Γ a b c d, e (fourChamber a b c d q) := by
  rw [rankQuads_eq_product]
  simp only [splitIdem, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum, corner_val_sum, galleryTensorHom_e_tmul_e,
    Finset.sum_product]
  rfl

/-- The idempotent of the parabolic `(a c)(b d)`, read in `(a + b) + (c + d)`, is the sum of the
idempotents of the rank-ordered chambers `(A C)(B D)`. -/
theorem castGallery_galleryTensorHom_splitIdem_splitIdem :
    castGallery k Γ (layout_eq a b c d)
        (galleryTensorHom k Γ (a + c) (b + d) (splitIdem k Γ a c ⊗ₜ splitIdem k Γ b d)).1 =
      ∑ q ∈ rankQuads Γ a b c d, e (fourChamberSwap a b c d q) := by
  have hcast : ∀ {ν μ : I →₀ ℕ} (h : ν = μ) (C : FullChamber Γ ν),
      castGallery k Γ h (e C) = e (castChamber h C) := fun h C => by
    subst h
    rfl
  rw [rankQuads_eq_product]
  simp only [splitIdem, TensorProduct.sum_tmul]
  simp only [TensorProduct.tmul_sum, map_sum, corner_val_sum, galleryTensorHom_e_tmul_e,
    Finset.sum_product, hcast]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_comm]
  rfl

end Juxtapose

end Categorification.WeightedKLR
