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

variable {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))

/-- **Balancedness of the middle parabolic, summed over the chambers.** Let `Z` be the
juxtaposition `(x_a x_b)(x_c x_d)` in the layout `a b c d` and `Z'` the juxtaposition
`(x_a x_c)(x_b x_d)` in the layout `a c b d`, cut down by the idempotents `E`, `E'` of the
parabolics `(a b)(c d)` and `(a c)(b d)`. Then `ψ_c E Z E - E' Z' E' ψ_c`, multiplied by `ι(x)`
on the left and `ι(y)` on the right and cut down to rank-ordered `L` and `R`, lies in the step of
the shuffle types strictly below `c` (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem typeShuffle_balance_mem_mackeyFilt {L R : FullChamber Γ (a + b + (c + d))}
    (hL' : L.IsRankOrdered) (hR : R.IsRankOrdered)
    (x : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d))
    (xa : GalleryAlgebra k Γ a) (xb : GalleryAlgebra k Γ b) (xc : GalleryAlgebra k Γ c)
    (xd : GalleryAlgebra k Γ d) :
    e L * inductionVal k (layout_eq a b c d) x *
        (typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d) *
            ((∑ q ∈ rankQuads Γ a b c d, e (fourChamber a b c d q)) *
              (galleryTensorHom k Γ (a + b) (c + d)
                ((galleryTensorHom k Γ a b (xa ⊗ₜ xb)).1 ⊗ₜ
                  (galleryTensorHom k Γ c d (xc ⊗ₜ xd)).1)).1 *
              ∑ q ∈ rankQuads Γ a b c d, e (fourChamber a b c d q)) -
          ((∑ q ∈ rankQuads Γ a b c d, e (fourChamberSwap a b c d q)) *
              castGallery k Γ (layout_eq a b c d) (galleryTensorHom k Γ (a + c) (b + d)
                ((galleryTensorHom k Γ a c (xa ⊗ₜ xc)).1 ⊗ₜ
                  (galleryTensorHom k Γ b d (xb ⊗ₜ xd)).1)).1 *
              ∑ q ∈ rankQuads Γ a b c d, e (fourChamberSwap a b c d q)) *
            typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d)) *
        inductionVal k rfl y * e R ∈
      mackeyFilt k hP hD hZ hΓ hW hL (a + b) (a + c) L R (Set.Iio ⇑c) := by
  set ψ := typeShuffle k hD hZ (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d)
  set Z := (galleryTensorHom k Γ (a + b) (c + d)
    ((galleryTensorHom k Γ a b (xa ⊗ₜ xb)).1 ⊗ₜ (galleryTensorHom k Γ c d (xc ⊗ₜ xd)).1)).1
  set Z' := castGallery k Γ (layout_eq a b c d) (galleryTensorHom k Γ (a + c) (b + d)
    ((galleryTensorHom k Γ a c (xa ⊗ₜ xc)).1 ⊗ₜ (galleryTensorHom k Γ b d (xb ⊗ₜ xd)).1)).1
  have hsum : ψ * ((∑ q ∈ rankQuads Γ a b c d, e (fourChamber a b c d q)) * Z *
        ∑ q ∈ rankQuads Γ a b c d, e (fourChamber a b c d q)) -
      ((∑ q ∈ rankQuads Γ a b c d, e (fourChamberSwap a b c d q)) * Z' *
        ∑ q ∈ rankQuads Γ a b c d, e (fourChamberSwap a b c d q)) * ψ =
      ∑ q ∈ rankQuads Γ a b c d, ∑ q' ∈ rankQuads Γ a b c d,
        (fourShuffle k hD hZ (middleLeft a b c d) (fourChamber a b c d q) *
            (e (fourChamber a b c d q) * Z * e (fourChamber a b c d q')) -
          (e (fourChamberSwap a b c d q) * Z' * e (fourChamberSwap a b c d q')) *
            fourShuffle k hD hZ (middleLeft a b c d) (fourChamber a b c d q')) := by
    have h1 : ∀ q ∈ rankQuads Γ a b c d, ∀ q' ∈ rankQuads Γ a b c d,
        fourShuffle k hD hZ (middleLeft a b c d) (fourChamber a b c d q) *
            (e (fourChamber a b c d q) * Z * e (fourChamber a b c d q')) -
          (e (fourChamberSwap a b c d q) * Z' * e (fourChamberSwap a b c d q')) *
            fourShuffle k hD hZ (middleLeft a b c d) (fourChamber a b c d q') =
        ψ * e (fourChamber a b c d q) * Z * e (fourChamber a b c d q') -
          e (fourChamberSwap a b c d q) * Z' * e (fourChamberSwap a b c d q') * ψ :=
      fun q hq q' hq' => by
        rw [← typeShuffle_mul_e_fourChamber hD hZ (isRankOrdered_of_mem_rankQuads hq),
          ← e_fourChamberSwap_mul_typeShuffle hD hZ (isRankOrdered_of_mem_rankQuads hq')]
        have he : ∀ (w : GalleryAlgebra k Γ (a + b + (c + d))) E, w * e E * e E = w * e E :=
          fun w E => by rw [mul_assoc, e_mul_e_self]
        simp only [← mul_assoc, he]
        rfl
    rw [Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun q' hq' => h1 q hq q' hq']
    simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    congr 1 <;> exact Finset.sum_comm
  rw [hsum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Submodule.sum_mem _ fun q hq => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Submodule.sum_mem _ fun q' hq' => ?_
  obtain ⟨A, B, C, D⟩ := q
  obtain ⟨A', B', C', D'⟩ := q'
  obtain ⟨hA, hB, hC, hD₀⟩ :=
    (isRankOrdered_fourChamber_iff _).1 (isRankOrdered_of_mem_rankQuads hq)
  obtain ⟨hA', hB', hC', hD'⟩ :=
    (isRankOrdered_fourChamber_iff _).1 (isRankOrdered_of_mem_rankQuads hq')
  exact inductionMap_mul_mul_mem_mackeyFilt hP hD hZ hΓ hW hL (layout_eq a b c d) rfl
    (isRankOrdered_of_mem_rankQuads hq') hR
    ((isRankOrdered_fourChamberSwap_iff _).2 (isRankOrdered_of_mem_rankQuads hq)) hL'
    (isLowerSet_Iio _) x y
    (fourShuffle_mul_sub_mul_fourShuffle_mem_mackeyFilt_middleSwap hΓ hP hD hZ hW hL hA hB hC
      hD₀ hA' hB' hC' hD' xa xb xc xd)

end Juxtapose

end Categorification.WeightedKLR
