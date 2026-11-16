/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.MiddleCorner

/-!
# The leading terms of the juxtaposed corner of the middle parabolic

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (injectivity half, after Khovanov–Lauda, arXiv:0803.4121v2,
Proposition 2.18). The descended map `middleTensorMap` sends the spanning vector
`(c_{u₁} ⊗ c_{u₂}) ⊗ (b₁ ⊗ b₂)` of the juxtaposed corner to a corner basis vector of Webster,
Theorem 2.8, modulo shorter corner basis vectors.

## Main definitions

* `GalleryAlgebra.IsRelGal x C E g`: `x = r g E * galList C w` for a minimal gallery `w` from `C`
  to `E`.

## Main results

* `GalleryAlgebra.IsRelGal.mul`: composition of relabelled minimal galleries through a chamber in
  between.
* `Juxtapose.IsRelGal.galleryTensorHom`: juxtaposition of relabelled minimal galleries.
-/

namespace Module.Basis

variable {R G ι κ : Type*} [CommRing R] [AddCommGroup G] [Module R G] {N : Submodule R G}

/-- **Triangular families stay independent modulo part of the basis.** Let `b` be a basis of
`N ≤ G`, `ℓ` a length on its index set and `y j ∈ G` congruent to `b (e j)` modulo basis vectors
of smaller length, for an injective leading index `e`. If a combination of the `y j` lies in the
span of the basis vectors `b i` with `p i`, and no leading index satisfies `p`, then all its
coefficients vanish. -/
theorem eq_zero_of_triangular_sum_mem (b : Module.Basis ι R N) (ℓ : ι → ℕ) {e : κ → ι}
    (he : Function.Injective e) (y : κ → G)
    (hy : ∀ j, y j - (b (e j) : G) ∈
      Submodule.span R (Set.range fun i : {i // ℓ i < ℓ (e j)} => (b i : G)))
    (p : ι → Prop) (hp : ∀ j, ¬ p (e j)) (s : Finset κ) (g : κ → R)
    (hg : ∑ j ∈ s, g j • y j ∈ Submodule.span R (Set.range fun i : {i // p i} => (b i : G))) :
    ∀ j ∈ s, g j = 0 := by
  classical
  have hspan : ∀ q : ι → Prop,
      Submodule.span R (Set.range fun i : {i // q i} => (b i : G)) ≤ N :=
    fun q => Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact (b i).2)
  have hyN : ∀ j, y j ∈ N := fun j => by
    have := N.add_mem (hspan _ (hy j)) (b (e j)).2
    rwa [sub_add_cancel] at this
  set x : κ → N := fun j => ⟨y j, hyN j⟩
  have hx : ∀ j, x j - b (e j) ∈ Submodule.span R (b '' {i | ℓ i < ℓ (e j)}) := fun j =>
    mem_span_image_of_coe_mem b (fun i => ℓ i < ℓ (e j)) (y := x j - b (e j)) (hy j)
  have hsum : ∑ j ∈ s, g j • x j ∈ Submodule.span R (b '' {i | p i}) := by
    refine mem_span_image_of_coe_mem b p ?_
    have : ((∑ j ∈ s, g j • x j : N) : G) = ∑ j ∈ s, g j • y j := by
      simp only [Submodule.coe_sum, Submodule.coe_smul, x]
    rw [this]
    exact hg
  intro j hj
  by_contra hne
  obtain ⟨j₀, hj₀, hmax⟩ : ∃ j ∈ s.filter (fun j => g j ≠ 0),
      ∀ j' ∈ s.filter (fun j => g j ≠ 0), ℓ (e j') ≤ ℓ (e j) :=
    Finset.exists_max_image _ (fun j => ℓ (e j)) ⟨j, Finset.mem_filter.2 ⟨hj, hne⟩⟩
  obtain ⟨hj₀s, hj₀g⟩ := Finset.mem_filter.1 hj₀
  have hterm : ∀ j' ∈ s, g j' * b.repr (x j') (e j₀) = if j' = j₀ then g j₀ else 0 := by
    intro j' hj'
    by_cases hg' : g j' = 0
    · rw [hg', zero_mul]
      split_ifs with h
      · rw [← h, hg']
      · rfl
    have hle : ℓ (e j') ≤ ℓ (e j₀) := hmax j' (Finset.mem_filter.2 ⟨hj', hg'⟩)
    have hz : b.repr (x j' - b (e j')) (e j₀) = 0 := by
      rw [← Finsupp.notMem_support_iff]
      intro hmem
      have := b.mem_span_image.1 (hx j') hmem
      exact absurd hle (not_le.2 this)
    rw [map_sub, Finsupp.sub_apply, b.repr_self, sub_eq_zero] at hz
    rw [hz, Finsupp.single_apply, he.eq_iff]
    split_ifs with h
    · rw [h, mul_one]
    · exact mul_zero _
  have h0 : b.repr (∑ j ∈ s, g j • x j) (e j₀) = 0 := by
    rw [← Finsupp.notMem_support_iff]
    exact fun hmem => hp j₀ (b.mem_span_image.1 hsum hmem)
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul] at h0
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j₀] at h0
  simp only [hj₀s, ↓reduceIte] at h0
  exact hj₀g h0

end Module.Basis

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose MulOpposite

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GalleryAlgebra

variable {ν : I →₀ ℕ}

variable (k) in
/-- `x` is a minimal gallery from `C` to `E` followed by the relabelling `r g E`. -/
def IsRelGal (x : GalleryAlgebra k Γ ν) (C E : FullChamber Γ ν) (g : ColPerm ν) : Prop :=
  ∃ w, GoodWord C.1 w ∧ C.flips w = E ∧ x = r g E * galList k C w

/-- A relabelled minimal gallery followed by another one, from a chamber that agrees with the
starting chamber wherever the starting and the final chambers agree, is a relabelled minimal
gallery. -/
theorem IsRelGal.mul {x y : GalleryAlgebra k Γ ν} {C E F : FullChamber Γ ν} {g h : ColPerm ν}
    (hy : IsRelGal k y C E g) (hx : IsRelGal k x (g • E) F h)
    (hb : ∀ s, C.1 s = (g⁻¹ • F).1 s → E.1 s = C.1 s) :
    IsRelGal k (x * y) C (g⁻¹ • F) (h * g) := by
  obtain ⟨w₁, hw₁, hf₁, rfl⟩ := hy
  obtain ⟨w₂, hw₂, hf₂, rfl⟩ := hx
  obtain ⟨g₁, g₂, g₃⟩ := goodWord_smul (k := k) g⁻¹ hw₂
  rw [inv_smul_smul] at g₁ g₂ g₃
  rw [hf₂] at g₂ g₃
  have hgal : galList k (g • E) w₂ * r g E =
      r g (g⁻¹ • F) * galList k E (w₂.map (Hyp.comap g⁻¹⁻¹)) := by
    have h1 : r g (g⁻¹ • F) * (galList k E (w₂.map (Hyp.comap g⁻¹⁻¹)) * r g⁻¹ (g • E)) =
        galList k (g • E) w₂ := by
      rw [g₃, ← mul_assoc, r_mul_r, mul_inv_cancel, r_one, ← hf₂, e_mul_galList]
    rw [← h1, mul_assoc, mul_assoc, r_mul_r, inv_mul_cancel, r_one, galList_mul_e]
  refine ⟨w₁ ++ w₂.map (Hyp.comap g⁻¹⁻¹), ?_, ?_, ?_⟩
  · refine GoodWord.append_of_between hw₁ (hf₁ ▸ g₁) ?_
    rw [hf₁, g₂]
    exact hb
  · rw [flips_append, hf₁, g₂]
  · have hF : r (h * g) (g⁻¹ • F) = r h F * r g (g⁻¹ • F) := by
      have h1 := r_mul_r (k := k) h g (g⁻¹ • F)
      rw [smul_inv_smul] at h1
      exact h1.symm
    rw [galList_append, hf₁, hF, mul_assoc, ← mul_assoc (galList k (g • E) w₂), hgal]
    simp only [mul_assoc]

/-- A relabelled minimal gallery, transported along `ν = μ`. -/
theorem IsRelGal.castGallery {μ : I →₀ ℕ} (hνμ : ν = μ) {x : GalleryAlgebra k Γ ν}
    {C E : FullChamber Γ ν} {g : ColPerm ν} (hx : IsRelGal k x C E g) :
    IsRelGal k (castGallery k Γ hνμ x) (castChamber hνμ C) (castChamber hνμ E) (hνμ ▸ g) := by
  subst hνμ
  exact hx

omit [DecidableEq I] in
theorem cast_smul_castChamber {μ : I →₀ ℕ} (hνμ : ν = μ) (g : ColPerm ν)
    (E : FullChamber Γ ν) : (hνμ ▸ g) • castChamber hνμ E = castChamber hνμ (g • E) := by
  subst hνμ
  rfl

/-- The coset element `c_u` is a relabelled minimal gallery. -/
theorem isRelGal_cosetElt (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (ν' : I →₀ ℕ) (u : ColPerm ν)
    (D : FullChamber Γ ν) :
    IsRelGal k (cosetElt k hD hZ ν' u D)
      (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D)) (u⁻¹ • D) u :=
  ⟨_, (goodWord_cosetWord hD hZ ν' _).1, (goodWord_cosetWord hD hZ ν' _).2, rfl⟩

/-- A relabelled minimal gallery from `shuffleTop X (u⁻¹ • D)` to `u⁻¹ • D` by `u` is the coset
element `c_u`. -/
theorem IsRelGal.eq_cosetElt (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (ν' : I →₀ ℕ) {u : ColPerm ν}
    {D : FullChamber Γ ν} {x : GalleryAlgebra k Γ ν}
    (hx : IsRelGal k x (shuffleTop (fun t => decide (t.IsLeft ν')) (u⁻¹ • D)) (u⁻¹ • D) u) :
    x = cosetElt k hD hZ ν' u D := by
  obtain ⟨w, hw, hfw, rfl⟩ := hx
  rw [cosetElt, galList_eq_cosetWord hD hZ ν' _ hw hfw]

/-- The four-block shuffle element is a relabelled minimal gallery. -/
theorem isRelGal_fourShuffle (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (Z : Strand ν → Bool)
    (B : FullChamber Γ ν) {ρ : ColPerm ν} (hρ : (ρ • shuffleTop Z B).IsRankOrdered) :
    IsRelGal k (fourShuffle k hD hZ Z B) B (shuffleTop Z B) ρ := by
  obtain ⟨w, hw, hfw⟩ := exists_goodWord hD hZ B (shuffleTop Z B)
  exact ⟨w, hw, hfw, fourShuffle_eq hD hZ Z B hρ hw hfw⟩

end GalleryAlgebra

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ}

/-- The juxtaposition of relabelled minimal galleries is a relabelled minimal gallery. -/
theorem IsRelGal.galleryTensorHom {x' : GalleryAlgebra k Γ ν'} {x'' : GalleryAlgebra k Γ ν''}
    {C' E' : FullChamber Γ ν'} {C'' E'' : FullChamber Γ ν''} {g' : ColPerm ν'}
    {g'' : ColPerm ν''} (hx' : IsRelGal k x' C' E' g') (hx'' : IsRelGal k x'' C'' E'' g'') :
    IsRelGal k (galleryTensorHom k Γ ν' ν'' (x' ⊗ₜ x'')).1 (chamber C' C'') (chamber E' E'')
      (colPermProd ν' ν'' (g', g'')) := by
  obtain ⟨w₁, hw₁, hf₁, rfl⟩ := hx'
  obtain ⟨w₂, hw₂, hf₂, rfl⟩ := hx''
  obtain ⟨hW, hfW, hgW⟩ := galList_map_append_map (k := k) hw₁ hw₂
  refine ⟨_, hW, by rw [hfW, hf₁, hf₂], ?_⟩
  rw [← Algebra.TensorProduct.tmul_mul_tmul, galleryTensorHom_mul_val, galleryTensorHom_r_tmul_r,
    hgW]

omit [DecidableEq I] in
/-- The restriction of a juxtaposition to the left strands. -/
theorem restrict_leftEmb_chamber (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    (leftEmb ν' ν'').restrict (chamber C' C'') = C' :=
  Subtype.ext (funext fun h => by rw [StrandEmbedding.restrict_apply, chamber_left])

omit [DecidableEq I] in
/-- The restriction of a juxtaposition to the right strands. -/
theorem restrict_rightEmb_chamber (C' : FullChamber Γ ν') (C'' : FullChamber Γ ν'') :
    (rightEmb ν' ν'').restrict (chamber C' C'') = C'' :=
  Subtype.ext (funext fun h => by rw [StrandEmbedding.restrict_apply, chamber_right])

omit [DecidableEq I] in
/-- `shuffleTop` commutes with transport along `ν₀ = ν`. -/
theorem shuffleTop_castChamber {ν₀ ν : I →₀ ℕ} (h : ν₀ = ν) (W : Strand ν → Bool)
    (C : FullChamber Γ ν₀) :
    shuffleTop W (castChamber h C) = castChamber h (shuffleTop (fun s => W (castStrand h s)) C) := by
  subst h
  rfl

omit [DecidableEq I] in
/-- `shuffleTop Y` of a juxtaposition only sees the two factors on the hyperplanes that `Y` does
not separate. -/
theorem shuffleTop_chamber_congr (Y : Strand (ν' + ν'') → Bool) {C' D' : FullChamber Γ ν'}
    {C'' D'' : FullChamber Γ ν''}
    (h' : ∀ y : Hyp Γ ν', Y (inlStrand ν' ν'' y.lo) = Y (inlStrand ν' ν'' y.hi) →
      C'.1 y = D'.1 y)
    (h'' : ∀ y : Hyp Γ ν'', Y (inrStrand ν' ν'' y.lo) = Y (inrStrand ν' ν'' y.hi) →
      C''.1 y = D''.1 y) :
    shuffleTop Y (chamber C' C'') = shuffleTop Y (chamber D' D'') := by
  refine Subtype.ext (funext fun x => ?_)
  rw [shuffleTop_apply, shuffleTop_apply]
  split_ifs with hx
  · by_cases hl : x ∈ Set.range ((leftEmb ν' ν'').hyp (Γ := Γ))
    · obtain ⟨y, rfl⟩ := hl
      rw [StrandEmbedding.lo_hyp, StrandEmbedding.hi_hyp] at hx
      rw [chamber_left, chamber_left]
      exact h' y hx
    by_cases hr : x ∈ Set.range ((rightEmb ν' ν'').hyp (Γ := Γ))
    · obtain ⟨y, rfl⟩ := hr
      rw [StrandEmbedding.lo_hyp, StrandEmbedding.hi_hyp] at hx
      rw [chamber_right, chamber_right]
      exact h'' y hx
    rw [chamber_cross _ _ hl hr, chamber_cross _ _ hl hr]
  · rfl

end Juxtapose

namespace Juxtapose

variable {a b c d : I →₀ ℕ}

theorem perm_inv_apply_self {α : Type*} (σ : Equiv.Perm α) (x : α) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

omit [DecidableEq I] in
/-- Read through the middle swap, the strands of `a + b` are those of `a` in `a + c`. -/
theorem isLeft_inv_middleSwap_inl (t : Strand (a + c)) :
    decide (((middleSwap a b c d).1⁻¹ (castStrand (layout_eq a b c d)
      (inlStrand (a + c) (b + d) t))).IsLeft (a + b)) = decide (t.IsLeft a) := by
  by_cases ht : t.IsLeft a
  · obtain ⟨s, rfl⟩ := exists_inlStrand_eq (ν'' := c) ht
    rw [← middleSwap_inl_inl, perm_inv_apply_self]
    simp [isLeft_inlStrand]
  · obtain ⟨s, rfl⟩ := exists_inrStrand_eq (ν'' := c) ht
    rw [← middleSwap_inr_inl, perm_inv_apply_self]
    simp [not_isLeft_inrStrand]

omit [DecidableEq I] in
/-- Read through the middle swap, the strands of `a + b` are those of `b` in `b + d`. -/
theorem isLeft_inv_middleSwap_inr (t : Strand (b + d)) :
    decide (((middleSwap a b c d).1⁻¹ (castStrand (layout_eq a b c d)
      (inrStrand (a + c) (b + d) t))).IsLeft (a + b)) = decide (t.IsLeft b) := by
  by_cases ht : t.IsLeft b
  · obtain ⟨s, rfl⟩ := exists_inlStrand_eq (ν'' := d) ht
    rw [← middleSwap_inl_inr, perm_inv_apply_self]
    simp [isLeft_inlStrand]
  · obtain ⟨s, rfl⟩ := exists_inrStrand_eq (ν'' := d) ht
    rw [← middleSwap_inr_inr, perm_inv_apply_self]
    simp [not_isLeft_inrStrand]

omit [DecidableEq I] in
/-- **The four-block chamber of a pair of coset representatives.** If `A C` and `B D` are
obtained from `E₁` and `E₂` by moving the strands of `a` (resp. `b`) to the left, then moving the
strands of `a + b` of `ρ⁻¹ • (E₁ E₂)` to the left gives `(A B)(C D)`, `ρ` the middle swap. -/
theorem shuffleTop_inv_middleSwap_smul {E₁ : FullChamber Γ (a + c)}
    {E₂ : FullChamber Γ (b + d)} {A : FullChamber Γ a} {B : FullChamber Γ b}
    {C : FullChamber Γ c} {D : FullChamber Γ d}
    (h₁ : chamber A C = shuffleTop (fun t => decide (t.IsLeft a)) E₁)
    (h₂ : chamber B D = shuffleTop (fun t => decide (t.IsLeft b)) E₂)
    (hq : IsFourBlock (fun t => decide (t.IsLeft (a + b))) (middleLeft a b c d)
      (chamber (chamber A B) (chamber C D))) :
    shuffleTop (fun t => decide (t.IsLeft (a + b)))
        ((middleSwap a b c d)⁻¹ • castChamber (layout_eq a b c d) (chamber E₁ E₂)) =
      chamber (chamber A B) (chamber C D) := by
  set ρ := middleSwap a b c d
  set X : Strand (a + b + (c + d)) → Bool := fun t => decide (t.IsLeft (a + b))
  set W : Strand (a + b + (c + d)) → Bool := fun t => X (ρ.1⁻¹ t)
  set Gq := chamber (chamber A B) (chamber C D)
  have hX : (fun t => W ((ρ⁻¹).1⁻¹ t)) = X := funext fun t => by
    simp only [W, InvMemClass.coe_inv, inv_inv, perm_inv_apply_self]
  have h0 := shuffleTop_smul W (castChamber (layout_eq a b c d) (chamber E₁ E₂)) ρ⁻¹
  rw [hX] at h0
  rw [← h0]
  suffices hs : shuffleTop W (castChamber (layout_eq a b c d) (chamber E₁ E₂)) = ρ • Gq by
    rw [hs, inv_smul_smul]
  have hρ : ρ • Gq = shuffleTop W (castChamber (layout_eq a b c d)
      (chamber (chamber A C) (chamber B D))) := by
    rw [← middleSwap_smul_shuffleTop, ← shuffleTop_smul]
    exact congrArg (ρ • ·) hq.2.symm
  rw [hρ, shuffleTop_castChamber, shuffleTop_castChamber, h₁, h₂]
  congr 1
  refine shuffleTop_chamber_congr _ (fun y hy => ?_) (fun y hy => ?_)
  · have hy' := ((isLeft_inv_middleSwap_inl (b := b) (d := d) y.lo).symm.trans hy).trans
      (isLeft_inv_middleSwap_inl (b := b) (d := d) y.hi)
    rw [shuffleTop_apply]
    split_ifs
    rfl
  · have hy' := ((isLeft_inv_middleSwap_inr (a := a) (c := c) y.lo).symm.trans hy).trans
      (isLeft_inv_middleSwap_inr (a := a) (c := c) y.hi)
    rw [shuffleTop_apply]
    split_ifs
    rfl

variable {L' : FullChamber Γ (a + c)} {L'' : FullChamber Γ (b + d)}

/-- The relabelling `U ρ` of `(a + b) + (c + d)` attached to representatives `u₁`, `u₂` for `L'`,
`L''`: `U` is the juxtaposition of `u₁` and `u₂`, read in `(a + b) + (c + d)`, and `ρ` the middle
swap. -/
noncomputable def middleCoset (u₁ : ParabolicRep a L') (u₂ : ParabolicRep b L'') :
    ColPerm (a + b + (c + d)) :=
  (layout_eq a b c d ▸ colPermProd (a + c) (b + d) (u₁.1, u₂.1)) * middleSwap a b c d

omit [DecidableEq I] in
theorem middleCoset_inv_smul (u₁ : ParabolicRep a L') (u₂ : ParabolicRep b L'') :
    (middleCoset u₁ u₂)⁻¹ • castChamber (layout_eq a b c d) (chamber L' L'') =
      (middleSwap a b c d)⁻¹ • castChamber (layout_eq a b c d)
        (chamber (u₁.1⁻¹ • L') (u₂.1⁻¹ • L'')) := by
  rw [middleCoset, mul_inv_rev, mul_smul]
  congr 1
  rw [inv_smul_eq_iff, cast_smul_castChamber, colPermProd_smul_chamber, smul_inv_smul,
    smul_inv_smul]

omit [DecidableEq I] in
/-- The four-block chamber `(A B)(C D)` of the restrictions of `G_{u₁}` and `G_{u₂}`. -/
theorem shuffleTop_middleCoset_inv_smul (u₁ : ParabolicRep a L') (u₂ : ParabolicRep b L'') :
    shuffleTop (fun t => decide (t.IsLeft (a + b)))
        ((middleCoset u₁ u₂)⁻¹ • castChamber (layout_eq a b c d) (chamber L' L'')) =
      chamber (chamber (repLeft u₁) (repLeft u₂)) (chamber (repRight u₁) (repRight u₂)) := by
  rw [middleCoset_inv_smul]
  exact shuffleTop_inv_middleSwap_smul (chamber_repLeft_repRight u₁)
    (chamber_repLeft_repRight u₂)
    (isFourBlock_fourChamber (isRankOrdered_repLeft u₁) (isRankOrdered_repLeft u₂)
      (isRankOrdered_repRight u₁) (isRankOrdered_repRight u₂))

/-- **The coset elements of the middle parabolic.** The juxtaposition of `c_{u₁}` and `c_{u₂}`,
followed by the four-block shuffle element of `(A B)(C D)`, is the coset element `c_{U ρ}` of
`(a + b) + (c + d)`. -/
theorem castGallery_cosetElt_mul_fourShuffle (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (u₁ : ParabolicRep a L') (u₂ : ParabolicRep b L'') :
    castGallery k Γ (layout_eq a b c d) (galleryTensorHom k Γ (a + c) (b + d)
        (cosetElt k hD hZ a u₁.1 L' ⊗ₜ cosetElt k hD hZ b u₂.1 L'')).1 *
      fourShuffle k hD hZ (middleLeft a b c d)
        (chamber (chamber (repLeft u₁) (repLeft u₂)) (chamber (repRight u₁) (repRight u₂))) =
      cosetElt k hD hZ (a + b) (middleCoset u₁ u₂)
        (castChamber (layout_eq a b c d) (chamber L' L'')) := by
  set ρ := middleSwap a b c d
  set Gq := chamber (chamber (repLeft u₁) (repLeft u₂)) (chamber (repRight u₁) (repRight u₂))
  set F := castChamber (layout_eq a b c d) (chamber (u₁.1⁻¹ • L') (u₂.1⁻¹ • L''))
  have h₁ := isRelGal_cosetElt (k := k) hD hZ a u₁.1 L'
  have h₂ := isRelGal_cosetElt (k := k) hD hZ b u₂.1 L''
  rw [← chamber_repLeft_repRight] at h₁ h₂
  have hx := (Juxtapose.IsRelGal.galleryTensorHom h₁ h₂).castGallery (layout_eq a b c d)
  have hsw : ρ • shuffleTop (middleLeft a b c d) Gq =
      castChamber (layout_eq a b c d)
        (chamber (chamber (repLeft u₁) (repRight u₁)) (chamber (repLeft u₂) (repRight u₂))) :=
    middleSwap_smul_shuffleTop a b c d _ _ _ _
  rw [← hsw] at hx
  have hρ : (ρ • shuffleTop (middleLeft a b c d) Gq).IsRankOrdered := by
    rw [hsw, isRankOrdered_castChamber_chamber_iff, chamber_repLeft_repRight,
      chamber_repLeft_repRight]
    exact ⟨u₁.2, u₂.2⟩
  have hy := isRelGal_fourShuffle (k := k) hD hZ (middleLeft a b c d) Gq hρ
  have hsep : IsSeparated (middleLeft a b c d) (ρ⁻¹ • F) :=
    (isSeparated_castChamber_chamber (layout_eq a b c d) _ _).smul_of ρ⁻¹ fun s => by
      rw [middleLeft_eq]
      have hc := (ρ⁻¹).2 s
      change ((ρ⁻¹).1 s).1 = s.1 at hc
      have hs : ρ.1 ((ρ⁻¹).1 s) = s := ρ.1.apply_symm_apply s
      rw [hs, hc]
      rfl
  have hxy := hy.mul hx fun s hs => shuffleTop_between hsep s hs
  rw [← middleCoset_inv_smul] at hxy
  refine IsRelGal.eq_cosetElt hD hZ (a + b) ?_
  rw [shuffleTop_middleCoset_inv_smul]
  exact hxy

variable {R' : FullChamber Γ (a + b)} {R'' : FullChamber Γ (c + d)}

/-- **The image of a vector of the spanning family, in the gallery algebra.** With
`L = castChamber (chamber L' L'')` and `R = chamber R' R''`, the map
`x ⊗ y ↦ e L ι(x) ψ_c ι(y) e R` sends `(c_{u₁} ⊗ c_{u₂}) ⊗ (x₁ ⊗ x₂)` to `c_{U ρ} ι(x₁ ⊗ x₂)`,
for `x₁`, `x₂` in the corners from the four-block chamber of `u₁`, `u₂` to `R'`, `R''` (Webster,
arXiv:1209.2463v4, Theorem 2.19). -/
theorem typeInductionAux_middleCorner (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hL' : L'.IsRankOrdered) (hL'' : L''.IsRankOrdered) (hR' : R'.IsRankOrdered)
    (hR'' : R''.IsRankOrdered) (u₁ : ParabolicRep a L') (u₂ : ParabolicRep b L'')
    (x₁ : cornerSpace k (chamber (repLeft u₁) (repLeft u₂)) R')
    (x₂ : cornerSpace k (chamber (repRight u₁) (repRight u₂)) R'') :
    typeInductionAux k hD hZ (rfl : a + b + (c + d) = a + b + (c + d)) (layout_eq a b c d)
        (castChamber (layout_eq a b c d) (chamber L' L'')) (chamber R' R'') (middleLeft a b c d)
        ((cosetW k hD hZ hL' u₁ ⊗ₜ cosetW k hD hZ hL'' u₂) ⊗ₜ
          (cornerW k (isRankOrdered_botLeft u₁ u₂) hR' x₁ ⊗ₜ
            cornerW k (isRankOrdered_botRight u₁ u₂) hR'' x₂)) =
      cosetElt k hD hZ (a + b) (middleCoset u₁ u₂)
          (castChamber (layout_eq a b c d) (chamber L' L'')) *
        (galleryTensorHom k Γ (a + b) (c + d)
          ((x₁ : GalleryAlgebra k Γ (a + b)) ⊗ₜ (x₂ : GalleryAlgebra k Γ (c + d)))).1 := by
  set hbl := isRankOrdered_botLeft u₁ u₂
  set hbr := isRankOrdered_botRight u₁ u₂
  set y := cornerW k hbl hR' x₁ ⊗ₜ[k] cornerW k hbr hR'' x₂
  set q := (repLeft u₁, repLeft u₂, repRight u₁, repRight u₂)
  have hq : (fourChamber a b c d q).IsRankOrdered :=
    (isRankOrdered_chamber_iff _ _).2 ⟨hbl, hbr⟩
  have hE : ∀ {C' : FullChamber Γ (a + b)} {C'' : FullChamber Γ (c + d)}
      (h' : C'.IsRankOrdered) (h'' : C''.IsRankOrdered),
      inductionVal k (rfl : a + b + (c + d) = a + b + (c + d)) (rankE k h' ⊗ₜ rankE k h'') =
        e (chamber C' C'') := fun h' h'' => by
    rw [inductionVal_apply, castGallery_rfl, inductionMap_rankE_tmul_rankE]
    rfl
  have hyR : inductionVal k rfl y * e (chamber R' R'') = inductionVal k rfl y := by
    rw [← hE hR' hR'', ← inductionVal_mul, Algebra.TensorProduct.tmul_mul_tmul,
      cornerW_mul_rankE, cornerW_mul_rankE]
  have hyL : inductionVal k rfl y = e (fourChamber a b c d q) * inductionVal k rfl y := by
    rw [fourChamber, ← hE hbl hbr, ← inductionVal_mul, Algebra.TensorProduct.tmul_mul_tmul,
      rankE_mul_cornerW, rankE_mul_cornerW]
  rw [typeInductionAux_tmul, mul_assoc _ (inductionVal k rfl y), hyR, hyL, ← mul_assoc,
    mul_assoc _ _ (e (fourChamber a b c d q)), typeShuffle_mul_e_fourChamber hD hZ hq,
    mul_assoc (e _)]
  have hc := castGallery_cosetElt_mul_fourShuffle (k := k) hD hZ u₁ u₂
  erw [hc]
  rw [cosetElt, ← mul_assoc, e_mul_r, ite_eq_left (smul_inv_smul _ _).symm]
  rfl

end Juxtapose

end Categorification.WeightedKLR
