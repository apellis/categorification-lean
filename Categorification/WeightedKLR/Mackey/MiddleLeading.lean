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

end Juxtapose

end Categorification.WeightedKLR
