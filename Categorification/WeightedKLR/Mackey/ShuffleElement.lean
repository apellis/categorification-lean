/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.BlockPieces

/-!
# The shuffle element and the factorization `b(g, m) ≡ ι(x) ψ_g ι(y)`

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Let `C` be separated by the strands of `ν'` and `D` by the
strands of `ν₁`. For a relabelling `g`, put `X t = t.IsLeft ν'` and `Y t = (g t).IsLeft ν₁`. The
**shuffle element** `ψ_g = r g (shuffleTop Y C) * w` (`GalleryAlgebra.shuffleElt`) is the gallery
product along a fixed minimal gallery `w` (`GalleryAlgebra.shuffleWord`) from `shuffleBot X Y C`
to `shuffleTop Y C`, followed by the relabelling `g`; it depends only on `X`, `Y`, `C` and `g`, so
only on the shuffle data of `g`, not on the parts of `g` inside the two blocks.

* Any minimal gallery through the middle may be replaced by `w`, modulo basis elements of shuffle
  type in `S` and shorter chosen gallery (`GalleryAlgebra.shuffle_sub_shuffleWord_mem`).
* **Factorization**: `b(g, m) ≡ ι(x) * ψ_g * ι(y)` modulo the same basis elements, for some `x`
  in the tensor product of the gallery algebras of `ν₁`, `ν₂` (decomposition `ν = ν₁ + ν₂`) and
  `y` in that of `ν'`, `ν''` (decomposition `ν = ν' + ν''`), with the dots `y^m` inside `y`
  (`GalleryAlgebra.exists_cornerBasis_sub_shuffleElt_mem`).

Here `ι` is the juxtaposition map `Juxtapose.galleryTensorHom` of the gallery algebras. The
chambers `shuffleBot X Y C` and `shuffleTop Y C` are not rank-ordered in general, so `x` and `y`
are not elements of the corners `W_{ν₁} ⊗ W_{ν₂}`, `W_{ν'} ⊗ W_{ν''}` and `ι` is not
`inductionMap` on them.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

attribute [local instance] ColPerm.fintype

/-- A fixed minimal gallery from `shuffleBot X Y C` to `shuffleTop Y C`. -/
noncomputable def shuffleWord (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X Y : Strand ν → Bool)
    (C : FullChamber Γ ν) : List (Hyp Γ ν) :=
  (exists_goodWord hD hZ (shuffleBot X Y C) (shuffleTop Y C)).choose

theorem goodWord_shuffleWord (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X Y : Strand ν → Bool)
    (C : FullChamber Γ ν) : GoodWord (shuffleBot X Y C).1 (shuffleWord hD hZ X Y C) :=
  (exists_goodWord hD hZ (shuffleBot X Y C) (shuffleTop Y C)).choose_spec.1

theorem flips_shuffleWord (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X Y : Strand ν → Bool)
    (C : FullChamber Γ ν) : (shuffleBot X Y C).flips (shuffleWord hD hZ X Y C) = shuffleTop Y C :=
  (exists_goodWord hD hZ (shuffleBot X Y C) (shuffleTop Y C)).choose_spec.2

variable (k) in
/-- **The shuffle element** `ψ_g`: the gallery product along the fixed minimal gallery
`shuffleWord` from `shuffleBot X Y C` to `shuffleTop Y C`, then the relabelling `g`, where
`X t = t.IsLeft ν'` and `Y t = (g t).IsLeft ν₁`. -/
noncomputable def shuffleElt (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (ν' ν₁ : I →₀ ℕ)
    (g : ColPerm ν) (C : FullChamber Γ ν) : GalleryAlgebra k Γ ν :=
  r g (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) *
    galList k (shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁)) C)
      (shuffleWord hD hZ (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁)) C)

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- **The middle piece is the shuffle element.** In the factorization through the shuffle
(`shuffle_sub_cornerBasis_mem`), any minimal gallery `b` from `shuffleBot X Y C` to
`shuffleTop Y C` may be replaced by the fixed one, `shuffleWord`, modulo basis elements of shuffle
type in `S` and shorter chosen gallery. -/
theorem shuffle_sub_shuffleWord_mem (ν' ν₁ : I →₀ ℕ) {D C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) {S : Set (I → ℕ)} (hS : IsLowerSet S)
    {g : ColPerm ν} (hg : shuffleType ν' ν₁ g ∈ S) {a b c : List (Hyp Γ ν)}
    (ha : GoodWord C.1 a)
    (hfa : C.flips a = shuffleBot (fun t => decide (t.IsLeft ν'))
      (fun t => decide ((g.1 t).IsLeft ν₁)) C)
    (hb : GoodWord (shuffleBot (fun t => decide (t.IsLeft ν'))
      (fun t => decide ((g.1 t).IsLeft ν₁)) C).1 b)
    (hfb : (shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁))
      C).flips b = shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C)
    (hc : GoodWord (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C).1 c)
    (hfc : (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C).flips c = g⁻¹ • D)
    (m : Strand ν →₀ ℕ) :
    r g (g⁻¹ • D) * galList k (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) c *
        galList k (shuffleBot (fun t => decide (t.IsLeft ν'))
          (fun t => decide ((g.1 t).IsLeft ν₁)) C) b * galList k C a *
          poly (monomial m 1) -
      r g (g⁻¹ • D) * galList k (shuffleTop (fun t => decide ((g.1 t).IsLeft ν₁)) C) c *
        galList k (shuffleBot (fun t => decide (t.IsLeft ν'))
          (fun t => decide ((g.1 t).IsLeft ν₁)) C)
          (shuffleWord hD hZ (fun t => decide (t.IsLeft ν'))
            (fun t => decide ((g.1 t).IsLeft ν₁)) C) * galList k C a *
          poly (monomial m 1) ∈
      Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
        shuffleType ν' ν₁ i.1 ∈ S ∧ segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
          (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) := by
  have h₁ := shuffle_sub_cornerBasis_mem hP hD hZ hΓ hW hL ν' ν₁ hC hD' hCs hDs hS hg ha hfa hb
    hfb hc hfc m
  have h₂ := shuffle_sub_cornerBasis_mem hP hD hZ hΓ hW hL ν' ν₁ hC hD' hCs hDs hS hg ha hfa
    (goodWord_shuffleWord hD hZ _ _ C) (flips_shuffleWord hD hZ _ _ C) hc hfc m
  have := Submodule.sub_mem _ h₁ h₂
  rwa [sub_sub_sub_cancel_right] at this

/-- **Factorization of a basis element through the shuffle element.** Let `C`, `D` be
rank-ordered, with the strands of `ν'` to the left in `C` and those of `ν₁` to the left in `D`,
`ν = ν' + ν'' = ν₁ + ν₂`, and let `S` be a lower set of shuffle types containing that of `g`.
Then `b(g, m) ≡ ι(x) * ψ_g * ι(y)` modulo basis elements of shuffle type in `S` and shorter
chosen gallery, for some `x` in the tensor product of the gallery algebras of `ν₁`, `ν₂` and some
`y` in that of `ν'`, `ν''`; the dots `y^m` are part of `y`. Here `ι` is the juxtaposition map of
the gallery algebras and `ψ_g = shuffleElt k hD hZ ν' ν₁ g C`. -/
theorem exists_cornerBasis_sub_shuffleElt_mem {ν' ν'' ν₁ ν₂ : I →₀ ℕ} (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) {D C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) {S : Set (I → ℕ)} (hS : IsLowerSet S)
    {g : ColPerm ν} (hg : shuffleType ν' ν₁ g ∈ S) (m : Strand ν →₀ ℕ) :
    ∃ (x : GalleryAlgebra k Γ ν₁ ⊗[k] GalleryAlgebra k Γ ν₂)
      (y : GalleryAlgebra k Γ ν' ⊗[k] GalleryAlgebra k Γ ν''),
      castGallery k Γ hν₁ (Juxtapose.galleryTensorHom k Γ ν₁ ν₂ x).1 *
          shuffleElt k hD hZ ν' ν₁ g C *
          castGallery k Γ hν' (Juxtapose.galleryTensorHom k Γ ν' ν'' y).1 -
        (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) ∈
      Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
        shuffleType ν' ν₁ i.1 ∈ S ∧ segLength P C (i.1⁻¹ • D) < segLength P C (g⁻¹ • D)} =>
          (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν)) := by
  obtain ⟨a, -, c, ha, hfa, -, -, hc, hfc⟩ := exists_goodWord_shuffle hD hZ
    (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁)) C (g⁻¹ • D)
  have h := shuffle_sub_cornerBasis_mem hP hD hZ hΓ hW hL ν' ν₁ hC hD' hCs hDs hS hg ha hfa
    (goodWord_shuffleWord hD hZ _ _ C) (flips_shuffleWord hD hZ _ _ C) hc hfc m
  obtain ⟨x, hx⟩ := exists_r_mul_top_eq_castGallery (k := k) (ν₂ := ν₂) hν₁ hDs g hc hfc
  obtain ⟨y, hy⟩ := exists_bot_mul_poly_eq_castGallery (k := k) (ν'' := ν'') hν' hCs ha hfa
    (monomial m 1)
  refine ⟨x, y, ?_⟩
  rw [hx, mul_assoc _ (galList k C a), hy] at h
  simpa only [shuffleElt, mul_assoc] using h

end GalleryAlgebra

end Categorification.WeightedKLR
