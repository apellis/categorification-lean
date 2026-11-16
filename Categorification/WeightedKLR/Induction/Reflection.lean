/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Reflection
import Categorification.WeightedKLR.Induction.TensorMap

/-!
# The vertical reflection and juxtaposition

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4.

Turning diagrams upside down commutes with placing them side by side: the vertical reflection
`GalleryAlgebra.reflect` of the gallery algebra of `ν' + ν''` restricts on juxtaposed diagrams to
the reflections of the two factors. Consequently it preserves Webster's algebra `W_ν` (the corner
of the rank-ordered idempotent) and the idempotent `e_{ν';ν''}`, and intertwines Webster's map
`ι_{ν';ν''}` with the reflections of `W_{ν'}` and `W_{ν''}`. This is what converts statements
about `W_{ν'+ν''} e_{ν';ν''}` as a right `W_{ν'} ⊗ W_{ν''}`-module into statements about
`e_{ν';ν''} W_{ν'+ν''}` as a left module, i.e. about restriction.

## Main results

* `ChamberEmbedding.reflect_galleryHom`: reflection commutes with the embedding of a block.
* `Juxtapose.reflect_galleryTensorHom_tmul`: `σ(x ∘ y) = σ(x) ∘ σ(y)` for juxtaposition.
* `GalleryAlgebra.reflectW`: the reflection of Webster's algebra `W_ν`, an anti-involution.
* `Juxtapose.reflectW_inductionMap`: `σ ∘ ι_{ν';ν''} = ι_{ν';ν''} ∘ (σ ⊗ σ)`.
-/

namespace Categorification.WeightedKLR

open MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GalleryAlgebra

variable {ν : I →₀ ℕ}

theorem reflect_sum (hΓ : Γ.PSymm) {ι : Type*} (s : Finset ι) (f : ι → GalleryAlgebra k Γ ν) :
    reflect k hΓ (∑ i ∈ s, f i) = ∑ i ∈ s, reflect k hΓ (f i) := by
  simp only [reflect, map_sum, Finset.unop_sum]

theorem reflect_algebraMap (hΓ : Γ.PSymm) (c : k) :
    reflect k hΓ (algebraMap k (GalleryAlgebra k Γ ν) c) = algebraMap k _ c := by
  rw [Algebra.algebraMap_eq_smul_one, reflect_smul, reflect_one]

theorem reflect_rankIdem (hΓ : Γ.PSymm) : reflect k hΓ (rankIdem k Γ ν) = rankIdem k Γ ν := by
  simp only [rankIdem, reflect_sum, reflect_e]

theorem reflect_mem_corner (hΓ : Γ.PSymm) {x : GalleryAlgebra k Γ ν}
    (hx : x ∈ Subsemigroup.corner (rankIdem k Γ ν)) :
    reflect k hΓ x ∈ Subsemigroup.corner (rankIdem k Γ ν) := by
  rw [Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem] at hx ⊢
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← reflect_rankIdem hΓ, ← reflect_mul, hx.2]
  · conv_lhs => rw [← reflect_rankIdem hΓ, ← reflect_mul, hx.1]

variable (k ν) in
/-- The vertical reflection of Webster's algebra `W_ν`, as a `k`-linear map. It reverses
products (`reflectW_mul`) and is an involution (`reflectW_reflectW`). -/
noncomputable def reflectW (hΓ : Γ.PSymm) :
    WeightedKLRAlgebra k Γ ν →ₗ[k] WeightedKLRAlgebra k Γ ν where
  toFun x := ⟨reflect k hΓ x.1, reflect_mem_corner hΓ x.2⟩
  map_add' x y := Subtype.ext (reflect_add hΓ x.1 y.1)
  map_smul' c x := Subtype.ext (reflect_smul hΓ c x.1)

@[simp] theorem reflectW_val (hΓ : Γ.PSymm) (x : WeightedKLRAlgebra k Γ ν) :
    (reflectW k ν hΓ x).1 = reflect k hΓ x.1 := rfl

theorem reflectW_mul (hΓ : Γ.PSymm) (x y : WeightedKLRAlgebra k Γ ν) :
    reflectW k ν hΓ (x * y) = reflectW k ν hΓ y * reflectW k ν hΓ x :=
  Subtype.ext (reflect_mul hΓ x.1 y.1)

theorem reflectW_one (hΓ : Γ.PSymm) :
    reflectW k ν hΓ (1 : WeightedKLRAlgebra k Γ ν) = 1 :=
  Subtype.ext (reflect_rankIdem hΓ)

theorem reflectW_reflectW (hΓ : Γ.PSymm) (x : WeightedKLRAlgebra k Γ ν) :
    reflectW k ν hΓ (reflectW k ν hΓ x) = x :=
  Subtype.ext (reflect_reflect hΓ x.1)

end GalleryAlgebra

open GalleryAlgebra

namespace ChamberEmbedding

variable {ν₁ ν : I →₀ ℕ} (J : ChamberEmbedding Γ ν₁ ν)

theorem reflect_idem (hΓ : Γ.PSymm) : reflect k hΓ (J.idem (k := k)) = J.idem := by
  simp only [idem, reflect_sum, reflect_e]

/-- Reflection commutes with the embedding of the diagrams of a block. -/
theorem reflect_galleryHom (hΓ : Γ.PSymm) (x : GalleryAlgebra k Γ ν₁) :
    reflect k hΓ (J.galleryHom x).1 = (J.galleryHom (reflect k hΓ x)).1 := by
  obtain ⟨x, rfl⟩ := mk_surjective x
  induction x using FreeAlgebra.induction with
  | grade0 c =>
    rw [AlgHom.commutes, reflect_algebraMap, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    change reflect k hΓ (c • J.idem) = c • J.idem
    rw [reflect_smul, J.reflect_idem hΓ]
  | grade1 g =>
    cases g with
    | idem C =>
      change reflect k hΓ (J.galleryHom (e C)).1 = (J.galleryHom (reflect k hΓ (e C))).1
      rw [reflect_e, galleryHom_e, reflect_e]
    | poly f =>
      change reflect k hΓ (J.galleryHom (poly f)).1 = (J.galleryHom (reflect k hΓ (poly f))).1
      rw [galleryHom_poly, reflect_mul, J.reflect_idem hΓ, reflect_poly, reflect_poly,
        galleryHom_poly, J.idem_mul_poly]
    | step C D =>
      change reflect k hΓ (J.galleryHom (t C D)).1 = (J.galleryHom (reflect k hΓ (t C D))).1
      rw [galleryHom_t, reflect_t, reflect_t, galleryHom_t]
    | relabel g C =>
      change reflect k hΓ (J.galleryHom (r g C)).1 = (J.galleryHom (reflect k hΓ (r g C))).1
      rw [galleryHom_r, reflect_r, reflect_r, galleryHom_r, map_inv, J.smul_chamber]
  | mul a b ha hb =>
    have h₁ : (J.galleryHom (GalleryAlgebra.mk k Γ ν₁ (a * b))).1 =
        (J.galleryHom (GalleryAlgebra.mk k Γ ν₁ a)).1 *
          (J.galleryHom (GalleryAlgebra.mk k Γ ν₁ b)).1 := by
      rw [map_mul, map_mul]; rfl
    have h₂ : (J.galleryHom (reflect k hΓ (GalleryAlgebra.mk k Γ ν₁ (a * b)))).1 =
        (J.galleryHom (reflect k hΓ (GalleryAlgebra.mk k Γ ν₁ b))).1 *
          (J.galleryHom (reflect k hΓ (GalleryAlgebra.mk k Γ ν₁ a))).1 := by
      rw [map_mul, reflect_mul, map_mul]; rfl
    rw [h₁, h₂, reflect_mul, ha, hb]
  | add a b ha hb =>
    have h₁ : (J.galleryHom (GalleryAlgebra.mk k Γ ν₁ (a + b))).1 =
        (J.galleryHom (GalleryAlgebra.mk k Γ ν₁ a)).1 +
          (J.galleryHom (GalleryAlgebra.mk k Γ ν₁ b)).1 := by
      rw [map_add, map_add]; rfl
    have h₂ : (J.galleryHom (reflect k hΓ (GalleryAlgebra.mk k Γ ν₁ (a + b)))).1 =
        (J.galleryHom (reflect k hΓ (GalleryAlgebra.mk k Γ ν₁ a))).1 +
          (J.galleryHom (reflect k hΓ (GalleryAlgebra.mk k Γ ν₁ b))).1 := by
      rw [map_add, reflect_add, map_add]; rfl
    rw [h₁, h₂, reflect_add, ha, hb]

end ChamberEmbedding

namespace Juxtapose

variable {ν' ν'' : I →₀ ℕ}

theorem reflect_leftHom (hΓ : Γ.PSymm) (x : GalleryAlgebra k Γ ν') :
    reflect k hΓ (leftHom k Γ ν' ν'' x).1 = (leftHom k Γ ν' ν'' (reflect k hΓ x)).1 := by
  simp only [leftHom, IsIdempotentElem.cornerSum_val, reflect_sum,
    ChamberEmbedding.reflect_galleryHom]

theorem reflect_rightHom (hΓ : Γ.PSymm) (y : GalleryAlgebra k Γ ν'') :
    reflect k hΓ (rightHom k Γ ν' ν'' y).1 = (rightHom k Γ ν' ν'' (reflect k hΓ y)).1 := by
  simp only [rightHom, IsIdempotentElem.cornerSum_val, reflect_sum,
    ChamberEmbedding.reflect_galleryHom]

/-- Reflecting a juxtaposition of two diagrams juxtaposes their reflections. -/
theorem reflect_galleryTensorHom_tmul (hΓ : Γ.PSymm) (x : GalleryAlgebra k Γ ν')
    (y : GalleryAlgebra k Γ ν'') :
    reflect k hΓ (galleryTensorHom k Γ ν' ν'' (x ⊗ₜ y)).1 =
      (galleryTensorHom k Γ ν' ν'' (reflect k hΓ x ⊗ₜ reflect k hΓ y)).1 := by
  rw [galleryTensorHom_tmul, galleryTensorHom_tmul]
  change reflect k hΓ ((leftHom k Γ ν' ν'' x).1 * (rightHom k Γ ν' ν'' y).1) =
    (leftHom k Γ ν' ν'' (reflect k hΓ x)).1 * (rightHom k Γ ν' ν'' (reflect k hΓ y)).1
  rw [reflect_mul, reflect_leftHom, reflect_rightHom]
  exact congrArg Subtype.val (commute_leftHom_rightHom _ _).eq.symm

theorem reflect_splitIdem (hΓ : Γ.PSymm) :
    reflect k hΓ (splitIdem k Γ ν' ν'') = splitIdem k Γ ν' ν'' := by
  simp only [splitIdem, reflect_sum, reflect_e]

/-- **Reflection intertwines Webster's map `ι_{ν';ν''}`**: `σ(ι(z)) = ι((σ ⊗ σ) z)`. -/
theorem reflectW_inductionMap (hΓ : Γ.PSymm)
    (z : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    reflectW k (ν' + ν'') hΓ (inductionMap k Γ ν' ν'' z) =
      inductionMap k Γ ν' ν'' (TensorProduct.map (reflectW k ν' hΓ) (reflectW k ν'' hΓ) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    apply Subtype.ext
    rw [reflectW_val, TensorProduct.map_tmul, inductionMap_tmul, inductionMap_tmul,
      reflectW_val, reflectW_val]
    exact reflect_galleryTensorHom_tmul hΓ x.1 y.1
  | add a b ha hb => simp only [map_add, ha, hb]

end Juxtapose

end Categorification.WeightedKLR
