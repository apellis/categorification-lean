/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.Chart
import Categorification.WeightedKLR.Local.Galleries
import Categorification.WeightedKLR.GalleryBasis.Corner

/-!
# Stabilizing basis terms in the local chart

Supporting the absolute-irreducibility argument for Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19 (roadmap A). A term of the basis of Theorem 2.8 whose endpoint
chambers are incident to a point, and whose colour permutation fixes that point,
lies in the image of the local chart. The polynomial part is localized at its
source idempotent, since the unit of the chart is the sum of incident idempotents.
-/

noncomputable section

namespace Categorification.WeightedKLR.Local

open GalleryAlgebra MvPolynomial Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- Dot polynomials localized at a source idempotent have their expected chart image. -/
theorem galleryVal_poly_mul_e (p : Strand ν → 𝕜) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (f : PolyRing ν k)
    (C : FullChamber (graph Γ p) (weight p)) :
    galleryVal p hD hZ hS (poly ((polyEquiv p).symm f) * e C) =
      poly f * e (chamber p C) := by
  change (galleryHom p hD hZ hS (poly ((polyEquiv p).symm f) * e C)).1 = _
  rw [map_mul, IsIdempotentElem.corner_val_mul, galleryHom_poly, galleryHom_e,
    AlgEquiv.apply_symm_apply, mul_assoc]
  have hu : chartIdem (Γ := Γ) p * e (chamber p C) = e (chamber p C) :=
    chamberIdem_mul_e (chamber p) (chamber_injective p) C
  rw [hu]

/-- Stabilizing terms of Webster's basis (arXiv:1209.2463v4, Theorem 2.8) are in
its local-chart image when both endpoint chambers are incident to the base point.
This is the basis-range step in the local proof of roadmap A for Theorem 2.19. -/
theorem exists_cornerElt_mul_poly_preimage (p : Strand ν → 𝕜) (hD : Γ.Dagger)
    (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E))
    {C D : FullChamber Γ ν} (hC : C.Incident p) (hD' : D.Incident p)
    (g : ColPerm ν) (hg : act g p = p) (f : PolyRing ν k) :
    ∃ b : GalleryAlgebra k (graph Γ p) (weight p),
      (galleryHom p hD hZ hS b).1 = cornerElt P D C g * poly f := by
  let φ := galleryVal p hD hZ hS
  have he : ∀ E, φ (e E) = e (chamber p E) := galleryHom_e p hD hZ hS
  have ht : ∀ E F, φ (t E F) = t (chamber p E) (chamber p F) := galleryHom_t p hD hZ hS
  have hr : ∀ h E, φ (r h E) = r (perm p h) (chamber p E) := galleryHom_r p hD hZ hS
  have hpoly : ∀ f : PolyRing ν k, ∀ E : FullChamber (graph Γ p) (weight p),
      ∃ f' : PolyRing (weight p) k, φ (poly f' * e E) = poly f * e (chamber p E) :=
    fun f E => ⟨(polyEquiv p).symm f, galleryVal_poly_mul_e p hD hZ hS f E⟩
  have hgi : act g⁻¹ p = p := by
    have h := congrArg (act g⁻¹) hg
    rw [← act_mul, inv_mul_cancel, act_one] at h
    exact h.symm
  have hE : (g⁻¹ • D).Incident p := by
    simpa only [hgi] using hD'.smul g⁻¹
  let w := word (hypAff (Γ := Γ)) (P C (g⁻¹ • D)).1 (P C (g⁻¹ • D)).2
  have hw : ∀ h ∈ w, h.val p = 0 := fun h hh =>
    mem_word_active hC hE (hP C (g⁻¹ • D)).2.1 (hP C (g⁻¹ • D)).2.2 h hh
  obtain ⟨b, hb⟩ := exists_term_preimage φ he ht hr hpoly hC hE g hg w hw f
  exact ⟨b, hb⟩

end Categorification.WeightedKLR.Local
