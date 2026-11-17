/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Local.BasisImage
import Categorification.WeightedKLR.Local.WeightedChart
import Categorification.WeightedKLR.GalleryBasis.Standing

/-!
# Stabilizing weighted basis terms in the local chart

Supporting the local-chart proof of B. Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4,
Theorem 2.19 (roadmap A). The local full-gallery preimages of stabilizing
terms of the basis of Theorem 2.8 descend to preimages in Webster's
rank-ordered corners. The incident endpoint idempotents ensure that the
original basis term is absorbed by the weighted star idempotent.
These are supporting lemmas, not statements printed in the source.
-/

noncomputable section

namespace Categorification.WeightedKLR.Local

open GalleryAlgebra MvPolynomial

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- A weighted corner between incident chambers is absorbed on both sides by
the weighted star idempotent. -/
theorem starIdemW_mul_cornerW_mul_starIdemW (p : Strand ν → 𝕜)
    {C D : FullChamber Γ ν} (hRankC : C.IsRankOrdered) (hRankD : D.IsRankOrdered)
    (hC : C.Incident p) (hD : D.Incident p) (x : cornerSpace k D C) :
    starIdemW (Γ := Γ) (k := k) p * cornerW k hRankD hRankC x *
      starIdemW (Γ := Γ) p = cornerW k hRankD hRankC x := by
  let a := cornerW k hRankD hRankC x
  have hl : rankE k hRankD * a = a := rankE_mul_cornerW hRankD hRankC x
  have hr : a * rankE k hRankC = a := cornerW_mul_rankE hRankD hRankC x
  change starIdemW p * a * starIdemW p = a
  calc
    starIdemW p * a * starIdemW p =
        starIdemW p * (rankE k hRankD * a * rankE k hRankC) * starIdemW p := by
      rw [hl, hr]
    _ = (starIdemW p * rankE k hRankD) * a * (rankE k hRankC * starIdemW p) := by
      simp only [mul_assoc]
    _ = a := by
      rw [starIdemW_mul_rankE p hRankD hD, rankE_mul_starIdemW p hRankC hC, hl, hr]

/-- Stabilizing terms of Webster's basis (arXiv:1209.2463v4, Theorem 2.8)
between incident rank-ordered chambers lie in the weighted local-chart image.
This is the weighted basis-range step in the local-chart proof of Theorem 2.19. -/
theorem exists_weighted_cornerElt_mul_poly_preimage (p : Strand ν → 𝕜)
    (hp : ∀ d : Diag ν, 0 ≤ d.val p) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing)
    {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E))
    {C D : FullChamber Γ ν} (hRankC : C.IsRankOrdered) (hRankD : D.IsRankOrdered)
    (hC : C.Incident p) (hD' : D.Incident p) (g : ColPerm ν) (hg : act g p = p)
    (f : PolyRing ν k) :
    ∃ r : WeightedKLRAlgebra k (graph Γ p) (weight p),
      weightedLinearMap p hp hD hZ hS r =
        colourSymCornerProjection (cornerElt P D C g * poly f) := by
  classical
  let := ColPerm.fintype (ν := ν)
  let x := cornerPolyEquivOfStanding hP hD hZ hS D C (Pi.single g f)
  have hx : x.1 = cornerElt P D C g * poly f := by
    rw [cornerPolyEquivOfStanding_apply, Finset.sum_eq_single g]
    · rw [Pi.single_eq_same]
    · intro h _ hh
      rw [Pi.single_eq_of_ne hh, ← polyHom_apply, map_zero, mul_zero]
    · intro hg'
      exact (hg' (Finset.mem_univ g)).elim
  let a := cornerW k hRankD hRankC x
  obtain ⟨b, hb⟩ := exists_cornerElt_mul_poly_preimage p hD hZ hS hP hC hD' g hg f
  have hb' : (galleryHom p hD hZ hS b).1 = a.1 := hb.trans hx.symm
  have ha : starIdemW (Γ := Γ) (k := k) p * a * starIdemW (Γ := Γ) p = a :=
    starIdemW_mul_cornerW_mul_starIdemW p hRankC hRankD hC hD' x
  refine ⟨colourSymCornerProjection b, ?_⟩
  rw [weightedLinearMap_cornerProjection_eq p hp hD hZ hS b a hb' ha]
  apply Subtype.ext
  have ha' := (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).1 a.2
  change a.1 = rankIdem k Γ ν * (cornerElt P D C g * poly f) * rankIdem k Γ ν
  rw [← hx]
  change a.1 = rankIdem k Γ ν * a.1 * rankIdem k Γ ν
  rw [ha'.1, ha'.2]

end Categorification.WeightedKLR.Local
