/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Standing
import Categorification.WeightedKLR.Grading

/-!
# The basis of the gallery algebra is homogeneous

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.8 and the
degree function of §2.1. For every grading datum `G` (`WeightedKLR.GradingDatum`), each element
`r g E * segGallery P C E * poly (y^m)` of the basis of Theorem 2.8 is homogeneous, of degree the
sum of the degrees of the steps of the chosen gallery plus the degree of the monomial `y^m`. In
particular the basis is a homogeneous basis for the grading of Webster's standing hypothesis
(`WeightedGraph.Standing.gradingDatum`).

## Main results

* `GradingDatum.segGallery_mem_grade`, `GradingDatum.basisOfSegments_mem_grade`.
* `GalleryAlgebra.straightBasisOfStanding_mem_grade`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial FullChamber Segment GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GradingDatum

variable (G : GradingDatum Γ)
  (P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜))

/-- The degree of the chosen gallery from `C` to `E`. -/
noncomputable def segDeg (C E : FullChamber Γ ν) : ℤ :=
  G.galDeg C (word (hypAff (Γ := Γ)) (P C E).1 (P C E).2)

theorem segGallery_mem_grade (C E : FullChamber Γ ν) :
    segGallery (k := k) P C E ∈ G.grade ν (G.segDeg P C E) :=
  G.galList_mem_grade C _

/-- **The basis of Webster's Theorem 2.8 is homogeneous**: the basis element indexed by
`(C, E, g, m)` has degree `segDeg P C E + ∑_s m_s · dot (label s)`. -/
theorem basisOfSegments_mem_grade {P} (hP : ∀ C E, IsChamberSegment C E (P C E))
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b)) (C E : FullChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    basisOfSegments hP hD hZ hΓ hW hL (C, E, g, m) ∈
      G.grade ν (G.segDeg P C E + Finsupp.weight G.wt m) := by
  rw [basisOfSegments_apply]
  exact G.r_mul_galList_mul_poly_mem_grade g E C _ m

end GradingDatum

namespace GalleryAlgebra

variable {ρ : Strand ν → ℕ} {pt : FullChamber Γ ν → Strand ν → 𝕜}
  (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (hρ : Function.Injective ρ)
  (hρ0 : ∀ s, ρ s ≠ 0) (hpt : ∀ C, IsGeneric Γ (pt C) ∧ fullSigns (pt C) = C.1)

/-- **Webster, Theorem 2.8, graded form**: under Webster's hypotheses the straight-line basis of
the gallery algebra consists of homogeneous elements for the grading of the standing hypothesis
(doubled normalization, `WeightedGraph.Standing.gradingDatum`). -/
theorem straightBasisOfStanding_mem_grade (C E : FullChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    straightBasisOfStanding hD hZ hS hρ hρ0 hpt (C, E, g, m) ∈
      hS.gradingDatum.grade ν (hS.gradingDatum.segDeg (straightSegment ρ pt) C E +
        Finsupp.weight hS.gradingDatum.wt m) := by
  rw [straightBasisOfStanding_apply]
  exact hS.gradingDatum.r_mul_galList_mul_poly_mem_grade g E C _ m

end GalleryAlgebra

end Categorification.WeightedKLR
