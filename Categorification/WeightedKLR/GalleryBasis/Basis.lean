/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Independence
import Categorification.WeightedKLR.GallerySpan.DotsBottom

/-!
# The straight-line gallery basis

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.8 (the
basis theorem), for the gallery algebra. Fix for each pair of full chambers `C, E` a simple
segment `P C E` from a generic point of `C` to a generic point of `E`. Then the elements

  `basisElt k P C E g m = r g E * segGallery P C E * poly (y^m)`

(the straight-line gallery from `C` to `E`, then the relabelling `g`, with the monomial `y^m` in
the dots at the bottom) form a `k`-basis of the gallery algebra (`basisOfSegments`), over every
commutative ring `k`.

The spanning half (`span_segGallery_mul_monomial`) uses Webster's condition (†) (`Γ.Dagger`) and
the absence of loops of weight `0` (`Γ.NoZeroLoops`); the independence half
(`linearIndependent_basisElt`) uses symmetry of the loop polynomials (`Γ.PSymm`) and that the
wall polynomials `Q_e` and the loop polynomials `P_i` are non-zero-divisors. Webster's standing
hypotheses (Section 2.1 of the source: `Q_e` with unit coefficients on its pure monomials) imply
the non-zero-divisor condition; that implication is not formalized here, and the theorem is stated
with the non-zero-divisor condition.

## Main results

* `GalleryAlgebra.basisOfSegments`: the basis for a given choice of segments.
* `GalleryAlgebra.exists_basis`: such a choice of segments exists.
-/

namespace Categorification.WeightedKLR

open MvPolynomial FullChamber Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}

/-- **Webster, Theorem 2.8 (basis theorem)**, for the gallery algebra: for a choice `P` of
simple segments between generic points of the full chambers, the straight-line galleries followed
by a relabelling, with a monomial in the dots at the bottom, form a `k`-basis. -/
noncomputable def basisOfSegments (hP : ∀ C E, IsChamberSegment C E (P C E))
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b)) :
    Module.Basis (FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
      (GalleryAlgebra k Γ ν) :=
  Module.Basis.mk (linearIndependent_basisElt hP hΓ hW hL) <| by
    rw [← span_segGallery_mul_monomial hP hD hZ]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨C, E, g, m, rfl⟩
    exact Submodule.subset_span ⟨(C, E, g, m), rfl⟩

@[simp]
theorem basisOfSegments_apply (hP : ∀ C E, IsChamberSegment C E (P C E))
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b)) (C E : FullChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    basisOfSegments hP hD hZ hΓ hW hL (C, E, g, m) =
      r g E * segGallery P C E * poly (MvPolynomial.monomial m 1) := by
  simp [basisOfSegments, basisElt, segGallery]

/-- **Webster, Theorem 2.8 (basis theorem)**, for the gallery algebra: there is a choice of
simple segments between the full chambers for which the straight-line galleries, relabellings and
monomials in the dots at the bottom form a `k`-basis. -/
theorem exists_basis (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b)) :
    ∃ P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜),
      ∃ b : Module.Basis (FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
        (GalleryAlgebra k Γ ν), ∀ C E g m,
        b (C, E, g, m) = r g E * segGallery P C E * poly (MvPolynomial.monomial m 1) := by
  obtain ⟨P, hP, -⟩ := exists_span_segGallery (k := k) hD hZ
  exact ⟨P, basisOfSegments hP hD hZ hΓ hW hL, basisOfSegments_apply hP hD hZ hΓ hW hL⟩

end GalleryAlgebra

end Categorification.WeightedKLR
