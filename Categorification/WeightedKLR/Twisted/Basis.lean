/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Twisted.Independence
import Categorification.WeightedKLR.Twisted.DotsBottom

/-!
# The straight-line basis of the twisted gallery algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.5,
Proposition 2.20, second assertion: the morphism spaces of the category `P` of pairs of a loading
and a weighting have a basis given by a fixed stringing-up of each permutation times the
monomials in the dots. Here `P` is read as the twisted gallery algebra `TwGalleryAlgebra k Γ ν`,
one idempotent for each chamber of the arrangement of positions and weights. Fix for each pair of
chambers `C, E` a simple segment `P C E` from a generic point of `C` to a generic point of `E`
(the stringing-up). Then the elements

  `basisElt k P C E g m = r g E * segGallery P C E * poly (y^m)`

form a `k`-basis (`basisOfSegments`), over every commutative ring `k`.

The proof is that of Theorem 2.8, as the source says. The spanning half
(`span_segGallery_mul_monomial`) needs no hypothesis on the graph: Webster's condition (†) and
the absence of loops of weight `0`, which Theorem 2.8 needs for the gallery algebra of one
weighting, are not needed here, because the weights of the edges are coordinates of the
arrangement, so its hyperplanes are distinct and its codimension-two flats are the blocks of the
braid moves of the algebra (including the block of a strand, its ghost along a loop and the
reflected ghost). The independence half (`linearIndependent_basisElt`) uses symmetry of the loop
polynomials (`Γ.PSymm`, needed for the polynomial representation) and that the wall polynomials
`Q_e` and the loop polynomials `P_i` are non-zero-divisors; as for Theorem 2.8, Webster's
standing hypotheses imply the latter, an implication not formalized here.

## Main results

* `TwGalleryAlgebra.basisOfSegments`: the basis for a given choice of segments.
* `TwGalleryAlgebra.exists_basis`: such a choice of segments exists.
-/

namespace Categorification.WeightedKLR

open MvPolynomial TwChamber Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace TwGalleryAlgebra

variable {P : TwChamber Γ ν → TwChamber Γ ν → (Strand ν ⊕ Γ.E → 𝕜) × (Strand ν ⊕ Γ.E → 𝕜)}

/-- **Webster, Proposition 2.20 (basis of the morphism spaces of `P`)**: for a choice `P` of
simple segments between generic points of the chambers of the arrangement of positions and
weights, the straight-line galleries followed by a relabelling, with a monomial in the dots at the
bottom, form a `k`-basis of the twisted gallery algebra. -/
noncomputable def basisOfSegments (hP : ∀ C E, IsChamberSegment C E (P C E)) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b)) :
    Module.Basis (TwChamber Γ ν × TwChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
      (TwGalleryAlgebra k Γ ν) :=
  Module.Basis.mk (linearIndependent_basisElt hP hΓ hW hL) <| by
    rw [← span_segGallery_mul_monomial hP]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨C, E, g, m, rfl⟩
    exact Submodule.subset_span ⟨(C, E, g, m), rfl⟩

@[simp]
theorem basisOfSegments_apply (hP : ∀ C E, IsChamberSegment C E (P C E)) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b)) (C E : TwChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    basisOfSegments hP hΓ hW hL (C, E, g, m) =
      r g E * segGallery P C E * poly (MvPolynomial.monomial m 1) := by
  simp [basisOfSegments, basisElt]

/-- **Webster, Proposition 2.20 (basis of the morphism spaces of `P`)**: there is a choice of
simple segments between the chambers of the arrangement of positions and weights for which the
straight-line galleries, relabellings and monomials in the dots at the bottom form a `k`-basis of
the twisted gallery algebra. -/
theorem exists_basis (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b)) :
    ∃ P : TwChamber Γ ν → TwChamber Γ ν → (Strand ν ⊕ Γ.E → 𝕜) × (Strand ν ⊕ Γ.E → 𝕜),
      ∃ b : Module.Basis (TwChamber Γ ν × TwChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
        (TwGalleryAlgebra k Γ ν), ∀ C E g m,
        b (C, E, g, m) = r g E * segGallery P C E * poly (MvPolynomial.monomial m 1) := by
  choose P hP using exists_isChamberSegment (Γ := Γ) (ν := ν)
  exact ⟨P, basisOfSegments hP hΓ hW hL, basisOfSegments_apply hP hΓ hW hL⟩

end TwGalleryAlgebra

end Categorification.WeightedKLR
