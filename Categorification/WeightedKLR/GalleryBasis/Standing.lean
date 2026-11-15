/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Calculator.Segment
import Categorification.WeightedKLR.GalleryBasis.Corner
import Categorification.WeightedKLR.Standing

/-!
# The basis theorem under Webster's hypotheses

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.8, with
the hypotheses of the paper: the standing hypothesis of §2.1 on the polynomials `Q_e` and `P_e`
(`WeightedGraph.Standing`) and assumption (†) (`WeightedGraph.Dagger`).

The general results (`basisOfSegments`, `cornerBasis`, `weightedKLRBasis`, `straightBasis`, ...)
assume that the loop polynomials are symmetric and that the wall factors `Q_e(y_a, y_b)` and loop
factors `P_i(y_a, y_b)` are non-zero-divisors; these follow from the standing hypothesis over
every commutative ring `k` (`WeightedGraph.Standing.psymm`, `Standing.isRegular_factor`,
`Standing.isRegular_loopFactor`). The results here carry only Webster's hypotheses.

The hypothesis `WeightedGraph.NoZeroLoops` is part of the encoding, not an assumption of the
paper: a loop of weight `0` at `i` is recorded by its polynomial `P_i` (`WeightedGraph.loop`), not
as an edge, so the edges of a `WeightedGraph` are required not to be loops of weight `0`. Every
graph of the paper is encoded in this way, its loops of weight `0` (at most one at each vertex,
by (†)) going to `loop`.

## Main definitions

* `GalleryAlgebra.cornerBasisOfStanding`, `GalleryAlgebra.chamberBasisOfStanding`: the basis of
  `e D * A * e C` (diagrams from `C` to `D`).
* `GalleryAlgebra.weightedKLRBasisOfStanding`: the basis of Webster's algebra.
* `GalleryAlgebra.cornerPolyEquivOfStanding`: freeness over the polynomials in the dots.
* `GalleryAlgebra.straightBasisOfStanding`, `GalleryAlgebra.straightWeightedKLRBasis`: the
  bases of the gallery algebra and of Webster's algebra for the straight-line choice of the
  diagrams `b_π`.

## Main results

* `GalleryAlgebra.exists_weightedKLRBasis`: Theorem 2.8 for Webster's algebra, for some choice of
  the diagrams `b_π`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial FullChamber Segment

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace GalleryAlgebra

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}

section Segments

variable (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hS : Γ.Standing)

/-- **Webster, Theorem 2.8 (basis theorem)** for the space `e D * A * e C` of diagrams from the
full chamber `C` to the full chamber `D`, under Webster's hypotheses: the elements
`r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)` form a `k`-basis. -/
noncomputable def cornerBasisOfStanding (D C : FullChamber Γ ν) :
    Module.Basis (ColPerm ν × (Strand ν →₀ ℕ)) k (cornerSpace k D C) :=
  cornerBasis hP hD hZ hS.psymm hS.isRegular_factor hS.isRegular_loopFactor' D C

@[simp]
theorem cornerBasisOfStanding_apply (D C : FullChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    (cornerBasisOfStanding hP hD hZ hS D C (g, m) : GalleryAlgebra k Γ ν) =
      r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (monomial m 1) :=
  cornerBasis_apply _ _ _ _ _ _ D C g m

/-- **Webster, Theorem 2.8 (basis theorem)** in Webster's form, under Webster's hypotheses: for
loadings `c` (bottom) and `d` (top), `e d * A * e c` has the `k`-basis `b_π y^m`, one element for
each colour-preserving permutation `π` and each monomial `y^m` in the dots at the bottom. -/
noncomputable def chamberBasisOfStanding (d c : Chamber Γ ν) :
    Module.Basis (ColPerm ν × (Strand ν →₀ ℕ)) k (cornerSpace k d.toFull c.toFull) :=
  chamberBasis hP hD hZ hS.psymm hS.isRegular_factor hS.isRegular_loopFactor' d c

@[simp]
theorem chamberBasisOfStanding_apply (d c : Chamber Γ ν) (π : ColPerm ν) (m : Strand ν →₀ ℕ) :
    (chamberBasisOfStanding hP hD hZ hS d c (π, m) : GalleryAlgebra k Γ ν) =
      r π (π⁻¹ • d.toFull) * segGallery P c.toFull (π⁻¹ • d.toFull) * poly (monomial m 1) :=
  chamberBasis_apply _ _ _ _ _ _ d c π m

/-- **Webster, Theorem 2.8 (basis theorem)** for Webster's weighted KLR algebra, under Webster's
hypotheses: the elements `r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)`, for loadings
(rank-ordered chambers) `C` at the bottom and `D` at the top, colour-preserving permutations `g`
and monomials `m`, form a `k`-basis. -/
noncomputable def weightedKLRBasisOfStanding :
    Module.Basis (RankChamber Γ ν × RankChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
      (weightedKLR k Γ ν) :=
  weightedKLRBasis hP hD hZ hS.psymm hS.isRegular_factor hS.isRegular_loopFactor'

@[simp]
theorem weightedKLRBasisOfStanding_apply (C D : RankChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    (weightedKLRBasisOfStanding hP hD hZ hS (C, D, g, m) : GalleryAlgebra k Γ ν) =
      r g (g⁻¹ • D.1) * segGallery P C.1 (g⁻¹ • D.1) * poly (monomial m 1) :=
  weightedKLRBasis_apply _ _ _ _ _ _ C D g m

/-- **Webster, Theorem 2.8**, as freeness over the polynomials in the dots at the bottom, under
Webster's hypotheses: every element of `e D * A * e C` is `∑_g b(g, 1) * poly (f g)` for unique
polynomials `f g`. -/
noncomputable def cornerPolyEquivOfStanding (D C : FullChamber Γ ν) :
    (ColPerm ν → PolyRing ν k) ≃ₗ[k] cornerSpace k D C :=
  cornerPolyEquiv hP hD hZ hS.psymm hS.isRegular_factor hS.isRegular_loopFactor' D C

theorem cornerPolyEquivOfStanding_apply (D C : FullChamber Γ ν) (f : ColPerm ν → PolyRing ν k) :
    (cornerPolyEquivOfStanding hP hD hZ hS D C f : GalleryAlgebra k Γ ν) =
      ∑ g, cornerElt P D C g * poly (f g) :=
  cornerPolyEquiv_apply _ _ _ _ _ _ D C f

end Segments

/-- **Webster, Theorem 2.8 (basis theorem)** for Webster's weighted KLR algebra, under Webster's
hypotheses (the standing hypothesis of §2.1 and (†)): for some choice of simple segments `P`
between the full chambers, the elements `r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)`
(for loadings `C`, `D`, colour-preserving permutations `g` and monomials `m`) form a `k`-basis. -/
theorem exists_weightedKLRBasis (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    ∃ P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜),
      ∃ b : Module.Basis (RankChamber Γ ν × RankChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
        (weightedKLR k Γ ν), ∀ C D g m,
        (b (C, D, g, m) : GalleryAlgebra k Γ ν) =
          r g (g⁻¹ • D.1) * segGallery P C.1 (g⁻¹ • D.1) * poly (monomial m 1) := by
  obtain ⟨P, hP, -⟩ := exists_span_segGallery (k := k) hD hZ
  exact ⟨P, weightedKLRBasisOfStanding hP hD hZ hS,
    weightedKLRBasisOfStanding_apply hP hD hZ hS⟩

section Straight

variable {ρ : Strand ν → ℕ} {pt : FullChamber Γ ν → Strand ν → 𝕜}
  (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) (hρ : Function.Injective ρ)
  (hρ0 : ∀ s, ρ s ≠ 0) (hpt : ∀ C, IsGeneric Γ (pt C) ∧ fullSigns (pt C) = C.1)

/-- **Webster, Theorem 2.8 (basis theorem)** for the gallery algebra, with the straight-line
choice of basis elements, under Webster's hypotheses. -/
noncomputable def straightBasisOfStanding :
    Module.Basis (FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
      (GalleryAlgebra k Γ ν) :=
  straightBasis hD hZ hS.psymm hS.isRegular_factor hS.isRegular_loopFactor' hρ hρ0 hpt

theorem straightBasisOfStanding_apply (C E : FullChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    straightBasisOfStanding hD hZ hS hρ hρ0 hpt (C, E, g, m) =
      r g E * segGallery (straightSegment ρ pt) C E * poly (monomial m 1) :=
  straightBasis_apply _ _ _ _ _ _ _ _ C E g m

/-- **Webster, Theorem 2.8 (basis theorem)** for Webster's weighted KLR algebra, with the
straight-line choice of the diagrams `b_π`, under Webster's hypotheses: the elements
`r g (g⁻¹ • D) * segGallery (straightSegment ρ pt) C (g⁻¹ • D) * poly (y^m)`, for loadings `C`
(bottom) and `D` (top), colour-preserving permutations `g` and monomials `m`, form a
`k`-basis. -/
noncomputable def straightWeightedKLRBasis :
    Module.Basis (RankChamber Γ ν × RankChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
      (weightedKLR k Γ ν) :=
  weightedKLRBasisOfStanding (isChamberSegment_straightSegment hD hZ hρ hρ0 hpt) hD hZ hS

@[simp]
theorem straightWeightedKLRBasis_apply (C D : RankChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    (straightWeightedKLRBasis hD hZ hS hρ hρ0 hpt (C, D, g, m) : GalleryAlgebra k Γ ν) =
      r g (g⁻¹ • D.1) * segGallery (straightSegment ρ pt) C.1 (g⁻¹ • D.1) *
        poly (monomial m 1) :=
  weightedKLRBasisOfStanding_apply _ _ _ _ C D g m

end Straight

end GalleryAlgebra

end Categorification.WeightedKLR
