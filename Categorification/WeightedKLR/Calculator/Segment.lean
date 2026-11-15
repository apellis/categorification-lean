/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Calculator.Perturbation
import Categorification.WeightedKLR.GalleryBasis.Basis

/-!
# The straight-line choice of basis elements

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.8: the
basis theorem holds for any choice of diagrams `b_π` in which no two strands, and no strand and
ghost, cross twice; in the gallery algebra, for any choice of simple segments between the full
chambers (`GalleryAlgebra.basisOfSegments`). This file fixes one choice, the straight-line
diagrams with infinitesimally perturbed top end points, so that the basis is the one used by the
diagrammatic calculator:

Fix a generic configuration `pt C` in every full chamber `C` and an injective `ρ : Strand ν → ℕ`
with positive values (for instance `ρ s` the position of `s` at the top, counted from `1`). The
segment for `(C, E)` runs from `pt C` to `pt E + (ε ^ ρ s)_s` with `ε > 0` infinitesimal. By
`Segment.exists_stablePerturbation`, for all sufficiently small `ε > 0` this segment is simple, its
end point lies in `E`, and its word, hence its gallery, does not depend on `ε`.

The only input beyond genericity of the points is that distinct hyperplanes of the arrangement are
distinct as sets (`hdist`), which holds under (†) and the absence of loops of weight `0`; without
it two hyperplanes would be crossed at the same time by every segment.

## Main definitions

* `GalleryAlgebra.perturbSize ρ p q`: a value of `ε` in the range where the word is stable.
* `GalleryAlgebra.straightSegment ρ pt C E`: the segment from `pt C` to `pt E` perturbed by
  `perturbSize`.
* `GalleryAlgebra.straightBasis`: the basis of Theorem 2.8 for this choice.

## Main results

* `GalleryAlgebra.exists_stablePerturbation_hypAff`: the perturbation is stable for small `ε`.
* `GalleryAlgebra.isChamberSegment_straightSegment`: the choice is valid.
* `GalleryAlgebra.word_straightSegment`, `GalleryAlgebra.segGallery_straightSegment`: its word and
  gallery are those of every sufficiently small perturbation.
* `GalleryAlgebra.straightBasis_apply`.
-/

namespace Categorification.WeightedKLR

open Segment FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

open Classical in
variable (Γ) in
/-- A value of `ε` in a range where the segment from `p` to `perturb ρ q ε` is stable (half of a
stability bound, when one exists). -/
noncomputable def perturbSize (ρ : Strand ν → ℕ) (p q : Strand ν → 𝕜) : 𝕜 :=
  if h : ∃ ε₀, StablePerturbation (hypAff (Γ := Γ)) ρ p q ε₀ then h.choose / 2 else 1

/-- The straight segment from the representative point of `C` to the representative point of `E`
with its end point moved by `s ↦ ε ^ ρ s`, `ε = perturbSize`. -/
noncomputable def straightSegment (ρ : Strand ν → ℕ) (pt : FullChamber Γ ν → Strand ν → 𝕜)
    (C E : FullChamber Γ ν) : (Strand ν → 𝕜) × (Strand ν → 𝕜) :=
  (pt C, perturb ρ (pt E) (perturbSize Γ ρ (pt C) (pt E)))

variable {ρ : Strand ν → ℕ}

/-- Infinitesimal perturbation of the top end point, for the arrangement of walls and
diagonals. -/
theorem exists_stablePerturbation_hypAff (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hρ : Function.Injective ρ) (hρ0 : ∀ s, ρ s ≠ 0) {p q : Strand ν → 𝕜} (hp : IsGeneric Γ p)
    (hq : IsGeneric Γ q) : ∃ ε₀, StablePerturbation (hypAff (Γ := Γ)) ρ p q ε₀ :=
  exists_stablePerturbation hρ hρ0 (hdist hD hZ) hp hq

theorem perturbSize_mem (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hρ : Function.Injective ρ)
    (hρ0 : ∀ s, ρ s ≠ 0) {p q : Strand ν → 𝕜} (hp : IsGeneric Γ p) (hq : IsGeneric Γ q) :
    ∃ ε₀, StablePerturbation (hypAff (Γ := Γ)) ρ p q ε₀ ∧ 0 < perturbSize Γ ρ p q ∧
      perturbSize Γ ρ p q < ε₀ := by
  have h := exists_stablePerturbation_hypAff hD hZ hρ hρ0 hp hq
  simp only [perturbSize, h, ↓reduceDIte]
  have h0 := h.choose_spec.1
  exact ⟨h.choose, h.choose_spec, by linarith, by linarith⟩

variable {pt : FullChamber Γ ν → Strand ν → 𝕜}

/-- The word of the straight segment is the word of every sufficiently small perturbation of the
top end point. -/
theorem word_straightSegment (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hρ : Function.Injective ρ)
    (hρ0 : ∀ s, ρ s ≠ 0) (hpt : ∀ C, IsGeneric Γ (pt C)) (C E : FullChamber Γ ν) :
    ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      word (hypAff (Γ := Γ)) (pt C) (perturb ρ (pt E) ε) =
        word (hypAff (Γ := Γ)) (straightSegment ρ pt C E).1 (straightSegment ρ pt C E).2 := by
  obtain ⟨ε₀, hst, h0, h1⟩ := perturbSize_mem hD hZ hρ hρ0 (hpt C) (hpt E)
  exact ⟨ε₀, hst.1, fun ε hε hεε => (hst.2 ε hε hεε).2.2 _ h0 h1⟩

/-- **Webster, Theorem 2.8**: the straight segments with perturbed top end points are a valid
choice of simple segments between the full chambers. -/
theorem isChamberSegment_straightSegment (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hρ : Function.Injective ρ) (hρ0 : ∀ s, ρ s ≠ 0)
    (hpt : ∀ C, IsGeneric Γ (pt C) ∧ fullSigns (pt C) = C.1) (C E : FullChamber Γ ν) :
    IsChamberSegment C E (straightSegment ρ pt C E) := by
  obtain ⟨ε₀, hst, h0, h1⟩ := perturbSize_mem hD hZ hρ hρ0 (hpt C).1 (hpt E).1
  obtain ⟨hs, hsg, -⟩ := hst.2 _ h0 h1
  exact ⟨hs, (hpt C).2, (hsg.trans (signs_hypAff _)).trans (hpt E).2⟩

/-- The gallery of the straight segment from `C` to `E` is the gallery of the word of every
sufficiently small perturbation of the top end point. -/
theorem segGallery_straightSegment (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hρ : Function.Injective ρ) (hρ0 : ∀ s, ρ s ≠ 0) (hpt : ∀ C, IsGeneric Γ (pt C))
    (C E : FullChamber Γ ν) :
    ∃ ε₀, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      segGallery (k := k) (straightSegment ρ pt) C E =
        galList k C (word (hypAff (Γ := Γ)) (pt C) (perturb ρ (pt E) ε)) := by
  obtain ⟨ε₀, h0, hw⟩ := word_straightSegment hD hZ hρ hρ0 hpt C E
  exact ⟨ε₀, h0, fun ε hε hεε => by rw [segGallery, hw ε hε hεε]⟩

/-- **Webster, Theorem 2.8 (basis theorem)**, for the gallery algebra, with the straight-line
choice of basis elements. -/
noncomputable def straightBasis (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b))
    (hρ : Function.Injective ρ) (hρ0 : ∀ s, ρ s ≠ 0)
    (hpt : ∀ C, IsGeneric Γ (pt C) ∧ fullSigns (pt C) = C.1) :
    Module.Basis (FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
      (GalleryAlgebra k Γ ν) :=
  basisOfSegments (isChamberSegment_straightSegment hD hZ hρ hρ0 hpt) hD hZ hΓ hW hL

theorem straightBasis_apply (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b))
    (hρ : Function.Injective ρ) (hρ0 : ∀ s, ρ s ≠ 0)
    (hpt : ∀ C, IsGeneric Γ (pt C) ∧ fullSigns (pt C) = C.1) (C E : FullChamber Γ ν)
    (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    straightBasis hD hZ hΓ hW hL hρ hρ0 hpt (C, E, g, m) =
      r g E * segGallery (straightSegment ρ pt) C E * poly (MvPolynomial.monomial m 1) :=
  basisOfSegments_apply _ hD hZ hΓ hW hL C E g m

end GalleryAlgebra

end Categorification.WeightedKLR
