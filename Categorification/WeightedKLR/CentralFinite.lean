/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.CentralPolynomials
import Categorification.WeightedKLR.GalleryBasis.Standing
import Categorification.WeightedKLR.KLR.SpacedComparison
import Categorification.Algebra.ParabolicSymmetricFree
import Categorification.Algebra.AugmentationQuotient

/-!
# Finiteness over the colour-symmetric dots

The algebraic finiteness input of roadmap A0 for Webster, *Weighted
Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Theorem 2.19.
The basis of Theorem 2.8 and the parabolic Artin theorem show that the weighted
algebra is finite over its central colour-symmetric dot polynomials. Its quotient
by their augmentation ideal is therefore finite-dimensional over a field.
This is the algebraic input to the adaptation of Khovanov–Lauda I,
arXiv:0803.4121v2, Proposition 2.12; it does not assert absolute irreducibility.
-/

noncomputable section

namespace Categorification

variable {k R M : Type*} [Field k] [CommRing R] [Algebra k R] [AddCommGroup M]
  [Module R M] [Module k M] [IsScalarTower k R M]

/-- The augmentation quotient of a finite module is finite-dimensional. -/
theorem finiteDimensional_augQuot_of_finite [Module.Finite R M] (ε : R →ₐ[k] k) :
    FiniteDimensional k (M ⧸ augSubmodule M ε) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have : FiniteDimensional k ((Fin n → R) ⧸ augSubmodule (Fin n → R) ε) :=
    finiteDimensional_augQuot (Pi.basisFun R (Fin n)) ε
  let g : (Fin n → R) →ₗ[k] (M ⧸ augSubmodule M ε) :=
    (augSubmodule M ε).mkQ.comp (f.restrictScalars k)
  have hg : augSubmodule (Fin n → R) ε ≤ LinearMap.ker g := by
    intro x hx
    refine augSubmodule_induction hx ?_ ?_
    · intro r hr m
      change (Submodule.Quotient.mk (f (r • m)) : M ⧸ augSubmodule M ε) = 0
      rw [map_smul, Submodule.Quotient.mk_eq_zero]
      exact smul_mem_augSubmodule hr _
    · intro x y hx hy
      exact add_mem hx hy
  let q := (augSubmodule (Fin n → R) ε).liftQ g hg
  apply Module.Finite.of_surjective q
  intro y
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x, rfl⟩ := hf m
  exact ⟨Submodule.Quotient.mk x, rfl⟩

end Categorification

namespace Categorification.WeightedKLR

open MvPolynomial Equiv IsIdempotentElem

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k]
  {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

/-- Polynomials symmetric separately among the strands of each colour. -/
abbrev colourSym (k : Type*) [CommRing k] (ν : I →₀ ℕ) :=
  labelInvariants k (Strand.label (ν := ν))

omit [DecidableEq I] in
theorem colourSym_invariant (f : colourSym k ν) (g : ColPerm ν) :
    rename g.1 (f : PolyRing ν k) = f :=
  f.2 g.1 (funext fun s => congrArg Subtype.val (g.2 s))

/-- The colour-symmetric dot polynomials map into the centre of the gallery algebra. -/
def colourSymGalleryHom (k : Type*) [CommRing k] (Γ : WeightedGraph I 𝕜 k) (ν : I →₀ ℕ) :
    colourSym k ν →ₐ[k] GalleryAlgebra k Γ ν :=
  (polyHom k Γ ν).comp (labelInvariants k (Strand.label (ν := ν))).val

instance colourSymAlgebra : Algebra (colourSym k ν) (GalleryAlgebra k Γ ν) :=
  (colourSymGalleryHom k Γ ν).toRingHom.toAlgebra' fun f a =>
    ((Subalgebra.mem_center_iff.1 (poly_mem_center (colourSym_invariant f))) a).symm

@[simp] theorem colourSym_algebraMap (f : colourSym k ν) :
    algebraMap (colourSym k ν) (GalleryAlgebra k Γ ν) f = poly (f : PolyRing ν k) := rfl

instance colourSym_isScalarTower :
    IsScalarTower k (colourSym k ν) (GalleryAlgebra k Γ ν) :=
  IsScalarTower.of_algebraMap_eq fun c => (colourSymGalleryHom k Γ ν).commutes c |>.symm

instance colourSym_corner_isScalarTower :
    IsScalarTower k (colourSym k ν) (WeightedKLRAlgebra k Γ ν) := by
  constructor
  intro c f a
  apply Subtype.ext
  exact smul_assoc c f a.1

/-- The colour-symmetric dots in Webster's corner algebra. -/
def colourSymHom (k : Type*) [CommRing k] (Γ : WeightedGraph I 𝕜 k) (ν : I →₀ ℕ) :
    colourSym k ν →ₐ[k] WeightedKLRAlgebra k Γ ν :=
  IsScalarTower.toAlgHom k (colourSym k ν) (WeightedKLRAlgebra k Γ ν)

@[simp] theorem colourSymHom_val (f : colourSym k ν) :
    (colourSymHom k Γ ν f).1 = poly (f : PolyRing ν k) * rankIdem k Γ ν := rfl

@[simp] theorem colourSym_smul_val (f : colourSym k ν) (x : WeightedKLRAlgebra k Γ ν) :
    (f • x).1 = poly (f : PolyRing ν k) * x.1 := rfl

/-- The augmentation of the colour-symmetric dots, given by constant coefficient. -/
def colourSymAug (k : Type*) [CommRing k] (ν : I →₀ ℕ) : colourSym k ν →ₐ[k] k :=
  (aeval fun _ => (0 : k)).comp (labelInvariants k (Strand.label (ν := ν))).val

omit [DecidableEq I] in
@[simp] theorem colourSymAug_apply (f : colourSym k ν) :
    colourSymAug k ν f = constantCoeff (f : PolyRing ν k) := by
  simp [colourSymAug]

/-- Right multiplication by dot polynomials is linear over the central invariants. -/
def colourSymPolyRight (a : GalleryAlgebra k Γ ν) :
    PolyRing ν k →ₗ[colourSym k ν] GalleryAlgebra k Γ ν where
  toFun f := a * poly f
  map_add' f g := by rw [← polyHom_apply, map_add, mul_add]; rfl
  map_smul' f p := by
    change a * poly ((f : PolyRing ν k) * p) = poly (f : PolyRing ν k) * (a * poly p)
    rw [← poly_mul_poly, ← mul_assoc,
      (Subalgebra.mem_center_iff.1 (poly_mem_center (colourSym_invariant f))) a, mul_assoc]

attribute [local instance] ColPerm.fintype

/-- The gallery algebra is finite over the central colour-symmetric dots, by
Webster arXiv:1209.2463v4, Theorem 2.8, and the parabolic Artin theorem. -/
theorem finite_gallery_colourSym (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    Module.Finite (colourSym k ν) (GalleryAlgebra k Γ ν) := by
  classical
  obtain ⟨P, hP, -⟩ := exists_span_segGallery (k := k) (ν := ν) hD hZ
  let b := basisOfSegments hP hD hZ hS.psymm hS.isRegular_factor hS.isRegular_loopFactor'
  let T := FullChamber Γ ν × FullChamber Γ ν × ColPerm ν
  let F : (T → PolyRing ν k) →ₗ[colourSym k ν] GalleryAlgebra k Γ ν :=
    LinearMap.lsum (colourSym k ν) (fun _ : T => PolyRing ν k) (colourSym k ν)
      (fun i => colourSymPolyRight (r i.2.2 i.2.1 * segGallery P i.1 i.2.1))
  have hF : Function.Surjective F := by
    rw [← LinearMap.range_eq_top]
    apply top_unique
    change (⊤ : Submodule k (GalleryAlgebra k Γ ν)) ≤ (LinearMap.range F).restrictScalars k
    rw [← b.span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨C, E, g, m⟩, rfl⟩
    refine ⟨Pi.single (C, E, g) (monomial m 1), ?_⟩
    rw [show F (Pi.single (C, E, g) (monomial m 1)) =
      colourSymPolyRight (r g E * segGallery P C E) (monomial m 1) from
        LinearMap.lsum_piSingle _ _ _ _ _ _]
    exact (basisOfSegments_apply hP hD hZ hS.psymm hS.isRegular_factor
      hS.isRegular_loopFactor' C E g m).symm
  exact Module.Finite.of_surjective F hF

/-- The central-linear projection from the gallery algebra to Webster's corner. -/
def colourSymCornerProjection :
    GalleryAlgebra k Γ ν →ₗ[colourSym k ν] WeightedKLRAlgebra k Γ ν where
  toFun x := ⟨rankIdem k Γ ν * x * rankIdem k Γ ν,
    mem_weightedKLR_iff_mem_corner.1 ⟨x, sandwich_apply _ _ _⟩⟩
  map_add' x y := Subtype.ext (by simp only [mul_add, add_mul]; rfl)
  map_smul' f x := Subtype.ext (by
    change rankIdem k Γ ν * (f • x) * rankIdem k Γ ν =
      f • (rankIdem k Γ ν * x * rankIdem k Γ ν)
    rw [mul_smul_comm, smul_mul_assoc])

theorem colourSymCornerProjection_surjective :
    Function.Surjective (colourSymCornerProjection (k := k) (Γ := Γ) (ν := ν)) := by
  intro x
  refine ⟨x.1, Subtype.ext ?_⟩
  have hx := (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).1 x.2
  change rankIdem k Γ ν * x.1 * rankIdem k Γ ν = x.1
  exact (congrArg (fun a => a * rankIdem k Γ ν) hx.1).trans hx.2

/-- Webster arXiv:1209.2463v4, Theorem 2.8, and the parabolic Artin theorem:
Webster's algebra is a finite module over its central colour-symmetric dots.
Hypotheses are those of the weighted basis theorem; no restriction excluding nonzero-weight loops is added. -/
theorem finite_colourSym (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    Module.Finite (colourSym k ν) (WeightedKLRAlgebra k Γ ν) := by
  have := finite_gallery_colourSym (ν := ν) hD hZ hS
  exact Module.Finite.of_surjective colourSymCornerProjection colourSymCornerProjection_surjective

/-- The augmentation quotient of Webster's algebra is finite-dimensional over
any field, as required by the adaptation of KL I Proposition 2.12 in roadmap A0
for Webster arXiv:1209.2463v4, Theorem 2.19. -/
theorem finiteDimensional_quotient_colourSymAug {k : Type*} [Field k]
    {Γ : WeightedGraph I 𝕜 k}
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing) :
    FiniteDimensional k (WeightedKLRAlgebra k Γ ν ⧸
      augSubmodule (WeightedKLRAlgebra k Γ ν) (colourSymAug k ν)) := by
  have := finite_colourSym (ν := ν) hD hZ hS
  exact finiteDimensional_augQuot_of_finite (colourSymAug k ν)

end GalleryAlgebra

end Categorification.WeightedKLR
