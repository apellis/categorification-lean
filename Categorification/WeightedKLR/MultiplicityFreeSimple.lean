/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Simple
import Categorification.WeightedKLR.Induction.Restriction
import Categorification.KLR.ExtTensorK0Equiv

/-!
# Scalar endomorphisms at multiplicity-free weights

An intermediate step toward roadmap A of Webster, *Weighted Khovanov–Lauda–Rouquier
algebras*, arXiv:1209.2463v4, §2.4, Theorem 2.19. The extra hypothesis
`∀ i, ν i ≤ 1` makes each diagonal chamber corner polynomial, by Theorem 2.8.
The central augmentation annihilation proved using Khovanov–Lauda I,
arXiv:0803.4121v2, §2.5, Proposition 2.12 then makes that corner act by scalars.
This gives scalar endomorphisms of graded simples without restrictions on cycles
or on the standing polynomials. It is an intermediate weighted analogue of
KL I, §3.2, Corollary 3.19, not the arbitrary-weight statement of that corollary
or completion of roadmap A.
-/

noncomputable section

namespace Categorification

section ScalarCorner

variable {k A M : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [IsSimpleModule A M]

/-- A nonzero idempotent component on which every sandwich acts by a scalar
detects scalar endomorphisms of a simple module. This is the corner argument
used for the multiplicity-free case of Webster Theorem 2.19, roadmap A. -/
theorem exists_eq_smul_of_scalar_corner (e : A)
    (he : ∃ v : M, v ≠ 0 ∧ e • v = v)
    (hcorner : ∀ a : A, ∃ c : k, ∀ m : M, (e * a * e) • m = c • (e • m))
    (φ : M →ₗ[A] M) : ∃ c : k, ∀ m, φ m = c • m := by
  obtain ⟨v, hv, hev⟩ := he
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hv (φ v)
  change a • v = φ v at ha
  obtain ⟨c, hc⟩ := hcorner a
  have hφv : φ v = c • v := by
    calc
      φ v = e • φ v := by rw [← φ.map_smul, hev]
      _ = (e * a * e) • v := by rw [mul_smul, mul_smul, hev, ha]
      _ = c • v := by rw [hc, hev]
  refine ⟨c, fun m => ?_⟩
  obtain ⟨b, rfl⟩ := IsSimpleModule.toSpanSingleton_surjective A hv m
  change φ (b • v) = c • (b • v)
  rw [map_smul, hφv, smul_comm]

end ScalarCorner

namespace WeightedKLR

open MvPolynomial DirectSum Categorification.Graded

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

namespace ColPerm

omit [DecidableEq I] in
/-- At a multiplicity-free weight every colour-preserving permutation is the identity. -/
theorem eq_one_of_multiplicityFree (hν : ∀ i, ν i ≤ 1) (g : ColPerm ν) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro s
  apply Strand.ext_of (g.2 s)
  have h₁ := (g.1 s).2.isLt
  have h₂ := s.2.isLt
  have h₃ := hν ((g.1 s).1 : I)
  have h₄ := hν (s.1 : I)
  omega

end ColPerm

namespace GalleryAlgebra

/-- Every dot polynomial is colour-symmetric at a multiplicity-free weight. -/
def colourSymOfMultiplicityFree (hν : ∀ i, ν i ≤ 1) (f : PolyRing ν k) : colourSym k ν :=
  ⟨f, fun g hg => by
    have hg' : g ∈ ColPerm ν := fun s => Subtype.ext (congrFun hg s)
    have h := ColPerm.eq_one_of_multiplicityFree hν ⟨g, hg'⟩
    have h' : g = 1 := congrArg Subtype.val h
    simp only [h', Equiv.Perm.coe_one, rename_id, AlgHom.id_apply]⟩

private theorem segGallery_self
    {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (C : FullChamber Γ ν) :
    segGallery (k := k) P C C = e C := by
  have hnil : Segment.word (hypAff (Γ := Γ)) (P C C).1 (P C C).2 = [] := by
    refine List.eq_nil_iff_forall_not_mem.2 fun h hm => ?_
    have hsep := (Segment.mem_word (f := hypAff (Γ := Γ))).1 hm
    have he : Segment.signs (hypAff (Γ := Γ)) (P C C).2 =
        Segment.signs (hypAff (Γ := Γ)) (P C C).1 :=
      (hP C C).2.2.trans (hP C C).2.1.symm
    exact ((Segment.separates_congr_right (f := hypAff (Γ := Γ)) he h).1 hsep) rfl
  rw [segGallery, hnil, galList_nil]

/-- The diagonal chamber corner consists of polynomials in the dots at a
multiplicity-free weight (Webster, arXiv:1209.2463v4, Theorem 2.8). -/
theorem exists_poly_of_multiplicityFree (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (hν : ∀ i, ν i ≤ 1) (C : FullChamber Γ ν)
    (x : cornerSpace k C C) : ∃ f : PolyRing ν k, (x : GalleryAlgebra k Γ ν) = e C * poly f := by
  classical
  let := ColPerm.fintype (ν := ν)
  obtain ⟨P, hP, -⟩ := exists_span_segGallery (k := k) (ν := ν) hD hZ
  let F := cornerPolyEquivOfStanding hP hD hZ hS C C
  obtain ⟨f, rfl⟩ := F.surjective x
  refine ⟨f 1, ?_⟩
  rw [show (F f : GalleryAlgebra k Γ ν) =
    ∑ g, cornerElt P C C g * poly (f g) from
      cornerPolyEquivOfStanding_apply hP hD hZ hS C C f]
  rw [Finset.sum_eq_single 1 (fun g _ hg =>
    (hg (ColPerm.eq_one_of_multiplicityFree hν g)).elim) (by simp)]
  simp only [cornerElt, inv_one, one_smul, r_one, segGallery_self hP,
    e_mul_e, ite_true]

/-- At a multiplicity-free weight a chamber sandwich is a chamber idempotent
times a colour-symmetric polynomial (Webster Theorem 2.8). -/
theorem exists_colourSym_sandwich_of_multiplicityFree (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
    (hS : Γ.Standing) (hν : ∀ i, ν i ≤ 1) {C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (a : WeightedKLRAlgebra k Γ ν) :
    ∃ f : colourSym k ν, rankE k hC * a * rankE k hC = rankE k hC * colourSymHom k Γ ν f := by
  obtain ⟨f, hf⟩ := exists_poly_of_multiplicityFree hD hZ hS hν C
    ⟨e C * a.1 * e C, ⟨a.1, sandwich_apply _ _ _⟩⟩
  change e C * a.1 * e C = e C * poly f at hf
  refine ⟨colourSymOfMultiplicityFree hν f, Subtype.ext ?_⟩
  change e C * a.1 * e C = e C * (poly f * rankIdem k Γ ν)
  rw [hf, ← mul_assoc, e_mul_poly, mul_assoc, e_mul_rankIdem, ite_eq_left hC,
    ← e_mul_poly]

end GalleryAlgebra

namespace GradingDatum

open GalleryAlgebra

variable (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
  {M : Type*} [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]
  {ℳ : ℤ → Submodule k M} [Decomposition ℳ]
  [SetLike.GradedSMul (hS.gradingDatum.klrGrade ν) ℳ]

include hD hZ in
/-- Colour-symmetric dot polynomials act on graded simples through their
augmentation, by KL I arXiv:0803.4121v2, Proposition 2.12's central argument. -/
theorem colourSymHom_smul_eq_aug_of_isGradedSimple
    (hM : IsGradedSimple (hS.gradingDatum.klrGrade ν) ℳ) (f : colourSym k ν) (m : M) :
    colourSymHom k Γ ν f • m = colourSymAug k ν f • m := by
  have hz := colourSymHom_smul_eq_zero_of_isGradedSimple hD hZ hS hM
    (f := f - algebraMap k (colourSym k ν) (colourSymAug k ν f)) (by simp) m
  rw [map_sub, AlgHom.commutes, sub_smul, algebraMap_smul] at hz
  exact sub_eq_zero.1 hz

include hD hZ in
/-- Scalar endomorphisms at multiplicity-free weights, an intermediate case of
Webster arXiv:1209.2463v4, §2.4, Theorem 2.19, roadmap A. The extra hypothesis
`∀ i, ν i ≤ 1` is absent from KL I arXiv:0803.4121v2, §3.2, Corollary 3.19;
this theorem uses Webster Theorem 2.8 and the A0 central augmentation argument
and does not establish the arbitrary-weight weighted assertion. Cycles and all
standing choices of polynomials are allowed. -/
theorem exists_eq_smul_of_isGradedSimple_multiplicityFree (hν : ∀ i, ν i ≤ 1)
    (hM : IsGradedSimple (hS.gradingDatum.klrGrade ν) ℳ)
    (φ : M →ₗ[WeightedKLRAlgebra k Γ ν] M) : ∃ c : k, ∀ m, φ m = c • m := by
  classical
  have := finiteDimensional_of_isGradedSimple hD hZ hS hM
  have := hM.isSimpleModule
  have := hM.nontrivial
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨C, hCv⟩ : ∃ C : RankChamber Γ ν, rankE k C.2 • v ≠ 0 := by
    by_contra h
    have hz : ∀ C : RankChamber Γ ν, rankE k C.2 • v = 0 := by simpa using h
    apply hv
    calc
      v = (1 : WeightedKLRAlgebra k Γ ν) • v := (one_smul _ _).symm
      _ = 0 := by rw [one_eq_sum_rankE, Finset.sum_smul]; simp only [hz, Finset.sum_const_zero]
  apply exists_eq_smul_of_scalar_corner (rankE k C.2) ?_ ?_ φ
  · exact ⟨rankE k C.2 • v, hCv, by rw [← mul_smul, rankE_mul_rankE]⟩
  · intro a
    obtain ⟨f, hf⟩ := exists_colourSym_sandwich_of_multiplicityFree hD hZ hS hν C.2 a
    refine ⟨colourSymAug k ν f, fun m => ?_⟩
    rw [hf, mul_smul, colourSymHom_smul_eq_aug_of_isGradedSimple hD hZ hS hM,
      smul_comm]

end GradingDatum

namespace GradingDatum

variable (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

include hD hZ in
/-- The tensor comparison hypotheses for two multiplicity-free weights.
This is an intermediate case of Webster arXiv:1209.2463v4, §2.4, Theorem 2.19,
roadmap A: A0 supplies all finite-dimensionality fields and the scalar corner
argument supplies the two endomorphism fields. The weights may overlap;
their sum need not be multiplicity-free. This does not discharge the comparison
hypothesis at arbitrary weights. -/
theorem tensorK0Hyp_multiplicityFree {μ : I →₀ ℕ}
    (hν : ∀ i, ν i ≤ 1) (hμ : ∀ i, μ i ≤ 1) :
    TensorK0Hyp (hS.gradingDatum.klrGrade ν) (hS.gradingDatum.klrGrade μ) where
  fdA b := finiteDimensional_top hD hZ hS b
  fdB b := finiteDimensional_top hD hZ hS b
  endA b φ := by
    obtain ⟨c, hc⟩ := exists_eq_smul_of_isGradedSimple_multiplicityFree hD hZ hS hν
      (GProj.IndecClass.isGradedSimple_top b) φ
    exact ⟨c, LinearMap.ext hc⟩
  endB b φ := by
    obtain ⟨c, hc⟩ := exists_eq_smul_of_isGradedSimple_multiplicityFree hD hZ hS hμ
      (GProj.IndecClass.isGradedSimple_top b) φ
    exact ⟨c, LinearMap.ext hc⟩
  fdC b := finiteDimensional_top_tensor hD hZ hS b

end GradingDatum

end WeightedKLR
end Categorification
