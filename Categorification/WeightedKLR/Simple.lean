/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.CentralFinite
import Categorification.WeightedKLR.GradedK0.Grading
import Categorification.Algebra.Graded.TensorSimpleFinite
import Categorification.Algebra.Graded.KrullSchmidt

/-!
# Finite-dimensional graded simple weighted KLR modules

Theorem 2.19, roadmap A0, of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, §2.4. We apply the argument of Khovanov–Lauda I,
arXiv:0803.4121v2, Proposition 2.12: positive-degree central colour-symmetric dot
polynomials annihilate graded simples, which factor through a finite-dimensional
augmentation quotient. This provides only the finite-dimensionality inputs for
the graded tensor comparison, with no assertion of absolute irreducibility.
-/

noncomputable section

namespace Categorification.WeightedKLR

open MvPolynomial DirectSum Categorification.Graded

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

namespace GradingDatum

omit [DecidableEq I] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A nonconstant dot monomial has positive degree when every dot does. This is the
positivity step of the adaptation of KL I, Proposition 2.12, in roadmap A0. -/
theorem weight_pos (G : GradingDatum Γ) (hG : ∀ s : Strand ν, 0 < G.wt s)
    {u : Strand ν →₀ ℕ} (hu : u ≠ 0) : 0 < Finsupp.weight G.wt u := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_pos (fun s hs => smul_pos
    (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hs)) (hG s))
    (Finsupp.support_nonempty_iff.2 hu)

/-- Dot polynomials with zero constant coefficient have no nonpositive homogeneous
components when all dot degrees are positive (KL I, Proposition 2.12 argument). -/
theorem decompose_poly_eq_zero (G : GradingDatum Γ) (hG : ∀ s : Strand ν, 0 < G.wt s)
    {f : PolyRing ν k} (hf : constantCoeff f = 0) {d : ℤ} (hd : d ≤ 0) :
    (decompose (G.grade ν) (GalleryAlgebra.poly f) d : GalleryAlgebra k Γ ν) = 0 := by
  classical
  rw [show GalleryAlgebra.poly f = GalleryAlgebra.polyHom k Γ ν f from rfl,
    f.as_sum, map_sum, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Finset.sum_eq_zero fun u hu => ?_
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [MvPolynomial.mem_support_iff, ← constantCoeff_eq, hf] at hu
    exact hu rfl
  exact decompose_of_mem_ne _ (G.poly_monomial_mem_grade u (f.coeff u))
    (by have := G.weight_pos hG hu0; omega)

open GalleryAlgebra

/-- The positive augmentation ideal remains positively supported on passing to
Webster's degree-zero corner (roadmap A0, KL I Proposition 2.12 argument). -/
theorem decompose_colourSymHom_eq_zero (G : GradingDatum Γ)
    (hG : ∀ s : Strand ν, 0 < G.wt s) {f : colourSym k ν}
    (hf : colourSymAug k ν f = 0) {d : ℤ} (hd : d ≤ 0) :
    (decompose (G.klrGrade ν) (colourSymHom k Γ ν f) d : WeightedKLRAlgebra k Γ ν) = 0 := by
  let L : WeightedKLRAlgebra k Γ ν →ₗ[k] GalleryAlgebra k Γ ν :=
    IsIdempotentElem.cornerVal (R := k) isIdempotentElem_rankIdem
  have hL : PreservesGrading (G.klrGrade ν) (G.grade ν) L := fun _ _ hx => hx
  have hpos : (decompose (G.grade ν) (L (colourSymHom k Γ ν f)) d :
      GalleryAlgebra k Γ ν) = 0 := by
    have hval : L (colourSymHom k Γ ν f) =
        poly (f : PolyRing ν k) * rankIdem k Γ ν := colourSymHom_val f
    rw [hval, coe_decompose_mul_of_right_mem_zero _ (rankIdem_mem_grade G ν),
      G.decompose_poly_eq_zero hG (by simpa using hf) hd, zero_mul]
  exact (show Function.Injective L from fun _ _ h => Subtype.ext h)
    ((decompose_map hL (colourSymHom k Γ ν f) d).symm.trans
      (hpos.trans (map_zero L).symm))

variable (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)

section Simple

variable {M : Type*} [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]
  {ℳ : ℤ → Submodule k M} [Decomposition ℳ]
  [SetLike.GradedSMul (hS.gradingDatum.klrGrade ν) ℳ]

omit [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M] in
include hD hZ in
/-- The colour-symmetric augmentation ideal acts by zero on graded simples,
by the argument of KL I, arXiv:0803.4121v2, §2.5, Proposition 2.12, applied
to Webster's algebra (arXiv:1209.2463v4, §2.4, Theorem 2.19, A0). -/
theorem colourSymHom_smul_eq_zero_of_isGradedSimple
    (hM : IsGradedSimple (hS.gradingDatum.klrGrade ν) ℳ) {f : colourSym k ν}
    (hf : colourSymAug k ν f = 0) (m : M) : colourSymHom k Γ ν f • m = 0 := by
  have := GalleryAlgebra.hasGdim_klrGrade (ν := ν) hD hZ hS
  obtain ⟨N, hN⟩ := HasGdim.bddBelow (ℳ := hS.gradingDatum.klrGrade ν)
  have hbound : ∀ n < N, hS.gradingDatum.klrGrade ν n = ⊥ := by
    intro n hn
    by_contra h
    exact (not_le_of_gt hn) (hN h)
  exact hM.smul_eq_zero_of_commute hbound
    (fun a => Algebra.commutes f a)
    (fun _ hd => hS.gradingDatum.decompose_colourSymHom_eq_zero
      (WeightedGraph.Standing.wt_pos hS) hf hd) m

include hD hZ in
/-- Every graded simple weighted KLR module is finite-dimensional. This is A0 for
Webster arXiv:1209.2463v4, §2.4, Theorem 2.19, by the finite augmentation quotient
argument of KL I arXiv:0803.4121v2, §2.5, Proposition 2.12. -/
theorem finiteDimensional_of_isGradedSimple
    (hM : IsGradedSimple (hS.gradingDatum.klrGrade ν) ℳ) : FiniteDimensional k M := by
  have := GalleryAlgebra.finiteDimensional_quotient_colourSymAug (ν := ν) hD hZ hS
  apply hM.finiteDimensional (augSubmodule (WeightedKLRAlgebra k Γ ν) (colourSymAug k ν))
  intro a ha m
  refine augSubmodule_induction (p := fun a : WeightedKLRAlgebra k Γ ν => a • m = 0)
    ha (fun f hf a => ?_)
    (fun a b ha hb => by rw [add_smul, ha, hb, add_zero])
  rw [Algebra.smul_def, mul_smul]
  exact colourSymHom_smul_eq_zero_of_isGradedSimple hD hZ hS hM hf (a • m)

end Simple

section Tensor

open scoped TensorProduct

variable {μ : I →₀ ℕ} {U : Type*} [AddCommGroup U] [Module k U]
  [Module (WeightedKLRAlgebra k Γ ν ⊗[k] WeightedKLRAlgebra k Γ μ) U]
  [IsScalarTower k (WeightedKLRAlgebra k Γ ν ⊗[k] WeightedKLRAlgebra k Γ μ) U]
  {𝒰 : ℤ → Submodule k U} [Decomposition 𝒰]
  [SetLike.GradedSMul
    (tensorGrading (hS.gradingDatum.klrGrade ν) (hS.gradingDatum.klrGrade μ)) 𝒰]

include hD hZ in
/-- Every graded simple module over a tensor product of two weighted KLR algebras
is finite-dimensional. This is the tensor finite-dimensionality input A0 for
Webster arXiv:1209.2463v4, §2.4, Theorem 2.19, by the argument of
KL I arXiv:0803.4121v2, §2.5, Proposition 2.12
applied to the augmentation ideals in the two factors. -/
theorem finiteDimensional_of_isGradedSimple_tensor
    (hU : IsGradedSimple
      (tensorGrading (hS.gradingDatum.klrGrade ν) (hS.gradingDatum.klrGrade μ)) 𝒰) :
    FiniteDimensional k U := by
  have := GalleryAlgebra.hasGdim_klrGrade (ν := ν) hD hZ hS
  have := GalleryAlgebra.hasGdim_klrGrade (ν := μ) hD hZ hS
  have := GalleryAlgebra.finiteDimensional_quotient_colourSymAug (ν := ν) hD hZ hS
  have := GalleryAlgebra.finiteDimensional_quotient_colourSymAug (ν := μ) hD hZ hS
  apply hU.finiteDimensional_tensor_of_quotients
    (augSubmodule (WeightedKLRAlgebra k Γ ν) (colourSymAug k ν))
    (augSubmodule (WeightedKLRAlgebra k Γ μ) (colourSymAug k μ))
  · intro a ha b u
    refine augSubmodule_induction
      (p := fun a : WeightedKLRAlgebra k Γ ν => (a ⊗ₜ[k] b) • u = 0)
      ha (fun f hf a => ?_)
      (fun a a' ha ha' => by rw [TensorProduct.add_tmul, add_smul, ha, ha', add_zero])
    rw [Algebra.smul_def,
      show (algebraMap (colourSym k ν) (WeightedKLRAlgebra k Γ ν) f * a) ⊗ₜ[k] b =
          (colourSymHom k Γ ν f ⊗ₜ[k] (1 : WeightedKLRAlgebra k Γ μ)) * (a ⊗ₜ[k] b) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl,
      mul_smul]
    exact hU.tmul_one_smul_eq_zero_of_commute (fun a => Algebra.commutes f a)
      (fun d hd => hS.gradingDatum.decompose_colourSymHom_eq_zero
        (WeightedGraph.Standing.wt_pos hS) hf hd) _
  · intro b hb a u
    refine augSubmodule_induction
      (p := fun b : WeightedKLRAlgebra k Γ μ => (a ⊗ₜ[k] b) • u = 0)
      hb (fun f hf b => ?_)
      (fun b b' hb hb' => by rw [TensorProduct.tmul_add, add_smul, hb, hb', add_zero])
    rw [Algebra.smul_def,
      show a ⊗ₜ[k] (algebraMap (colourSym k μ) (WeightedKLRAlgebra k Γ μ) f * b) =
          ((1 : WeightedKLRAlgebra k Γ ν) ⊗ₜ[k] colourSymHom k Γ μ f) * (a ⊗ₜ[k] b) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl,
      mul_smul]
    exact hU.one_tmul_smul_eq_zero_of_commute (fun b => Algebra.commutes f b)
      (fun d hd => hS.gradingDatum.decompose_colourSymHom_eq_zero
        (WeightedGraph.Standing.wt_pos hS) hf hd) _

end Tensor

include hD hZ in
/-- Finite-dimensionality of each graded simple top of `W_ν`, supplying either
factor field `fdA` or `fdB` in `TensorK0Hyp` (Webster Theorem 2.19, roadmap A0). -/
theorem finiteDimensional_top (b : GProj.IndecClass (hS.gradingDatum.klrGrade ν)) :
    FiniteDimensional k b.top :=
  finiteDimensional_of_isGradedSimple hD hZ hS (GProj.IndecClass.isGradedSimple_top b)

include hD hZ in
/-- Finite-dimensionality of the graded simple tops of `W_ν ⊗ W_μ`, supplying
`fdC` in `TensorK0Hyp` (Webster Theorem 2.19, roadmap A0). -/
theorem finiteDimensional_top_tensor {μ : I →₀ ℕ}
    (c : GProj.IndecClass
      (tensorGrading (hS.gradingDatum.klrGrade ν) (hS.gradingDatum.klrGrade μ))) :
    FiniteDimensional k c.top :=
  finiteDimensional_of_isGradedSimple_tensor hD hZ hS (GProj.IndecClass.isGradedSimple_top c)

end GradingDatum

end Categorification.WeightedKLR
