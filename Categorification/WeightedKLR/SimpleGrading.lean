/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.SimpleDots

/-!
# Admissible gradings of weighted KLR algebras

Supporting the graded tensor comparison in Webster, *Weighted
Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4, Theorem 2.19.
The locally finite, bounded-below condition `HasGdim` forces every dot degree
to be positive: negative degrees contradict the lower bound, and degree zero
would contain infinitely many independent polynomial powers. Consequently the
augmentation argument of Khovanov–Lauda I, arXiv:0803.4121v2, §2.5,
Proposition 2.12 applies to every such grading datum, including the arbitrary
grading datum in the graded Mackey formula.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.WeightedKLR

open MvPolynomial DirectSum Categorification.Graded GalleryAlgebra

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [Field k] {Γ : WeightedGraph I 𝕜 k}
  {ν : I →₀ ℕ}

namespace GradingDatum

private def polynomialCorner : PolyRing ν k →ₗ[k] WeightedKLRAlgebra k Γ ν :=
  (colourSymCornerProjection (k := k) (Γ := Γ) (ν := ν)).restrictScalars k |>.comp
    (polyHom k Γ ν).toLinearMap

private theorem e_mul_polynomialCorner_val (C : FullChamber Γ ν)
    (hC : C.IsRankOrdered) (f : PolyRing ν k) :
    e C * (polynomialCorner (Γ := Γ) f).1 = poly f * e C := by
  change e C * (rankIdem k Γ ν * poly f * rankIdem k Γ ν) = _
  rw [← mul_assoc, ← mul_assoc, e_mul_rankIdem, ite_eq_left hC, e_mul_poly,
    mul_assoc, e_mul_rankIdem, ite_eq_left hC]

private theorem polynomialCorner_injective (hS : Γ.Standing) :
    Function.Injective (polynomialCorner (k := k) (Γ := Γ) (ν := ν)) := by
  have hc : Nonempty (Chamber Γ ν) := by
    have C := KLR.Seq.spacedChamber Γ (Classical.arbitrary (KLR.Seq ν.toMultiset))
    exact ⟨by simpa using C⟩
  let C := (Classical.choice hc).toFull
  have hC : C.IsRankOrdered := (Classical.choice hc).toFull_isRankOrdered
  intro f g h
  have he := congrArg (fun a : WeightedKLRAlgebra k Γ ν => e C * a.1) h
  rw [e_mul_polynomialCorner_val C hC, e_mul_polynomialCorner_val C hC] at he
  have hv := congrArg (fun a : GalleryAlgebra k Γ ν =>
    galleryRep k hS.psymm a (Pi.single C 1) C) he
  simpa [map_mul, Module.End.mul_apply, galleryRep_poly, galleryRep_e,
    diagOp_apply, blk_apply] using hv

private theorem polynomialCorner_mem_grade (G : GradingDatum Γ)
    {f : PolyRing ν k} {d : ℤ} (hf : f.IsWeightedHomogeneous G.wt d) :
    polynomialCorner (Γ := Γ) f ∈ G.klrGrade ν d := by
  change rankIdem k Γ ν * poly f * rankIdem k Γ ν ∈ G.grade ν d
  simpa only [zero_add, add_zero] using
    SetLike.mul_mem_graded (SetLike.mul_mem_graded (rankIdem_mem_grade G ν)
      (G.poly_mem_grade hf)) (rankIdem_mem_grade G ν)

/-- Local finiteness and a lower degree bound force positive dot degrees.
This supporting observation lets the KL I Proposition 2.12 argument apply to
the arbitrary grading datum in Webster's graded Mackey formula (Theorem 2.19). -/
theorem wt_pos_of_hasGdim (G : GradingDatum Γ) (hS : Γ.Standing)
    [HasGdim (G.klrGrade ν)] (s : Strand ν) : 0 < G.wt s := by
  classical
  have hLI : LinearIndependent k (fun n : ℕ =>
      polynomialCorner (Γ := Γ) (monomial (Finsupp.single s n) 1)) :=
    ((basisMonomials (Strand ν) k).linearIndependent.comp
      (fun n : ℕ => Finsupp.single s n)
      (fun n m h => by simpa using congrArg (fun u : Strand ν →₀ ℕ => u s) h)).map'
        _ (LinearMap.ker_eq_bot.mpr (polynomialCorner_injective hS))
  have hmem (n : ℕ) : polynomialCorner (Γ := Γ) (monomial (Finsupp.single s n) 1) ∈
      G.klrGrade ν (n • G.wt s) := by
    apply polynomialCorner_mem_grade G
    simpa [Finsupp.weight_single] using
      isWeightedHomogeneous_monomial G.wt (Finsupp.single s n) (1 : k) rfl
  by_contra hpos
  have hle : G.wt s ≤ 0 := le_of_not_gt hpos
  by_cases hz : G.wt s = 0
  · let v : ℕ → G.klrGrade ν 0 := fun n => ⟨_, by simpa [hz] using hmem n⟩
    have hv : LinearIndependent k v := LinearIndependent.of_comp
      (G.klrGrade ν 0).subtype hLI
    exact Module.Finite.not_linearIndependent_of_infinite v hv
  · have hneg : G.wt s < 0 := lt_of_le_of_ne hle hz
    obtain ⟨N, hN⟩ := HasGdim.bddBelow (ℳ := G.klrGrade ν)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) * G.wt s < N := by
      refine ⟨N.natAbs + 1, ?_⟩
      have hNabs := neg_abs_le N
      have hw : G.wt s ≤ -1 := by omega
      simp only [Nat.cast_add, Nat.cast_one, Int.natCast_natAbs]
      nlinarith [mul_nonneg (abs_nonneg N) (show 0 ≤ -1 - G.wt s by omega)]
    have hne : G.klrGrade ν (n • G.wt s) ≠ ⊥ := by
      intro he
      have hm := hmem n
      rw [he, Submodule.mem_bot] at hm
      exact hLI.ne_zero n hm
    have := hN hne
    rw [nsmul_eq_mul] at this
    omega

section Simple

variable (G : GradingDatum Γ) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
  [HasGdim (G.klrGrade ν)]
  {M : Type*} [AddCommGroup M] [Module k M]
  [Module (WeightedKLRAlgebra k Γ ν) M] [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M]
  {ℳ : ℤ → Submodule k M} [Decomposition ℳ]
  [SetLike.GradedSMul (G.klrGrade ν) ℳ]

include hS

omit [IsScalarTower k (WeightedKLRAlgebra k Γ ν) M] in
/-- The colour-symmetric augmentation annihilates graded simples for every
locally finite grading bounded below, by KL I, Proposition 2.12. -/
theorem colourSymHom_smul_eq_zero_of_isGradedSimple_of_hasGdim
    (hM : IsGradedSimple (G.klrGrade ν) ℳ) {f : colourSym k ν}
    (hf : colourSymAug k ν f = 0) (m : M) : colourSymHom k Γ ν f • m = 0 := by
  obtain ⟨N, hN⟩ := HasGdim.bddBelow (ℳ := G.klrGrade ν)
  have hbound : ∀ n < N, G.klrGrade ν n = ⊥ := by
    intro n hn
    by_contra h
    exact (not_le_of_gt hn) (hN h)
  exact hM.smul_eq_zero_of_commute hbound (fun a => Algebra.commutes f a)
    (fun _ hd => G.decompose_colourSymHom_eq_zero (G.wt_pos_of_hasGdim hS) hf hd) m

include hD hZ in
/-- The KL I Proposition 2.12 augmentation argument gives finite-dimensional
graded simples for every locally finite grading bounded below (Theorem 2.19, A0). -/
theorem finiteDimensional_of_isGradedSimple_of_hasGdim
    (hM : IsGradedSimple (G.klrGrade ν) ℳ) : FiniteDimensional k M := by
  have := GalleryAlgebra.finiteDimensional_quotient_colourSymAug (ν := ν) hD hZ hS
  apply hM.finiteDimensional (augSubmodule (WeightedKLRAlgebra k Γ ν) (colourSymAug k ν))
  intro a ha m
  refine augSubmodule_induction (p := fun a : WeightedKLRAlgebra k Γ ν => a • m = 0)
    ha (fun f hf a => ?_)
    (fun a b ha hb => by rw [add_smul, ha, hb, add_zero])
  rw [Algebra.smul_def, mul_smul]
  exact G.colourSymHom_smul_eq_zero_of_isGradedSimple_of_hasGdim hS hM hf (a • m)

include hD hZ in
/-- Dots act nilpotently on graded simples for every locally finite grading
bounded below, by KL I Proposition 2.12 and positivity forced by `HasGdim`. -/
theorem smulNilpotent_reducedDot_of_isGradedSimple_of_hasGdim
    (hM : IsGradedSimple (G.klrGrade ν) ℳ) (s : Strand ν) :
    KLR.SmulNilpotent (reducedDot k Γ ν s) M := by
  have := G.finiteDimensional_of_isGradedSimple_of_hasGdim hD hZ hS hM
  exact G.smulNilpotent_reducedDot_of_graded (ℳ := ℳ) s (G.wt_pos_of_hasGdim hS s)

end Simple

section Tensor

open scoped TensorProduct

variable (G : GradingDatum Γ) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
  {μ : I →₀ ℕ} [HasGdim (G.klrGrade ν)] [HasGdim (G.klrGrade μ)]
  {U : Type*} [AddCommGroup U] [Module k U]
  [Module (WeightedKLRAlgebra k Γ ν ⊗[k] WeightedKLRAlgebra k Γ μ) U]
  [IsScalarTower k (WeightedKLRAlgebra k Γ ν ⊗[k] WeightedKLRAlgebra k Γ μ) U]
  {𝒰 : ℤ → Submodule k U} [Decomposition 𝒰]
  [SetLike.GradedSMul (tensorGrading (G.klrGrade ν) (G.klrGrade μ)) 𝒰]

include hS

include hD hZ in
/-- The tensor augmentation argument gives finite-dimensional graded simples
for arbitrary locally finite gradings bounded below (Theorem 2.19, A0). -/
theorem finiteDimensional_of_isGradedSimple_tensor_of_hasGdim
    (hU : IsGradedSimple (tensorGrading (G.klrGrade ν) (G.klrGrade μ)) 𝒰) :
    FiniteDimensional k U := by
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
      (fun d hd => G.decompose_colourSymHom_eq_zero (G.wt_pos_of_hasGdim hS) hf hd) _
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
      (fun d hd => G.decompose_colourSymHom_eq_zero (G.wt_pos_of_hasGdim hS) hf hd) _

end Tensor

/-- Finite-dimensional simple tops for every locally finite grading bounded
below, providing the factor finite-dimensionality in `TensorK0Hyp`. -/
theorem finiteDimensional_top_of_hasGdim (G : GradingDatum Γ)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    [HasGdim (G.klrGrade ν)] (b : GProj.IndecClass (G.klrGrade ν)) :
    FiniteDimensional k b.top :=
  G.finiteDimensional_of_isGradedSimple_of_hasGdim hD hZ hS
    (GProj.IndecClass.isGradedSimple_top b)

/-- Finite-dimensional tensor simple tops for every locally finite grading
bounded below, providing `fdC` in `TensorK0Hyp`. -/
theorem finiteDimensional_top_tensor_of_hasGdim (G : GradingDatum Γ)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hS : Γ.Standing)
    {μ : I →₀ ℕ} [HasGdim (G.klrGrade ν)] [HasGdim (G.klrGrade μ)]
    (c : GProj.IndecClass (tensorGrading (G.klrGrade ν) (G.klrGrade μ))) :
    FiniteDimensional k c.top :=
  G.finiteDimensional_of_isGradedSimple_tensor_of_hasGdim hD hZ hS
    (GProj.IndecClass.isGradedSimple_top c)

end GradingDatum

end Categorification.WeightedKLR
