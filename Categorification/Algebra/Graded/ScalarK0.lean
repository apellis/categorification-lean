/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.KrullSchmidt
import Categorification.Algebra.Graded.Tensor

/-!
# The Grothendieck group of a graded scalar algebra

The vacuum block in Webster, arXiv:1209.2463v4, proof of Theorem 2.19, and in
arXiv:1309.3796v2, proof of Lemma 4.36, is the scalar field. Its regular
projective freely generates its graded Grothendieck group.
-/

noncomputable section

namespace Categorification.Graded

open Module

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] (e : k ≃ₐ[k] A)

local notation "R" => LaurentPolynomial ℤ

private theorem scalarEquiv_apply (c : k) : e c = algebraMap k A c := e.commutes c

include e

theorem mem_scalarGrade (a : A) : a ∈ 𝒜 0 := by
  obtain ⟨c, rfl⟩ := e.surjective a
  rw [scalarEquiv_apply e, Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem

private theorem hasGdim_scalarGrade : HasGdim 𝒜 := by
  let : FiniteDimensional k A := FiniteDimensional.of_surjective e.toLinearEquiv.toLinearMap e.surjective
  refine ⟨fun d => inferInstance, ⟨0, fun d hd => ?_⟩⟩
  by_contra h
  have hn : d ≠ 0 := by omega
  apply hd
  rw [Submodule.eq_bot_iff]
  exact fun a ha => by
    by_contra ha0
    exact hn (DirectSum.degree_eq_of_mem_mem 𝒜 ha
      (mem_scalarGrade 𝒜 e a) ha0)

private theorem regular_isIndec_of_scalar : (GProj.regular 𝒜).IsIndec A := by
  refine ⟨e.injective.nontrivial, ?_⟩
  change ∀ f : Module.End A A, f ∈ endZero A 𝒜 → IsIdempotentElem f → f = 0 ∨ f = 1
  intro f _ hf
  have he : IsIdempotentElem (e.symm (f (1 : A))) :=
    ((LinearMap.isIdempotentElem_map_one_iff (f := f)).2 hf).map e.symm
  have h : f (1 : A) = 0 ∨ f (1 : A) = 1 := by
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with h | h
    · exact Or.inl (e.symm.injective (h.trans (map_zero _).symm))
    · exact Or.inr (e.symm.injective (h.trans (map_one _).symm))
  have hf_apply (a : A) : f a = a • f (1 : A) := by
    rw [← f.map_smul]
    simp
  rcases h with h | h
  · exact Or.inl (LinearMap.ext fun a => by simp [hf_apply a, h])
  · exact Or.inr (LinearMap.ext fun a => by simp [hf_apply a, h])

omit e in
private theorem exists_iso_regular_shift [HasGdim 𝒜]
    (hreg : (GProj.regular 𝒜).IsIndec A) (P : GProj 𝒜) (hP : P.IsIndec A) :
    ∃ a : ℤ, Nonempty (P.Iso ((GProj.regular 𝒜).shift a)) := by
  let := hP.nontrivial
  obtain ⟨S, f, hS, hf, hf0, _⟩ := P.exists_isGradedSimple_quotient
  let := hS.nontrivial
  let := S.gradedSMul
  obtain ⟨a, v, hv, hv0⟩ := exists_mem_ne_zero S.grading
  let g := LinearMap.toSpanSingleton A S.carrier v
  have hg : PreservesGrading (Graded.shift 𝒜 a) S.grading g := by
    intro d b hb
    have h : b • v ∈ S.grading (d - a + a) :=
      SetLike.GradedSMul.smul_mem (mem_shift.1 hb) hv
    simpa only [g, LinearMap.toSpanSingleton_apply, sub_add_cancel] using h
  have hg0 : g ≠ 0 := fun h => hv0 (by simpa [g] using LinearMap.congr_fun h 1)
  exact ⟨a, hP.nonempty_iso (hreg.shift a) hS hf hf0 hg hg0⟩

omit e in
/-- If the graded regular module is indecomposable, its class is a basis of graded
projective `K₀`. Every simple quotient of an indecomposable projective also admits
a quotient map from a shift of the regular module. -/
def regularK0Equiv [HasGdim 𝒜] (hreg : (GProj.regular 𝒜).IsIndec A) :
    K0 𝒜 ≃ₗ[R] R := by
  let b := K0.indecBasis 𝒜
  let f : R →ₗ[R] K0 𝒜 := LinearMap.toSpanSingleton R _ (K0.of (GProj.regular 𝒜))
  have hgen : ∀ i, b i ∈ LinearMap.range f := fun i => by
    obtain ⟨a, ⟨e⟩⟩ := exists_iso_regular_shift 𝒜 hreg i.rep i.isIndec_rep
    exact ⟨LaurentPolynomial.T a, by
      change (LaurentPolynomial.T a : R) • (K0.of (GProj.regular 𝒜)) = b i
      rw [K0.T_smul_of, show b i = K0.of i.rep from K0.indecBasis_apply i]
      exact (K0.of_eq_of_iso e).symm⟩
  have hsurj : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have hinj : Function.Injective f := by
    obtain ⟨i, a, ⟨e⟩⟩ := GProj.IndecClass.exists_iso_rep_shift hreg
    have he : (K0.of (GProj.regular 𝒜)) = (LaurentPolynomial.T a : R) • b i := by
      rw [K0.indecBasis_apply, K0.T_smul_of]
      exact K0.of_eq_of_iso e
    intro p q hpq
    change p • (K0.of (GProj.regular 𝒜)) = q • (K0.of (GProj.regular 𝒜)) at hpq
    rw [he, smul_smul, smul_smul] at hpq
    have h := congrArg (fun x => b.repr x i) hpq
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h
    exact (LaurentPolynomial.isUnit_T a).mul_left_inj.mp h
  exact (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm

omit e in
@[simp] theorem regularK0Equiv_symm_apply [HasGdim 𝒜] (hreg : (GProj.regular 𝒜).IsIndec A)
    (p : R) : (regularK0Equiv 𝒜 hreg).symm p = p • K0.of (GProj.regular 𝒜) := rfl

/-- At weight zero the class of the regular projective freely generates the
Grothendieck group over the Laurent-polynomial scalars. -/
def scalarK0Equiv : K0 𝒜 ≃ₗ[R] R := by
  letI := hasGdim_scalarGrade 𝒜 e
  exact regularK0Equiv 𝒜 (regular_isIndec_of_scalar 𝒜 e)

@[simp] theorem scalarK0Equiv_symm_apply (p : R) : (scalarK0Equiv 𝒜 e).symm p = p • (K0.of (GProj.regular 𝒜)) :=
  rfl

end Categorification.Graded
