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

private theorem exists_iso_regular_shift (P : GProj 𝒜)
    (hP : P.IsIndec A) : ∃ a : ℤ, Nonempty (P.Iso ((GProj.regular 𝒜).shift a)) := by
  let := hP.nontrivial
  obtain ⟨a, x, hx, hx0⟩ := exists_mem_ne_zero P.grading
  let s : P.grading a := ⟨x, hx⟩
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k (x := s)
    (fun h => hx0 (congrArg Subtype.val h))
  let π : P.carrier →ₗ[k] P.grading a :=
    DirectSum.component k ℤ (fun d => P.grading d) a ∘ₗ (DirectSum.decomposeLinearEquiv P.grading).toLinearMap
  let p : P.carrier →ₗ[k] P.carrier := (f ∘ₗ π).smulRight x
  have hp (y : P.carrier) : p y = f (DirectSum.decompose P.grading y a) • x := rfl
  have hpx : p x = x := by
    rw [hp, DirectSum.decompose_of_mem P.grading hx, DirectSum.of_eq_same]
    exact (congrArg (fun c : k => c • x) hf).trans (one_smul k x)
  let pA : P.carrier →ₗ[A] P.carrier :=
    { p.toAddHom with
      map_smul' := fun b y => by
        obtain ⟨c, rfl⟩ := e.surjective b
        change p (e c • y) = e c • p y
        rw [scalarEquiv_apply e, algebraMap_smul, algebraMap_smul, map_smul] }
  have hgp : PreservesGrading P.grading P.grading pA := by
    intro d y hy
    change p y ∈ P.grading d
    by_cases h : d = a
    · subst d
      rw [hp]
      exact Submodule.smul_mem _ _ hx
    · have hdecomp : DirectSum.decompose P.grading y a = 0 :=
        Subtype.ext (DirectSum.decompose_of_mem_ne P.grading hy h)
      rw [hp, hdecomp, map_zero, zero_smul]
      exact zero_mem _
  have hi : IsIdempotentElem pA := by
    apply LinearMap.ext
    intro y
    change p (p y) = p y
    conv_lhs => rw [hp y, map_smul, hpx]
    rfl
  have hp1 : pA = 1 := (hP.eq_zero_or_eq_one pA hgp hi).resolve_left fun h =>
    hx0 (hpx.symm.trans (LinearMap.congr_fun h x))
  let F : A →ₗ[A] P.carrier := LinearMap.toSpanSingleton A P.carrier x
  have hF : Function.Bijective F := by
    constructor
    · intro b b' h
      obtain ⟨c, rfl⟩ := e.surjective b
      obtain ⟨c', rfl⟩ := e.surjective b'
      have hcc : c • x = c' • x := by
        simpa only [F, LinearMap.toSpanSingleton_apply, scalarEquiv_apply e,
          algebraMap_smul] using h
      exact congrArg e ((smul_left_injective k hx0) hcc)
    · intro y
      refine ⟨e (f (DirectSum.decompose P.grading y a)), ?_⟩
      change e _ • x = y
      rw [scalarEquiv_apply e, algebraMap_smul]
      exact (hp y).symm.trans (LinearMap.congr_fun hp1 y)
  have hFgr : PreservesGrading (shift 𝒜 a) P.grading F :=
    fun d b hb => by
      let : SetLike.GradedSMul 𝒜 P.grading := P.gradedSMul
      have ht : b • x ∈ P.grading (d - a + a) := SetLike.GradedSMul.smul_mem (mem_shift.1 hb) hx
      change b • x ∈ P.grading d
      simpa only [sub_add_cancel] using ht
  exact ⟨a, ⟨(GradedEquiv.ofPreserves (LinearEquiv.ofBijective F hF) hFgr).symm⟩⟩

/-- At weight zero the class of the regular projective freely generates the
Grothendieck group over the Laurent-polynomial scalars. -/
def scalarK0Equiv : K0 𝒜 ≃ₗ[R] R := by
  letI := hasGdim_scalarGrade 𝒜 e
  let b := K0.indecBasis 𝒜
  let f : R →ₗ[R] K0 𝒜 := LinearMap.toSpanSingleton R _ (K0.of (GProj.regular 𝒜))
  have hgen : ∀ i, b i ∈ LinearMap.range f := fun i => by
    obtain ⟨a, ⟨e⟩⟩ := exists_iso_regular_shift 𝒜 e i.rep i.isIndec_rep
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
    obtain ⟨i, a, ⟨e⟩⟩ := GProj.IndecClass.exists_iso_rep_shift (regular_isIndec_of_scalar 𝒜 e)
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

@[simp] theorem scalarK0Equiv_symm_apply (p : R) : (scalarK0Equiv 𝒜 e).symm p = p • (K0.of (GProj.regular 𝒜)) :=
  rfl

end Categorification.Graded
