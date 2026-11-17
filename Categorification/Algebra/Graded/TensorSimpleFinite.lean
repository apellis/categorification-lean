/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Simple
import Categorification.Algebra.Graded.TensorGdim

/-!
# Finite-dimensional graded simple modules over tensor products

The tensor form of the positive central augmentation argument used in
Khovanov–Lauda I, arXiv:0803.4121v2, Proposition 2.12. These supporting lemmas
are needed for roadmap A0 of Webster, arXiv:1209.2463v4, Theorem 2.19:
central positive elements in either tensor factor annihilate graded simples;
finite-dimensional quotient spaces in both factors then imply finiteness of
the simple tensor module. No classification or absolute irreducibility is used.
-/

noncomputable section

namespace Categorification.Graded

open DirectSum
open scoped TensorProduct

section Tensor

variable {k A B U : Type*} [Field k] [Ring A] [Algebra k A] [Ring B] [Algebra k B]
  {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ]
  [AddCommGroup U] [Module k U] [Module (A ⊗[k] B) U]
  [IsScalarTower k (A ⊗[k] B) U] {𝒰 : ℤ → Submodule k U}
  [Decomposition 𝒰] [SetLike.GradedSMul (tensorGrading 𝒜 ℬ) 𝒰]

omit [IsScalarTower k (A ⊗[k] B) U] in
/-- The left-factor version of positive central annihilation, used in the tensor
augmentation quotient argument of roadmap A0 (KL I, Proposition 2.12 argument). -/
theorem IsGradedSimple.tmul_one_smul_eq_zero_of_commute
    (hU : IsGradedSimple (tensorGrading 𝒜 ℬ) 𝒰) {z : A}
    (hz : ∀ a : A, Commute z a)
    (hpos : ∀ d ≤ 0, (decompose 𝒜 z d : A) = 0) (u : U) :
    (z ⊗ₜ[k] (1 : B)) • u = 0 := by
  obtain ⟨N, hN⟩ := HasGdim.bddBelow (ℳ := tensorGrading 𝒜 ℬ)
  have hbound : ∀ n < N, tensorGrading 𝒜 ℬ n = ⊥ := by
    intro n hn
    by_contra h
    exact (not_le_of_gt hn) (hN h)
  have hc : ∀ t : A ⊗[k] B, Commute (z ⊗ₜ[k] 1) t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      show (z ⊗ₜ[k] (1 : B)) * (a ⊗ₜ[k] b) = (a ⊗ₜ[k] b) * (z ⊗ₜ[k] 1)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, (hz a).eq]
    | add s t hs ht => exact hs.add_right ht
  let L : A →ₗ[k] A ⊗[k] B := (TensorProduct.mk k A B).flip 1
  have hL : PreservesGrading 𝒜 (tensorGrading 𝒜 ℬ) L := fun d a ha => by
    have := tmul_mem_tensorGrading (k := k) ha
      (SetLike.GradedOne.one_mem : (1 : B) ∈ ℬ 0)
    rwa [add_zero] at this
  apply hU.smul_eq_zero_of_commute hbound hc
  intro d hd
  have h := decompose_map hL z d
  rw [show L z = z ⊗ₜ[k] 1 from rfl] at h
  rw [h, hpos d hd, map_zero]

omit [IsScalarTower k (A ⊗[k] B) U] in
/-- The right-factor version of positive central annihilation, used in roadmap A0
(KL I, Proposition 2.12 argument). -/
theorem IsGradedSimple.one_tmul_smul_eq_zero_of_commute
    (hU : IsGradedSimple (tensorGrading 𝒜 ℬ) 𝒰) {z : B}
    (hz : ∀ b : B, Commute z b)
    (hpos : ∀ d ≤ 0, (decompose ℬ z d : B) = 0) (u : U) :
    ((1 : A) ⊗ₜ[k] z) • u = 0 := by
  obtain ⟨N, hN⟩ := HasGdim.bddBelow (ℳ := tensorGrading 𝒜 ℬ)
  have hbound : ∀ n < N, tensorGrading 𝒜 ℬ n = ⊥ := by
    intro n hn
    by_contra h
    exact (not_le_of_gt hn) (hN h)
  have hc : ∀ t : A ⊗[k] B, Commute (1 ⊗ₜ[k] z) t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      show ((1 : A) ⊗ₜ[k] z) * (a ⊗ₜ[k] b) = (a ⊗ₜ[k] b) * (1 ⊗ₜ[k] z)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, (hz b).eq]
    | add s t hs ht => exact hs.add_right ht
  let L : B →ₗ[k] A ⊗[k] B := TensorProduct.mk k A B 1
  have hL : PreservesGrading ℬ (tensorGrading 𝒜 ℬ) L := fun d b hb => by
    have := tmul_mem_tensorGrading (k := k)
      (SetLike.GradedOne.one_mem : (1 : A) ∈ 𝒜 0) hb
    rwa [zero_add] at this
  apply hU.smul_eq_zero_of_commute hbound hc
  intro d hd
  have h := decompose_map hL z d
  rw [show L z = 1 ⊗ₜ[k] z from rfl] at h
  rw [h, hpos d hd, map_zero]

omit [HasGdim 𝒜] [HasGdim ℬ] in
/-- A graded simple tensor module annihilated by subspaces in each factor is a
quotient of the tensor of the two quotient spaces (roadmap A0, tensor form of the
finite augmentation quotient argument following KL I, Proposition 2.12). -/
theorem IsGradedSimple.finiteDimensional_tensor_of_quotients
    (hU : IsGradedSimple (tensorGrading 𝒜 ℬ) 𝒰)
    (J₁ : Submodule k A) (J₂ : Submodule k B)
    [FiniteDimensional k (A ⧸ J₁)] [FiniteDimensional k (B ⧸ J₂)]
    (hL : ∀ a ∈ J₁, ∀ (b : B) (u : U), (a ⊗ₜ[k] b) • u = 0)
    (hR : ∀ b ∈ J₂, ∀ (a : A) (u : U), (a ⊗ₜ[k] b) • u = 0) :
    FiniteDimensional k U := by
  have := hU.nontrivial
  obtain ⟨j, v, hv, hv0⟩ := exists_mem_ne_zero 𝒰
  let β : A →ₗ[k] B →ₗ[k] U :=
    LinearMap.mk₂ k (fun a b => (a ⊗ₜ[k] b) • v)
      (fun a a' b => by rw [TensorProduct.add_tmul, add_smul])
      (fun c a b => by rw [← TensorProduct.smul_tmul', smul_assoc])
      (fun a b b' => by rw [TensorProduct.tmul_add, add_smul])
      (fun c a b => by rw [TensorProduct.tmul_smul, smul_assoc])
  have hβ : ∀ a, J₂ ≤ LinearMap.ker (β a) := fun a b hb => hR b hb a v
  let β' : A →ₗ[k] (B ⧸ J₂) →ₗ[k] U :=
    { toFun := fun a => J₂.liftQ (β a) (hβ a)
      map_add' := fun a a' => Submodule.linearMap_qext _ (by
        ext b
        simp [map_add])
      map_smul' := fun c a => Submodule.linearMap_qext _ (by
        ext b
        simp [map_smul]) }
  have hβ' : J₁ ≤ LinearMap.ker β' := fun a ha => Submodule.linearMap_qext _ (by
    ext b
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      LinearMap.zero_comp, LinearMap.zero_apply]
    show β a b = 0
    exact hL a ha b v)
  let Ψ : (A ⧸ J₁) ⊗[k] (B ⧸ J₂) →ₗ[k] U := TensorProduct.lift (J₁.liftQ β' hβ')
  have hΨ : ∀ (a : A) (b : B),
      Ψ (Submodule.Quotient.mk a ⊗ₜ Submodule.Quotient.mk b) = (a ⊗ₜ[k] b) • v :=
    fun _ _ => rfl
  refine Module.Finite.of_surjective Ψ fun u => ?_
  have hu : u ∈ Submodule.span (A ⊗[k] B) {v} := by
    rw [hU.span_singleton_eq_top hv hv0]
    trivial
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
  clear hu
  induction t using TensorProduct.inductionOn with
  | tmul a b => exact ⟨_, hΨ a b⟩
  | add s t hs ht =>
    obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ := ht
    exact ⟨x + y, by rw [map_add, hx, hy, add_smul]⟩

end Tensor

end Categorification.Graded
