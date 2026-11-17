/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.HomForm
import Categorification.Algebra.Graded.K0Map

/-!
# Transport of the graded Hom form

A graded algebra isomorphism identifies homogeneous module maps after
restriction of scalars, and hence preserves the projective Euler form.
-/

noncomputable section
namespace Categorification.Graded

universe u v
variable {k : Type v} [Field k] {A B : Type u} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    {𝒜 : ℤ → Submodule k A} {ℬ : ℤ → Submodule k B} (σ : A ≃ₐ[k] B)
    (hσ : ∀ ⦃d : ℤ⦄ ⦃b : B⦄, b ∈ ℬ d → σ.symm b ∈ 𝒜 d)

local notation "R" => GProj.restrict (𝒜 := 𝒜) (𝒜' := ℬ) σ hσ

/-- A homogeneous map of a degree-preserving restriction along an algebra
isomorphism is the same additive map as before restriction. -/
def GProj.homGradeRestrictEquiv (P Q : GProj 𝒜) (d : ℤ) :
    homGrade B (R P).grading (R Q).grading d ≃ₗ[k] homGrade A P.grading Q.grading d where
  toFun f := ⟨{ f.1.toAddHom with
    map_smul' := fun a x => by
      let g : P.carrier → Q.carrier := fun t => f.1 t
      change g (a • x) = a • g x
      have h : g (σ.symm (σ a) • x) = σ.symm (σ a) • g x := f.1.map_smul (σ a) x
      simpa only [σ.symm_apply_apply] using h }, f.2⟩
  invFun f := ⟨{ f.1.toAddHom with map_smul' := fun b x => f.1.map_smul (σ.symm b) x }, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The graded projective Hom form is invariant under transport along a
degree-preserving algebra isomorphism. -/
theorem K0.homForm_map [GradedAlgebra 𝒜] [GradedAlgebra ℬ] [HasGdim 𝒜] [HasGdim ℬ]
    (x y : K0 𝒜) :
    K0.homForm ℬ (K0.map σ hσ x) (K0.map σ hσ y) = K0.homForm 𝒜 x y := by
  induction y using K0.induction_on with
  | of Q =>
    induction x using K0.induction_on with
    | of P =>
      rw [K0.map_of, K0.map_of, K0.homForm_of, K0.homForm_of]
      exact gdim_eq_of_finrank_eq fun d => (GProj.homGradeRestrictEquiv σ hσ P Q d).finrank_eq
    | zero => simp only [map_zero, AddMonoidHom.zero_apply]
    | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
    | neg x hx => simp only [map_neg, AddMonoidHom.neg_apply, hx]
  | zero => simp only [map_zero]
  | add y y' hy hy' => simp only [map_add, hy, hy']
  | neg y hy => simp only [map_neg, hy]

end Categorification.Graded
