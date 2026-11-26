/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.RightTwist
import Categorification.Algebra.Graded.ProjectiveCharacterIso

/-!
# Right twists of finite-dimensional modules and projective characters

Regarding a graded left module as a graded right module through a graded anti-involution `ψ`
does not change graded Hom spaces: a map `P^ψ → M^ψ` of right modules is the same additive map
as a map `P → M` of left modules (`homGradeRightTwistEquiv`). Hence the Laurent-polynomial
coordinates `[P] ↦ dim_q Hom(P, M)` of a finite-dimensional module agree with those of its right
twist along the identification `K₀(A) ≃ K₀(Aᵐᵒᵖ)` of `K0.rightTwistEquiv`
(`projectiveHomPolynomial_rightTwist`).
-/

noncomputable section
namespace Categorification.Graded

open MulOpposite

universe u v
variable {k : Type v} [Field k] {A : Type u} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] (ψ : GradedAntiInvolution 𝒜)

/-- A homogeneous map of right twists is the same additive map as a homogeneous map of the
underlying left modules. -/
def homGradeRightTwistEquiv (P M : GMod 𝒜) (d : ℤ) :
    homGrade Aᵐᵒᵖ (P.rightTwist ψ).grading (M.rightTwist ψ).grading d ≃ₗ[k]
      homGrade A P.grading M.grading d where
  toFun f := ⟨{ f.1.toAddHom with
    map_smul' := fun a x => by
      let g : P.carrier → M.carrier := fun t => f.1 (Twist.of (ψ := ψ) (k := k) t)
      change g (a • x) = a • g x
      have h := f.1.map_smul (op (ψ a)) (Twist.of (ψ := ψ) (k := k) x)
      have h' : g (ψ (ψ a) • x) = ψ (ψ a) • g x := h
      rwa [ψ.invol] at h' }, f.2⟩
  invFun f := ⟨{ f.1.toAddHom with
    map_smul' := fun a x => f.1.map_smul (ψ a.unop) (Twist.of.symm x) }, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The right twist of a finite-dimensional graded module. -/
def GFin.rightTwist (M : GFin 𝒜) : GFin (oppositeGrade 𝒜) :=
  { toGMod := M.toGMod.rightTwist ψ
    finiteDimensional := inferInstanceAs (FiniteDimensional k M.carrier) }

theorem pairingRight_rightTwist (M : GFin 𝒜) (x : K0 𝒜) :
    pairingRight (M.rightTwist ψ) (K0.rightTwistEquiv ψ x) = pairingRight M x := by
  induction x using K0.induction_on with
  | of P =>
    rw [K0.rightTwistEquiv_of, pairingRight_of, pairingRight_of]
    exact gdim_eq_of_finrank_eq fun d =>
      (homGradeRightTwistEquiv ψ P.toGMod M.toGMod d).finrank_eq
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | neg x hx => simp only [map_neg, hx]

variable [Module.Finite k A]

/-- Right twisting preserves the projective Hom polynomial. -/
theorem projectiveHomPolynomial_rightTwist (M : GFin 𝒜) (x : K0 𝒜) :
    projectiveHomPolynomial _ (M.rightTwist ψ) (K0.rightTwistEquiv ψ x) =
      projectiveHomPolynomial _ M x :=
  toLaurentSeries_injective (by
    rw [toLaurentSeries_projectiveHomPolynomial, toLaurentSeries_projectiveHomPolynomial,
      pairingRight_rightTwist])

end Categorification.Graded
