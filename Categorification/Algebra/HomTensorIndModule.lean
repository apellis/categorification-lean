/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.HomTensorInd
import Categorification.Algebra.HomTensorDecomp
import Categorification.Algebra.BalancedTensorTransport

/-!
# Induction along a ring map as a module functor

Let `F : C ⥤ D` be additive, `O` an object of `C`, `O'` an object of `D`, and let
`σ : A ≃+* (End O)ᵐᵒᵖ` and `φ : A →ₙ+* B`. An additive isomorphism
`c : Corner φ ≃+ (O' ⟶ F O)` intertwining the right actions of `A` and `(End O)ᵐᵒᵖ`
identifies induction `Ind N φ = Corner φ ⊗_A N` with the module functor
`(O' ⟶ F O) ⊗_{End O} N'` of `F` (`HomTensor.tensorObj`), for every `A`-module `N` and every
right `End O`-module `N'` identified with `N` along `σ` (`indTensorEquiv`). The identification
is semilinear along `τ : B ≃+* (End O')ᵐᵒᵖ` when `c` is (`indTensorEquiv_smul`).

This extends `HomTensor.indEquiv`, which treats the modules `O ⟶ X`, to arbitrary modules, so
that the module-level decompositions of `HomTensor.sumDecompModule` apply to Webster's
induction functors on modules (arXiv:1309.3796v3, §4.6 and Proposition 5.5).
-/

namespace Categorification.HomTensor

open CategoryTheory MulOpposite InductionAlong

noncomputable section

universe u w

variable {C : Type*} [Category C] [Preadditive C] {D : Type*} [Category D] [Preadditive D]
  {F : C ⥤ D} [F.Additive] {O : C} {O' : D}
  {A : Type u} [Ring A] {B : Type u} [Ring B] {φ : A →ₙ+* B} {σ : A ≃+* (End O)ᵐᵒᵖ}

attribute [local instance] bimodule

variable (c : Corner φ ≃+ (O' ⟶ F.obj O))
  (hc : ∀ (a : A) (z : Corner φ), c (op a • z) = c z ≫ F.map (σ a).unop)
  {N : Type w} [AddCommGroup N] [Module A N]
  {N' : Type w} [AddCommGroup N'] [Module (End O)ᵐᵒᵖ N']
  (g : N ≃+ N') (hg : ∀ (a : A) (n : N), g (a • n) = σ a • g n)

/-- **Induction as a module functor**: `Corner φ ⊗_A N ≅ (O' ⟶ F O) ⊗_{End O} N'`. -/
def indTensorEquiv :
    Ind N φ ≃ₗ[ℤ] BalancedTensor ℤ (End O')ᵐᵒᵖ (End O)ᵐᵒᵖ (O' ⟶ F.obj O) N' :=
  BalancedTensor.changeRingEquiv σ c.toIntLinearEquiv g.toIntLinearEquiv hc hg

theorem indTensorEquiv_tmul (z : Corner φ) (n : N) :
    indTensorEquiv c hc g hg (Ind.tmul z n) = BalancedTensor.tmul (c z) (g n) := rfl

/-- The identification of `indTensorEquiv` is semilinear along `τ`. -/
theorem indTensorEquiv_smul (τ : B ≃+* (End O')ᵐᵒᵖ)
    (hτ : ∀ (b : B) (z : Corner φ), c (b • z) = (τ b).unop ≫ c z) (b : B) (x : Ind N φ) :
    indTensorEquiv c hc g hg (b • x) = τ b • indTensorEquiv c hc g hg x :=
  BalancedTensor.changeRingEquiv_smul σ c.toIntLinearEquiv g.toIntLinearEquiv hc hg τ hτ b x

end

end Categorification.HomTensor
