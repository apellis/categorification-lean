/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.Algebra.HomTensorInd
import Categorification.Algebra.HomTensorDecomp
import Categorification.Algebra.BalancedTensorTransport
import Categorification.Algebra.InductionAlongResTensor

/-!
# Induction along a ring map as a module functor

Let `F : C ⥤ D` be additive, `O` an object of `C`, `O'` an object of `D`, and let
`σ : A ≃+* (End O)ᵐᵒᵖ` and `φ : A →ₙ+* B`. An additive isomorphism
`c : Corner φ ≃+ (O' ⟶ F O)` intertwining the right actions of `A` and `(End O)ᵐᵒᵖ`
identifies induction `Ind N φ = Corner φ ⊗_A N` with the module functor
`(O' ⟶ F O) ⊗_{End O} N'` of `F` (`HomTensor.tensorObj`), for every `A`-module `N` and every
right `End O`-module `N'` identified with `N` along `σ` (`indTensorEquiv`). The identification
is semilinear along `τ : B ≃+* (End O')ᵐᵒᵖ` when `c` is (`indTensorEquiv_smul`). Dually, for
`ψ : A' →ₙ+* A` and an additive isomorphism `r : Res ψ A ≃+ (O' ⟶ F O)` intertwining the right
actions, restriction `Res_ψ N` is the module functor of `F` (`resTensorEquiv`). Every `A`-module
is a right `End O`-module along `σ` (`transferModule`).

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

/-- An `A`-module as a right `End O`-module along `σ`. -/
abbrev transferModule (σ : A ≃+* (End O)ᵐᵒᵖ) (N : Type w) [AddCommGroup N] [Module A N] :
    Module (End O)ᵐᵒᵖ N :=
  Module.compHom N σ.symm.toRingHom

omit [AddCommGroup N'] [Module (End O)ᵐᵒᵖ N'] in
theorem transferModule_smul (a : A) (n : N) :
    letI := transferModule σ N
    σ a • n = a • n := by
  let _ := transferModule σ N
  change σ.symm (σ a) • n = a • n
  rw [σ.symm_apply_apply]

section Res

variable {A' : Type u} [Ring A'] {ψ : A' →ₙ+* A}
  (r : Res ψ A ≃+ (O' ⟶ F.obj O))
  (hr : ∀ (a : A) (x : Res ψ A), r (op a • x) = r x ≫ F.map (σ a).unop)
  (M : Type u) [AddCommGroup M] [Module A M]

/-- **Restriction as a module functor**: `Res_ψ M ≅ (O' ⟶ F O) ⊗_{End O} M`, with `M` a right
`End O`-module along `σ`. -/
def resTensorEquiv :
    letI := transferModule σ M
    Res ψ M ≃ₗ[ℤ] BalancedTensor ℤ (End O')ᵐᵒᵖ (End O)ᵐᵒᵖ (O' ⟶ F.obj O) M :=
  letI := transferModule σ M
  (resTensor ψ M).toAddEquiv.toIntLinearEquiv.trans
    (BalancedTensor.changeRingEquiv σ r.toIntLinearEquiv (LinearEquiv.refl ℤ M) hr
      (fun a n => (transferModule_smul a n).symm))

theorem resTensorEquiv_apply (m : Res ψ M) :
    letI := transferModule σ M
    resTensorEquiv r hr M m = BalancedTensor.tmul (r (resUnit ψ)) m.val :=
  rfl

theorem resTensorEquiv_eq (m : Res ψ M) :
    letI := transferModule σ M
    resTensorEquiv r hr M m = BalancedTensor.changeRingEquiv σ r.toIntLinearEquiv
      (LinearEquiv.refl ℤ M) hr (fun a n => (transferModule_smul a n).symm) (resTensor ψ M m) :=
  rfl

/-- The identification of `resTensorEquiv` is semilinear along `τ : A' ≃+* (End O')ᵐᵒᵖ`. -/
theorem resTensorEquiv_smul (τ : A' ≃+* (End O')ᵐᵒᵖ)
    (hτ : ∀ (a : A') (x : Res ψ A), r (a • x) = (τ a).unop ≫ r x) (a : A') (m : Res ψ M) :
    letI := transferModule σ M
    resTensorEquiv r hr M (a • m) = τ a • resTensorEquiv r hr M m := by
  let _ := transferModule σ M
  rw [resTensorEquiv_eq, resTensorEquiv_eq, (resTensor ψ M).map_smul]
  exact BalancedTensor.changeRingEquiv_smul σ _ _ hr _ τ hτ a _

end Res

end

end Categorification.HomTensor
