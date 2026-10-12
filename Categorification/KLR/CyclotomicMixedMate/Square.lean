/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.KLR.CyclotomicMixedMate.Coefficient

/-!
# Inversion of the removable-colour ordinary mixed mate

`comparison_square` identifies the original mate with the accepted crossing tensored
with an arbitrary module. `originalMateEquiv_eq_mate` and both inverse identities
retain the domain, nonzero factorization and KLR symmetry hypotheses, with arbitrary
cyclotomic polynomials. The input is `{i} + gamma`, including `gamma = 0`; no monicity,
flatness, projectivity or nonzero quotient is assumed. This is ungraded and does not
give a globally absent-input extension, a bundled natural isomorphism or an
all-weight mixed-inversion family.
-/

noncomputable section
namespace Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
open MulOpposite MixedMate
universe u v w
variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (a : I → Polynomial k)
  (γ : Multiset I) (i j : I)
local notation "A" => CycKLR k Q a ((Singleton.singleton j : Multiset I) + γ)
local notation "C" => CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)
variable [IsDomain k] {P : I → I → MvPolynomial (Fin 2) k}
  (hPQ : ∀ a b, a ≠ b → Q a b = P b a * MvPolynomial.rename ![1, 0] (P a b))
  (hP : ∀ a b, a ≠ b → P a b ≠ 0) (hij : i ≠ j) (hsym : KLRSymm Q)
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]
  [IsScalarTower k (CycKLR k Q a ((Singleton.singleton i : Multiset I) + γ)) M]

/-- Tensor the accepted crossing, with the original left/right actions already verified. -/
def tensorForward : MixedModule.LowerTensor Q γ i j a M →ₗ[A] UpperTensor Q a γ i j M :=
  BalancedTensor.liftB
    ((BalancedTensor.mkBil k A C (Corner Q a γ i j) M).comp
      (coefficientEquiv Q a γ i j hPQ hP hij hsym).toLinearMap)
    (fun z c m => by
      change BalancedTensor.tmul (coefficientEquiv Q a γ i j hPQ hP hij hsym (op c • z)) m = _
      rw [coefficientEquiv_right, BalancedTensor.op_smul_tmul]; rfl)
    (fun b z m => by
      change BalancedTensor.tmul (coefficientEquiv Q a γ i j hPQ hP hij hsym (b • z)) m =
        b • BalancedTensor.tmul (coefficientEquiv Q a γ i j hPQ hP hij hsym z) m
      rw [coefficientEquiv_left, BalancedTensor.smul_tmul'])

theorem coefficientEquiv_symm_right (c : C) (z : Corner Q a γ i j) :
    (coefficientEquiv Q a γ i j hPQ hP hij hsym).symm (op c • z) =
      op c • (coefficientEquiv Q a γ i j hPQ hP hij hsym).symm z := by
  apply (coefficientEquiv Q a γ i j hPQ hP hij hsym).injective
  rw [LinearEquiv.apply_symm_apply, coefficientEquiv_right, LinearEquiv.apply_symm_apply]

theorem coefficientEquiv_symm_left (b : A) (z : Corner Q a γ i j) :
    (coefficientEquiv Q a γ i j hPQ hP hij hsym).symm (b • z) =
      b • (coefficientEquiv Q a γ i j hPQ hP hij hsym).symm z := by
  apply (coefficientEquiv Q a γ i j hPQ hP hij hsym).injective
  rw [LinearEquiv.apply_symm_apply, coefficientEquiv_left, LinearEquiv.apply_symm_apply]

/-- Tensor the accepted inverse; no flatness or projectivity is used. -/
def tensorInverse : UpperTensor Q a γ i j M →ₗ[A] MixedModule.LowerTensor Q γ i j a M :=
  BalancedTensor.liftB
    ((BalancedTensor.mkBil k A C (MixedModule.Lower Q γ i j a) M).comp
      (coefficientEquiv Q a γ i j hPQ hP hij hsym).symm.toLinearMap)
    (fun z c m => by
      change BalancedTensor.tmul
        ((coefficientEquiv Q a γ i j hPQ hP hij hsym).symm (op c • z)) m = _
      rw [coefficientEquiv_symm_right, BalancedTensor.op_smul_tmul]; rfl)
    (fun b z m => by
      change BalancedTensor.tmul ((coefficientEquiv Q a γ i j hPQ hP hij hsym).symm (b • z)) m =
        b • BalancedTensor.tmul ((coefficientEquiv Q a γ i j hPQ hP hij hsym).symm z) m
      rw [coefficientEquiv_symm_left, BalancedTensor.smul_tmul'])

omit [IsScalarTower k C M] in
@[simp] theorem tensorForward_tmul (z : MixedModule.Lower Q γ i j a) (m : M) :
    tensorForward Q a γ i j hPQ hP hij hsym M (BalancedTensor.tmul z m) =
      BalancedTensor.tmul (coefficientEquiv Q a γ i j hPQ hP hij hsym z) m := rfl
omit [IsScalarTower k C M] in
@[simp] theorem tensorInverse_tmul (z : Corner Q a γ i j) (m : M) :
    tensorInverse Q a γ i j hPQ hP hij hsym M (BalancedTensor.tmul z m) =
      BalancedTensor.tmul ((coefficientEquiv Q a γ i j hPQ hP hij hsym).symm z) m := rfl

/-- Accepted tensor equivalence on arbitrary original modules. -/
def tensorAcceptedEquiv : MixedModule.LowerTensor Q γ i j a M ≃ₗ[A]
    UpperTensor Q a γ i j M :=
  LinearEquiv.ofLinearMap (tensorForward Q a γ i j hPQ hP hij hsym M)
    (tensorInverse Q a γ i j hPQ hP hij hsym M)
    (by
      apply BalancedTensor.extB
      intro z m
      simp only [LinearMap.coe_comp, Function.comp_apply, tensorForward_tmul, tensorInverse_tmul,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply])
    (by
      apply BalancedTensor.extB
      intro z m
      simp only [LinearMap.coe_comp, Function.comp_apply, tensorForward_tmul, tensorInverse_tmul,
        LinearEquiv.symm_apply_apply, LinearMap.id_apply])

/-- The actual comparison square on an arbitrary module generator. -/
theorem comparison_generator (x : IndCorner Q j a γ)
    (y : MixedModule.Coefficient Q γ i a) (m : M) :
    upperComparison Q a γ i j M
      (mate Q a γ i j M ((MixedModule.indResEquiv Q γ i j a M).symm
        (BalancedTensor.tmul (BalancedTensor.tmul x y) m))) =
      BalancedTensor.tmul
        (coefficientEquiv Q a γ i j hPQ hP hij hsym (BalancedTensor.tmul x y)) m := by
  change cutTensor Q a γ i j M
    (mate Q a γ i j M ((MixedModule.indResEquiv Q γ i j a M).symm
      (BalancedTensor.tmul (BalancedTensor.tmul x y) m))).1 = _
  rw [mate_lower_generator, cutTensor_tmul]
  congr 1
  apply Subtype.ext
  change leftInc Q a γ i j 1 * (op y.1 • factor Q a γ i j x).1 = _
  rw [← coefficientEquiv_tmul Q a γ i j hPQ hP hij hsym x y]
  exact (coefficientEquiv Q a γ i j hPQ hP hij hsym (BalancedTensor.tmul x y)).2.1

/-- The full well-defined square uses the original ordinary-adjunction mate. -/
theorem comparison_square :
    (upperComparison Q a γ i j M).toLinearMap.comp
      ((mate Q a γ i j M).comp (MixedModule.indResEquiv Q γ i j a M).symm.toLinearMap) =
        tensorForward Q a γ i j hPQ hP hij hsym M := by
  apply BalancedTensor.extB
  intro z m
  induction z using BalancedTensor.induction_on with
  | zero => simp only [BalancedTensor.zero_tmul, map_zero]
  | add z t hz ht => simp only [BalancedTensor.add_tmul, map_add, hz, ht]
  | tmul x y => exact comparison_generator Q a γ i j hPQ hP hij hsym M x y m

/-- An equivalence whose forward map is proved to be the already-defined original mate. -/
def originalMateEquiv : MixedModule.FE Q γ i j a M ≃ₗ[A] Target Q a γ i j M :=
  (MixedModule.indResEquiv Q γ i j a M).trans
    ((tensorAcceptedEquiv Q a γ i j hPQ hP hij hsym M).trans
      (upperComparison Q a γ i j M).symm)

theorem originalMateEquiv_eq_mate :
    (originalMateEquiv Q a γ i j hPQ hP hij hsym M).toLinearMap = mate Q a γ i j M := by
  apply LinearMap.ext
  intro z
  apply (upperComparison Q a γ i j M).injective
  change upperComparison Q a γ i j M ((upperComparison Q a γ i j M).symm
    (tensorForward Q a γ i j hPQ hP hij hsym M (MixedModule.indResEquiv Q γ i j a M z))) = _
  rw [LinearEquiv.apply_symm_apply]
  have h := LinearMap.congr_fun (comparison_square Q a γ i j hPQ hP hij hsym M)
    (MixedModule.indResEquiv Q γ i j a M z)
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using h.symm

/-- The actual inverse, formed using the accepted inverse and the two concrete comparisons. -/
def mateInverse : Target Q a γ i j M →ₗ[A] MixedModule.FE Q γ i j a M :=
  (originalMateEquiv Q a γ i j hPQ hP hij hsym M).symm.toLinearMap

theorem mateInverse_mate (z : MixedModule.FE Q γ i j a M) :
    mateInverse Q a γ i j hPQ hP hij hsym M (mate Q a γ i j M z) = z := by
  rw [← originalMateEquiv_eq_mate Q a γ i j hPQ hP hij hsym M]
  exact (originalMateEquiv Q a γ i j hPQ hP hij hsym M).symm_apply_apply z

theorem mate_mateInverse (z : Target Q a γ i j M) :
    mate Q a γ i j M (mateInverse Q a γ i j hPQ hP hij hsym M z) = z := by
  rw [← originalMateEquiv_eq_mate Q a γ i j hPQ hP hij hsym M]
  exact (originalMateEquiv Q a γ i j hPQ hP hij hsym M).apply_symm_apply z

end Categorification.KLR.KLRAlgebra.AbsentColour.MixedComparison
