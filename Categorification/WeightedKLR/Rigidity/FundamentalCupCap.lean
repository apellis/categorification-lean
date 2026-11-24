/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.DerivedCupCap
import Categorification.WeightedKLR.Rigidity.FundamentalCoevaluation

/-!
# Cups and caps for two fundamental type A₁ factors

Webster, arXiv:1309.3796v2, Definition 7.4. Over the rationals the dual
of the terminal character module is the simple right quotient by the
smaller-cut trace. This supplies the coefficient of the ungraded cup and cap.
-/

noncomputable section

namespace Categorification.Stendhal.FundamentalCorner

open CategoryTheory Coevaluation DG MulOpposite
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)

/-- The left coefficient for the pair of fundamental type A₁ weights over ℚ. -/
def FundamentalCoefficient := ℚ

instance : AddCommGroup FundamentalCoefficient := inferInstanceAs (AddCommGroup ℚ)
instance : Module ℚ FundamentalCoefficient := inferInstanceAs (Module ℚ ℚ)
instance : Module T FundamentalCoefficient := Module.compHom ℚ terminalCharacter.toRingHom

instance : IsScalarTower ℚ T FundamentalCoefficient where
  smul_assoc c a x := by
    change terminalCharacter (c • a) * (show ℚ from x) = c * (terminalCharacter a * (show ℚ from x))
    rw [map_smul, smul_eq_mul, mul_assoc]

/-- The dual coefficient carries the right action by the same character. -/
theorem dualCoefficient_smul_apply (a : T)
    (f : CupCoefficient ℚ FundamentalCoefficient) (x : FundamentalCoefficient) :
    (show Module.Dual ℚ FundamentalCoefficient from op a • f) x =
      terminalCharacter a * (show Module.Dual ℚ FundamentalCoefficient from f) x := by
  rw [cup_op_smul_apply]
  exact map_smul (show Module.Dual ℚ FundamentalCoefficient from f) (terminalCharacter a) x

private def scalarFunctional : CupCoefficient ℚ FundamentalCoefficient :=
  LinearMap.id

private def terminalToDual : rIdeal terminalIdem →ₗ[Tᵐᵒᵖ]
    CupCoefficient ℚ FundamentalCoefficient where
  toFun x := terminalCoefficient x • scalarFunctional
  map_add' x y := by
    change (terminalCoefficient (x+y)) • scalarFunctional = _
    rw [map_add, add_smul]
  map_smul' a x := by
    apply LinearMap.ext
    intro y
    change (terminalCoefficient (a • x) • (show Module.Dual ℚ FundamentalCoefficient from
      scalarFunctional)) y = (show Module.Dual ℚ FundamentalCoefficient from
      a • (terminalCoefficient x • scalarFunctional)) y
    rw [← op_unop a, dualCoefficient_smul_apply]
    change terminalCharacter (x.val * a.unop) * (show ℚ from y) =
      terminalCharacter a.unop * (terminalCharacter x.val * (show ℚ from y))
    rw [map_mul]
    ring

private theorem terminalToDual_ker : LinearMap.ker terminalToDual = fundamentalCutTrace := by
  ext x
  rw [LinearMap.mem_ker, mem_fundamentalCutTrace_iff]
  constructor
  · intro h
    have he := congrArg (fun f : CupCoefficient ℚ FundamentalCoefficient =>
      (show Module.Dual ℚ FundamentalCoefficient from f) (1 : ℚ)) h
    change terminalCoefficient x * (1 : ℚ) = 0 at he
    change terminalCoefficient x = 0
    simpa only [mul_one] using he
  · intro h
    change terminalCoefficient x • scalarFunctional = 0
    change terminalCoefficient x = 0 at h
    rw [h, zero_smul]

private theorem terminalToDual_surjective : Function.Surjective terminalToDual := by
  intro f
  let f' : Module.Dual ℚ FundamentalCoefficient := f
  obtain ⟨x, hx⟩ := terminalCoefficient_surjective (f' (1 : ℚ))
  refine ⟨x, ?_⟩
  apply LinearMap.ext
  intro y
  change terminalCoefficient x * (show ℚ from y) = f' y
  rw [hx, mul_comm]
  have hy : (show ℚ from y) • (show FundamentalCoefficient from (1 : ℚ)) = y := by
    change (show ℚ from y) * 1 = (show ℚ from y)
    exact mul_one _
  exact (map_smul f' (show ℚ from y) (show FundamentalCoefficient from (1 : ℚ))).symm.trans
    (congrArg f' hy)

/-- The dual coefficient of the cup is the simple right quotient from
Webster's Lemma 7.3, expressed using the terminal character. -/
def terminalQuotientDualEquiv :
    (rIdeal terminalIdem ⧸ fundamentalCutTrace) ≃ₗ[Tᵐᵒᵖ]
      CupCoefficient ℚ FundamentalCoefficient :=
  (Submodule.quotEquivOfEq _ _ terminalToDual_ker.symm).trans
    (LinearMap.quotKerEquivOfSurjective terminalToDual terminalToDual_surjective)

universe v

variable [HasDerivedCategory.{v,0} ℚ] [HasDerivedCategory.{v,0} Tᵐᵒᵖ]

/-- The ungraded type A₁ fundamental cup with cohomological shift minus one. -/
def fundamentalCup : DerivedCategory.{v,0} ℚ ⥤ DerivedCategory.{v,0} Tᵐᵒᵖ :=
  shiftedCupFunctor ℚ T FundamentalCoefficient (-1)

/-- The ungraded type A₁ fundamental cap with the terminal coefficient. -/
def fundamentalCap : DerivedCategory.{v,0} Tᵐᵒᵖ ⥤ DerivedCategory.{v,0} ℚ :=
  capFunctor ℚ T FundamentalCoefficient


end Categorification.Stendhal.FundamentalCorner
