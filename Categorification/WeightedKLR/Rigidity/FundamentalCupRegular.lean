/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalCupCap
import Categorification.Algebra.DerivedTensorRegular

/-!
# Computing the fundamental type A₁ cup on the ground field

The cup of Webster's Definition 7.4, arXiv:1309.3796v2, takes the field
to the terminal simple quotient with shift minus one after forgetting
the internal grading. The cap takes the regular Webster module to the
left terminal coefficient.
-/

noncomputable section

namespace Categorification.Stendhal.FundamentalCorner

open CategoryTheory Coevaluation DG MulOpposite
open scoped DG.DegreeZero

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe v
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "S" => rIdeal terminalIdem ⧸ fundamentalCutTrace

private instance : SMulCommClass T ℚ FundamentalCoefficient where
  smul_comm a c x := smul_algebra_smul_comm c a x

variable [HasDerivedCategory.{v,0} ℚ] [HasDerivedCategory.{v,0} Tᵐᵒᵖ]

/-- The fundamental cup takes the ground field to the terminal simple
quotient with the prescribed cohomological shift. -/
def fundamentalCupRegularIso :
    fundamentalCup.obj (DG.DerivedCategory.Q.obj (DGModuleCat.of ℚ ℚ)) ≅
      (shiftFunctor (DerivedCategory.{v,0} Tᵐᵒᵖ) (-1)).obj
        (DG.DerivedCategory.Q.obj (DGModuleCat.of Tᵐᵒᵖ (InDegreeZero S))) := by
  let e := terminalQuotientDualEquiv
  let eDG : InDegreeZero S ≃ᵈᵍ[Tᵐᵒᵖ] InDegreeZero (CupCoefficient ℚ FundamentalCoefficient) :=
    { toLinearEquiv := e
      map_mem' := fun {n m} hz => by
        have h := (InDegreeZero.mem_grading_iff (M := S)).mp hz
        change (show InDegreeZero (CupCoefficient ℚ FundamentalCoefficient) from
          e (show S from m)) ∈ DG.grading n
        apply (InDegreeZero.mem_grading_iff (M := CupCoefficient ℚ FundamentalCoefficient)).mpr
        rcases h with h | h
        · exact Or.inl h
        · right
          change (show S from m) = 0 at h
          change e (show S from m) = 0
          rw [h, map_zero]
      map_d' := fun _ => e.map_zero }
  exact (shiftFunctor (DerivedCategory.{v,0} Tᵐᵒᵖ) (-1)).mapIso
    (derivedTensorRegularCoefficientIso Tᵐᵒᵖ ℚ (CupCoefficient ℚ FundamentalCoefficient) ≪≫
      DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv eDG.symm))

/-- The fundamental cap takes the regular Webster module to its
left coefficient in degree zero. -/
def fundamentalCapRegularIso :
    fundamentalCap.obj (DG.DerivedCategory.Q.obj (DGModuleCat.of Tᵐᵒᵖ Tᵐᵒᵖ)) ≅
      DG.DerivedCategory.Q.obj
        (DGModuleCat.of ℚ (InDegreeZero (OpBimodule T FundamentalCoefficient))) :=
  derivedTensorRegularCoefficientIso ℚ Tᵐᵒᵖ (OpBimodule T FundamentalCoefficient)

end Categorification.Stendhal.FundamentalCorner
