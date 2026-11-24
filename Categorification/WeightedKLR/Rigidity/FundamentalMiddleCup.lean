/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.FundamentalMiddleHead
import Categorification.WeightedKLR.Rigidity.CapRHomProjectives
import Categorification.WeightedKLR.Rigidity.DerivedCupRegular

/-!
# The fundamental cup and its left adjoint at the middle cut

Webster, arXiv:1309.3796v2, §7.1, Definition 7.4 and Proposition 7.5.
After forgetting the internal grading, the derived Hom cup takes the
ground field to the simple quotient at (0,1), shifted by minus one.
Before this shift its left adjoint evaluates the (0,1) projective to the
ground field and annihilates the (0,0) projective.
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits Coevaluation DG
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe v
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)
local notation "S" => rIdeal middleIdem ⧸ middleCutTrace
local notation "zeroObj" R:arg N:arg => DG.DerivedCategory.Q.obj (DGModuleCat.of R (InDegreeZero N))
private theorem idem (s : KLR.Seq (stendhalWeight 2 ({()} : Multiset Unit))) :
    IsIdempotentElem (project (StendhalAlgebraAllOrders.e s)) :=
  IsIdempotentElem.map (by simp [IsIdempotentElem, StendhalAlgebraAllOrders.e_mul_e]) project

variable [CatModule.HasDerivedCategory.{v,0} (SingleObj ℚ)]
    [CatModule.HasDerivedCategory.{v,0} (SingleObj Tᵐᵒᵖ)]
    [HasDerivedCategory.{v,0} ℚ] [HasDerivedCategory.{v,0} Tᵐᵒᵖ]

/-- The cup defined using the scalar derived Hom and the cohomological shift of Definition 7.4. -/
abbrev middleCup := shiftedCupRHomFunctor.{0,v} ℚ T MiddleCoefficient (-1)

/-- On the field the shifted scalar derived Hom cup gives the simple head of Lemma 7.3. -/
def middleCup_fieldIso :
    middleCup.obj (DG.DerivedCategory.Q.obj (DGModuleCat.of ℚ ℚ)) ≅
      (shiftFunctor (DerivedCategory.{v,0} Tᵐᵒᵖ) (-1)).obj (zeroObj Tᵐᵒᵖ S) := by
  let e := middleQuotientDualEquiv
  let h : InDegreeZero S ≃ᵈᵍ[Tᵐᵒᵖ] InDegreeZero (CupCoefficient ℚ MiddleCoefficient) :=
    DGModuleEquiv.ofDegreeZero e
      (fun hx hn => ((InDegreeZero.mem_grading_iff _).mp hx).resolve_left hn)
      (InDegreeZero.d_apply _)
      (fun x => (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl)) (InDegreeZero.d_apply _)
  exact (shiftFunctor (DerivedCategory.{v,0} Tᵐᵒᵖ) (-1)).mapIso
    (cupRHomRegularIso ℚ T MiddleCoefficient ≪≫ DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv h.symm))

/-- The derived tensor with the middle coefficient is the left adjoint of the unshifted derived Hom cup. -/
def middleCapCupAdjunction :
    capBimoduleFunctor ℚ T MiddleCoefficient ⊣ cupRHomFunctor ℚ T MiddleCoefficient :=
  capBimoduleCupRHomAdjunction ℚ T MiddleCoefficient

/-- The left adjoint evaluates the (0,1) projective to one scalar in degree zero. -/
def middleAdjointCap_middleIso :
    (capBimoduleFunctor ℚ T MiddleCoefficient).obj (zeroObj Tᵐᵒᵖ (rIdeal middleIdem)) ≅ zeroObj ℚ ℚ := by
  let : Module.Projective Tᵐᵒᵖ (rIdeal middleIdem) := rIdeal_projective (idem middle)
  exact capBimoduleProjectiveIso ℚ T MiddleCoefficient (DGModuleCat.of Tᵐᵒᵖ (InDegreeZero (rIdeal middleIdem)))
    (show IsKProjective Tᵐᵒᵖ (InDegreeZero (rIdeal middleIdem)) from InDegreeZero.isKProjective) ≪≫ middleCap_middleIso

/-- The same left adjoint annihilates the (0,0) projective. -/
theorem middleAdjointCap_terminal_isZero :
    IsZero ((capBimoduleFunctor ℚ T MiddleCoefficient).obj (zeroObj Tᵐᵒᵖ (rIdeal terminalIdem))) := by
  let : Module.Projective Tᵐᵒᵖ (rIdeal terminalIdem) := rIdeal_projective (idem terminal)
  exact middleCap_terminal_isZero.of_iso (capBimoduleProjectiveIso ℚ T MiddleCoefficient
    (DGModuleCat.of Tᵐᵒᵖ (InDegreeZero (rIdeal terminalIdem)))
    (show IsKProjective Tᵐᵒᵖ (InDegreeZero (rIdeal terminalIdem)) from InDegreeZero.isKProjective))

end Categorification.Stendhal.FundamentalCorner
