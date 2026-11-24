/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CapProjectives
import Categorification.WeightedKLR.Rigidity.FundamentalCoevaluation
import Categorification.WeightedKLR.RedStrands.StandardModule

/-!
# Fundamental evaluation at the two cuts

In Webster, arXiv:1309.3796v2, Definition 4.1 and §7.1, Proposition 7.5,
the cut counts the black termini on the left of each red terminus. In type
A₁ at the fundamental weight, the cut (0,1) has the black strand between
the red strands. The cap with this boundary character sends its projective
to the ground field and kills the projective at the smaller cut (0,0).
-/

noncomputable section
namespace Categorification.Stendhal.FundamentalCorner
open CategoryTheory CategoryTheory.Limits DG MulOpposite Coevaluation
open scoped DG.DegreeZero
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "μ" => stendhalWeight 2 ({()} : Multiset Unit)
local notation "T" => TensorProductAlgebra ℚ Q wt ({()} : Multiset Unit)

/-- The two values of the root function at the second red terminus. -/
theorem middle_terminal_cuts :
    blackCount middle 0 () = 0 ∧ blackCount middle 1 () = 1 ∧
      blackCount terminal 0 () = 0 ∧ blackCount terminal 1 () = 0 := by
  decide +kernel

private theorem middle_redOrdered : IsRedOrdered middle := by unfold IsRedOrdered; decide +kernel

/-- The one-dimensional character supported on the cut (0,1). -/
def middleCharacter : T →ₐ[ℚ] ℚ :=
  FirstWeight.boundaryCharacter Q wt (by intro r; simp [wt]) middle middle_redOrdered
    (by unfold IsViolated; decide +kernel)

/-- In the ordered corner the all-orders loading projector equals the image of its ordered idempotent. -/
theorem projectedLoading_eq_mk_e (s : KLR.Seq μ) (hs : IsRedOrdered s) :
    project (StendhalAlgebraAllOrders.e s) =
      TensorProductAlgebra.mk Q wt {()} (StendhalAlgebra.e s hs) := by
  apply congrArg (TensorProductAlgebra.mk Q wt {()})
  apply Subtype.ext
  exact (StendhalAlgebraAllOrders.e_mul_redOrderedIdem s).trans (ite_eq_left hs)

@[simp] theorem middleCharacter_middleIdem : middleCharacter middleIdem = 1 := by
  simp [middleIdem, projectedLoading_eq_mk_e _ middle_redOrdered, middleCharacter, FirstWeight.boundaryCharacter_e]

@[simp] theorem middleCharacter_terminalIdem : middleCharacter terminalIdem = 0 := by
  simp [terminalIdem, projectedLoading_eq_mk_e _ terminal_ordered, middleCharacter,
    FirstWeight.boundaryCharacter_e, show terminal ≠ middle by decide +kernel]

/-- The left coefficient on which a diagram acts by its middle character. -/
def MiddleCoefficient := ℚ

instance : AddCommGroup MiddleCoefficient := inferInstanceAs (AddCommGroup ℚ)
instance : Module ℚ MiddleCoefficient := inferInstanceAs (Module ℚ ℚ)
instance : Module T MiddleCoefficient := Module.compHom ℚ middleCharacter.toRingHom
instance : IsScalarTower ℚ T MiddleCoefficient where
  smul_assoc c a x := by
    change middleCharacter (c • a) * (show ℚ from x) = c * (middleCharacter a * (show ℚ from x))
    rw [map_smul, smul_eq_mul, mul_assoc]

@[simp] theorem middleIdem_smul_middleCoefficient (x : MiddleCoefficient) : middleIdem • x = x := by
  change middleCharacter middleIdem * (show ℚ from x) = _
  rw [middleCharacter_middleIdem, one_mul]

@[simp] theorem terminalIdem_smul_middleCoefficient (x : MiddleCoefficient) : terminalIdem • x = 0 := by
  change middleCharacter terminalIdem * (show ℚ from x) = 0
  rw [middleCharacter_terminalIdem, zero_mul]

private theorem loadingIdem_idem (s : KLR.Seq μ) :
    IsIdempotentElem (project (StendhalAlgebraAllOrders.e s)) :=
  IsIdempotentElem.map (by simp [IsIdempotentElem, StendhalAlgebraAllOrders.e_mul_e]) project

universe v
variable [HasDerivedCategory.{v,0} ℚ] [HasDerivedCategory.{v,0} Tᵐᵒᵖ]
local notation "zeroObj" R:arg N:arg => DG.DerivedCategory.Q.obj (DGModuleCat.of R (InDegreeZero N))

/-- The derived cap with coefficient at Webster's cut (0,1). -/
abbrev middleCap := capFunctor.{0,v} ℚ T MiddleCoefficient

/-- The cap vanishes at the smaller cut, whose black strand is to the right of both reds. -/
theorem middleCap_terminal_isZero :
    IsZero (middleCap.obj (zeroObj Tᵐᵒᵖ (rIdeal terminalIdem))) := by
  let e := capFunctor_projectiveIso ℚ T MiddleCoefficient (loadingIdem_idem terminal)
  have : Subsingleton (fixSub ℚ MiddleCoefficient terminalIdem) := ⟨fun x y => Subtype.ext (by
    have hx := mem_fixSub.mp x.property
    have hy := mem_fixSub.mp y.property
    rw [terminalIdem_smul_middleCoefficient] at hx hy
    exact hx.symm.trans hy)⟩
  let : Subsingleton (InDegreeZero (fixSub ℚ MiddleCoefficient terminalIdem)) :=
    (InDegreeZero.equiv _).injective.subsingleton
  exact (DG.DerivedCategory.Q.map_isZero (DGModuleCat.isZero_of_subsingleton
    (DGModuleCat.of ℚ (InDegreeZero (fixSub ℚ MiddleCoefficient terminalIdem))))).of_iso e

/-- Webster, arXiv:1309.3796v2, Proposition 7.5. The derived cap of the projective
with the black strand between the two fundamental reds is the scalar line in degree zero. -/
def middleCap_middleIso :
    middleCap.obj (zeroObj Tᵐᵒᵖ (rIdeal middleIdem)) ≅ zeroObj ℚ ℚ := by
  let e : fixSub ℚ MiddleCoefficient middleIdem ≃ₗ[ℚ] ℚ :=
    LinearEquiv.ofBijective (fixSub ℚ MiddleCoefficient middleIdem).subtype
      ⟨Subtype.val_injective, fun x => ⟨⟨x, middleIdem_smul_middleCoefficient x⟩, rfl⟩⟩
  let h : InDegreeZero (fixSub ℚ MiddleCoefficient middleIdem) ≃ᵈᵍ[ℚ] InDegreeZero ℚ :=
    DGModuleEquiv.ofDegreeZero e
      (fun hx hn => ((InDegreeZero.mem_grading_iff _).mp hx).resolve_left hn)
      (InDegreeZero.d_apply _)
      (fun y => (InDegreeZero.mem_grading_iff _).mpr (Or.inl rfl))
      (InDegreeZero.d_apply _)
  exact capFunctor_projectiveIso ℚ T MiddleCoefficient (loadingIdem_idem middle) ≪≫
    DG.DerivedCategory.Q.mapIso (DGModuleCat.isoOfDGModuleEquiv h)

end Categorification.Stendhal.FundamentalCorner
