/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DerivedTensorIdempotentCut
import Categorification.Algebra.DerivedHomologyShift
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorReflectedCut
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorProjectiveAcyclic

/-!
# Ambient diagonal Tor of the outgoing label-two exterior term

The two actual exterior diagram modules are paired by horizontal
reflection. Their ambient degree-zero tensor is the one-dimensional
reflected projector cut, and all other ambient cohomology groups vanish.
-/

namespace Categorification.Stendhal.LabelTwo

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory MulOpposite
open scoped DG.DegreeZero
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w
variable (k : Type) [Field k]
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "ν" => Multiset.replicate 2 ()
local notation "T" => TensorProductAlgebra k (parameter k) wt ν
local notation "p" => labelTwoLeftExteriorProjector (parameter k)
local notation "P" => lIdeal p

private abbrev reflection : T →ₐ[k] Tᵐᵒᵖ := tensorReflect

private def reflectedAction : Tᵐᵒᵖ →+* T :=
  (RingEquiv.opOp T).symm.toRingHom.comp (reflection k).toRingHom.op

/-- The reflected outgoing exterior projective as a right diagram coefficient. -/
def ExteriorProjectiveCoefficient : Type := P

local notation "N" => ExteriorProjectiveCoefficient k

instance : AddCommGroup N := inferInstanceAs (AddCommGroup P)
instance : Module k N := inferInstanceAs (Module k P)
instance : Module Tᵐᵒᵖ N := Module.compHom P (reflectedAction k)

private theorem coefficient_op_smul (a : T) (z : N) :
    (op a • z : N) = ((reflection k a).unop • (show P from z) : P) := rfl

private theorem coefficient_algebraMap_smul (c : k) (z : N) :
    (op (algebraMap k T c) • z : N) = c • z := by
  rw [coefficient_op_smul, AlgHom.commutes]
  exact algebraMap_smul T c (show P from z)

instance : IsScalarTower k Tᵐᵒᵖ N where
  smul_assoc c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    change (op (c • b) • z : N) = c • (op b • z)
    rw [coefficient_op_smul, coefficient_op_smul]
    change (reflection k (c • b)).unop • (show P from z) =
      c • ((reflection k b).unop • (show P from z))
    rw [map_smul, unop_smul, smul_assoc]

instance : SMulCommClass k Tᵐᵒᵖ N where
  smul_comm c a z := by
    obtain ⟨b, rfl⟩ := op_surjective a
    rw [coefficient_op_smul, coefficient_op_smul]
    exact smul_comm c (reflection k b).unop (show P from z)

variable [HasDerivedCategory.{w,0}
  (TensorProductAlgebra k (parameter k) (fun (_ : Fin 2) => Finsupp.single () 2) (Multiset.replicate 2 ()))]
  [HasDerivedCategory.{w,0} k]

/-- The diagonal exterior ambient derived tensor in diagram cohomological degree n. -/
abbrev outgoingExteriorAmbientHomology (n : ℤ) : ModuleCat k :=
  (homologyFunctor k n).obj
    ((derivedTensor k T N).obj (Q.obj (DGModuleCat.of T (InDegreeZero P))))

/-- The only outgoing exterior diagonal ambient homology group is a line. -/
def outgoingExteriorAmbientHomology_zero :
    outgoingExteriorAmbientHomology k 0 ≃ₗ[k] k :=
  (ambientDerivedTensorH0LeftIdealEquiv (coefficient_algebraMap_smul k)
    (isIdempotentElem_labelTwoLeftExteriorProjector (parameter k))).trans
      (labelTwoExteriorReflectedLineEquiv (parameter k)).symm

/-- The outgoing exterior diagonal has no ambient homology outside degree zero. -/
theorem outgoingExteriorAmbientHomology_isZero (n : ℤ) (hn : n ≠ 0) :
    IsZero (outgoingExteriorAmbientHomology k n) := by
  apply isZero_homology_of_isZero_intHomology k
  exact labelTwoLeftExterior_derivedTensorHomology_isZero k N n hn

end
end Categorification.Stendhal.LabelTwo
