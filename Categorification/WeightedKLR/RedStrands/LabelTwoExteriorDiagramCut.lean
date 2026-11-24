/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicDividedCut
import Categorification.WeightedKLR.RedStrands.ParabolicStandardLastIndMap
import Categorification.WeightedKLR.RedStrands.SingleRedTerminalProjective
import Categorification.KLR.CyclotomicAbsentColour

/-!
# The exterior standardization cuts for the label-two unknot

Webster, arXiv:1309.3796v2, §8.2, Proposition 8.4, printed page 80.
The two exterior allocations have one vacuum factor. A lift of the
saturated divided-power idempotent of the other factor cuts out a scalar
line in the actual diagrammatic standardization for either allocation.
-/

noncomputable section

namespace Categorification.Stendhal.SingleRed

open KLR KLRAlgebra
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] (Q : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "ν" => Multiset.replicate 2 ()
local notation "Λ₁" => fun (_ : Fin 1) => Finsupp.single () 2
local notation "Λ₂" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "A" => TensorProductAlgebra k Q Λ₁ ν
local notation "p" => twoBlackTerminalWebsterIdem Q
local notation "hP" => twoBlackTerminalWebsterIdem_idempotent Q

/-- The non-vacuum factor is the first one in the exterior (2,0) allocation. -/
def labelTwoFirstFactorEquiv : parabolicFactorAlgebra Q Λ₂ ν 0 ≃ₐ[k] A :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (cyclotomicZeroEquiv Q _)).trans
    (Algebra.TensorProduct.rid k k A)

/-- The non-vacuum factor is the last one in the exterior (0,2) allocation. -/
def labelTwoLastFactorEquiv : parabolicFactorAlgebra Q Λ₂ 0 ν ≃ₐ[k] A := by
  let e := (cyclotomicEquiv Q Λ₁ 0).symm.trans (cyclotomicZeroEquiv Q _)
  let e' := cyclotomicEquiv Q Λ₁ ν
  exact (Algebra.TensorProduct.congr e e').trans (Algebra.TensorProduct.lid k A)

variable {θ β : Multiset Unit}
local notation "D" => parabolicFactorAlgebra Q Λ₂ θ β
local notation "α" => Multiset.map (addRedColor 1) (stendhalWeight 1 θ)
local notation "δ" => Multiset.map (Sum.map (id : Unit → Unit) (fun _ : Fin 1 => Fin.last 1))
  (stendhalWeight 1 β)
local notation "B" => TensorKLR (stendhalQ Q Λ₂) α δ

variable (factorEquiv : parabolicFactorAlgebra Q (fun (_ : Fin 2) => Finsupp.single () 2) θ β
  ≃ₐ[k] TensorProductAlgebra k Q (fun (_ : Fin 1) => Finsupp.single () 2)
    (Multiset.replicate 2 ()))

private def exteriorIdempotent : D := factorEquiv.symm p

local notation "f" => exteriorIdempotent Q factorEquiv
local notation "V" => lIdeal (exteriorIdempotent Q factorEquiv)

private def fixedCorner : fixSub k V f ≃ₗ[k] (hP).Corner where
  toFun x := ⟨factorEquiv x.val.val,(Subsemigroup.mem_corner_iff hP).mpr
    ⟨by
      have h : f * x.val.val = x.val.val := congrArg Subtype.val x.property
      simpa only [exteriorIdempotent, map_mul, AlgEquiv.apply_symm_apply] using congrArg factorEquiv h,
     by
      have h := mem_lIdeal.mp x.val.property
      simpa only [exteriorIdempotent, map_mul, AlgEquiv.apply_symm_apply] using congrArg factorEquiv h⟩⟩
  invFun x := by
    have h := (Subsemigroup.mem_corner_iff hP).mp x.property
    exact ⟨⟨factorEquiv.symm x.val, mem_lIdeal.mpr (by rw [exteriorIdempotent, ← map_mul, h.2])⟩,
      Subtype.ext (by change f * factorEquiv.symm x.val = factorEquiv.symm x.val; rw [exteriorIdempotent, ← map_mul, h.1])⟩
  left_inv x := Subtype.ext (Subtype.ext (factorEquiv.symm_apply_apply x.val.val))
  right_inv x := Subtype.ext (factorEquiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add factorEquiv x.val.val y.val)
  map_smul' c x := Subtype.ext (map_smul factorEquiv c x.val.val)

/-- An affine lift of the primitive factor idempotent defining its diagram cut. -/
def labelTwoExteriorLift : B :=
  (parabolicInputMap_surjective Q Λ₂ θ β f).choose

theorem labelTwoExteriorLift_spec :
    parabolicInputMap Q Λ₂ θ β (labelTwoExteriorLift Q factorEquiv) = f :=
  (parabolicInputMap_surjective Q Λ₂ θ β f).choose_spec

/-- The affine lift acts as an idempotent on the exterior standardization. -/
theorem isIdempotentElem_labelTwoExteriorProjection (hQ : KLRSymm Q) :
    IsIdempotentElem
      (parabolicStandardConcatAction Q Λ₂ θ β V hQ (labelTwoExteriorLift Q factorEquiv)) := by
  apply isIdempotentElem_parabolicStandardConcatAction
  rw [labelTwoExteriorLift_spec]
  exact (hP).map factorEquiv.symm

/-- The primitive divided-power cut of either exterior standardization is one scalar. -/
def labelTwoExteriorStandardCutEquiv (hQ : KLRSymm Q) :
    LinearMap.ker
      (parabolicStandardConcatAction Q Λ₂ θ β V hQ (labelTwoExteriorLift Q factorEquiv) -
        LinearMap.id) ≃ₗ[k] k := by
  let t := labelTwoExteriorLift Q factorEquiv
  let line : fixSub k V (parabolicInputMap Q Λ₂ θ β t) ≃ₗ[k] k := by
    change fixSub k V (parabolicInputMap Q Λ₂ θ β (labelTwoExteriorLift Q factorEquiv)) ≃ₗ[k] k
    rw [labelTwoExteriorLift_spec]
    exact (fixedCorner Q factorEquiv).trans (twoBlackTerminalWebsterCornerEquiv Q).toLinearEquiv
  exact (parabolicStandardFixedEquiv Q Λ₂ θ β V hQ t).symm.trans line

end Categorification.Stendhal.SingleRed
