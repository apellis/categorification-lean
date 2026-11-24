/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorMiddleMap

/-!
# The two incoming exterior crossing diagrams at label two

Webster, arXiv:1309.3796v2, §8.2, printed page 80. These formulas
identify the actual differential on the projected generator and its
black-crossing translate with the terminal shuffle diagrams.
-/

namespace Categorification.Stendhal
open KLR KLRAlgebra TypeA

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] (param : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "ν" => Multiset.replicate 2 ()
local notation "μ" => stendhalWeight 2 (Multiset.replicate 2 ())
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "S" => stendhalQ param wt
local notation "H" => KLRAlgebra k S μ
local notation "T" => TensorProductAlgebra k param wt ν
local notation "π" => tensorOfKLR param wt ν
local notation "A" => labelTwoExteriorRightLoading
local notation "B" => labelTwoMiddleLoading
local notation "m" => Multiset.card μ
local notation "X₂" => (x (⟨2, by decide⟩ : Fin m) : H)
local notation "X₃" => (x (⟨3, by decide⟩ : Fin m) : H)
local notation "pa" => (X₂ * ψ 2 * e A : H)

private theorem orderedA : IsRedOrdered A := by unfold IsRedOrdered; decide +kernel
private theorem orderedB : IsRedOrdered B := by unfold IsRedOrdered; decide +kernel
local notation "M" => leftStandard param wt B orderedB
local notation "gA" => leftStandardUnit param wt A orderedA
local notation "gB" => leftStandardUnit param wt B orderedB
local notation "MQ" => M ⧸ LinearMap.range (labelTwoMiddleDotSumEnd param)
local notation "gbar" => (Submodule.Quotient.mk gB : MQ)

private theorem right_projector_isIdempotentElem : IsIdempotentElem (pa : H) := by
  have hc : IsConstOn A 2 2 := by unfold IsConstOn; decide
  have h := isIdempotentElem_blockIdem (Q := S) (by decide : 2 + 2 ≤ m) hc
  rw [blockIdem, blockElt_two (by decide : 2 + 1 < m)] at h
  exact h

/-- The projected generator maps to the elementary shuffle and the dotted secondary shuffle. -/
theorem labelTwoExteriorMiddle_map_projectedGen :
    labelTwoExteriorToMiddle param (π pa • gA) =
      π (ψ 1 * e B) • gbar + π (ψ 2 * (ψ 1 * (X₃ * e B))) • gbar := by
  rw [map_smul, labelTwoExteriorToMiddle_unit]
  change π pa • (π (pa * (ψ 1 * e B)) • gbar) = _
  have hp : (pa * (pa * (ψ 1 * e B)) : H) = pa * (ψ 1 * e B) := by
    rw [← mul_assoc, (right_projector_isIdempotentElem param).eq]
  have hmap : π pa * π (pa * (ψ 1 * e B)) = π (pa * (ψ 1 * e B)) := by
    simp only [tensorOfKLR, ← map_mul]
    exact congrArg (π) hp
  rw [← mul_smul]
  refine (congrArg (fun t : T => t • gbar) hmap).trans ?_
  refine (congrArg (fun t : H => π t • gbar) (labelTwo_otherExterior_generator_expansion S)).trans ?_
  simp only [tensorOfKLR, map_add, add_smul]

/-- The black-crossing translate maps to the undotted secondary shuffle. -/
theorem labelTwoExteriorMiddle_map_projectedTranslate :
    labelTwoExteriorToMiddle param (π (ψ 2 : H) • (π pa • gA)) =
      π (ψ 2 * (ψ 1 * e B)) • gbar := by
  rw [map_smul, map_smul, labelTwoExteriorToMiddle_unit]
  change π (ψ 2 : H) • (π pa • (π (pa * (ψ 1 * e B)) • gbar)) = _
  have hp : (ψ 2 * (pa * (pa * (ψ 1 * e B))) : H) = ψ 2 * (pa * (ψ 1 * e B)) := by
    rw [← mul_assoc pa, (right_projector_isIdempotentElem param).eq]
  rw [← mul_smul (π pa), ← mul_smul (π (ψ 2 : H))]
  have hmap : π (ψ 2 : H) * (π pa * π (pa * (ψ 1 * e B))) =
      π (ψ 2 * (pa * (ψ 1 * e B))) := by
    simp only [tensorOfKLR, ← map_mul]
    exact congrArg (π) hp
  exact (congrArg (fun t : T => t • gbar) hmap).trans
    (congrArg (fun t : H => π t • gbar) (labelTwo_otherExterior_generator_translate S))

end
end Categorification.Stendhal
