/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoExteriorMiddleMap
import Categorification.WeightedKLR.RedStrands.StendhalTensorGrading
import Categorification.WeightedKLR.RedStrands.LabelTwoPeriodic

/-!
# The incoming exterior return before the dot-sum quotient

The return of the lifted incoming generator gives the actual middle
dot-sum relation. In the separated middle algebra, this relation survives
modulo the image of its second multiplication.
-/

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA
noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {k : Type} [Field k] (param : Unit → Unit → MvPolynomial (Fin 2) k)
local notation "ν" => Multiset.replicate 2 ()
local notation "μ" => stendhalWeight 2 ν
local notation "wt" => fun (_ : Fin 2) => Finsupp.single () 2
local notation "H" => KLRAlgebra k (stendhalQ param wt) μ
local notation "π" => stendhalTensorProjection (Q := param) wt ν
local notation "A" => labelTwoExteriorRightLoading
local notation "B" => labelTwoMiddleLoading
local notation "X₂" => (x (⟨2, by decide⟩ : Fin (Multiset.card μ)) : H)
local notation "up" => ((X₂ * ψ 2 * e A) * (ψ 1 * e B) : H)
local notation "down" => (ψ 1 * ψ 2 : H)

private theorem orderedB : IsRedOrdered B := by unfold IsRedOrdered; decide +kernel
local notation "S" => leftStandard param wt B orderedB
local notation "g" => leftStandardUnit param wt B orderedB

private theorem generator_fixed : π (e B) • (g : S) = g := by
  rw [stendhalTensorProjection_e wt ν B orderedB, leftStandardUnit, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext (seqIdem_mul_self param wt B orderedB)

private theorem affine_return : down * up = (ψ 1 * ψ 2 * ψ 1 : H) * e B := by
  rw [mul_assoc (ψ 1), labelTwo_otherExterior_generator_translate]
  simp only [mul_assoc]

/-- The two-crossing return sends the lifted incoming generator to the
dot-sum relation in the unquotiented middle standard. -/
theorem labelTwo_incomingLift_return :
    π down • (π up • (g : S)) = labelTwoMiddleDotSumEnd param g := by
  rw [← mul_smul, ← map_mul, affine_return, map_mul, mul_smul,
    generator_fixed]
  exact (labelTwo_otherExterior_middleBraid param).trans
    (labelTwoMiddleDotSumEnd_generator param).symm

end
end Categorification.Stendhal

namespace Categorification.Webster.LabelTwo

variable {k : Type*} [CommRing k] [Nontrivial k]

/-- The dot-sum relation itself survives after quotienting its image by the
second application of the dot sum. -/
theorem plus_one_notMem_range_plus_comp_plus :
    plus (1 : Middle k) ∉ LinearMap.range ((plus (k := k)).comp plus) := by
  rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,h⟩
  change plus (plus (⟨⟨a,b⟩,⟨c,d⟩⟩ : Middle k)) = plus 1 at h
  rw [plus_coordinates, plus_coordinates] at h
  have h₁ := congrArg (fun z : Middle k => z.snd.fst) h
  have hunit : plus (1 : Middle k) = ⟨⟨0,1⟩,⟨1,0⟩⟩ := by
    change plus (⟨⟨1,0⟩,⟨0,0⟩⟩ : Middle k) = _
    rw [plus_coordinates, zero_add]
  rw [hunit] at h₁
  exact zero_ne_one h₁

end Categorification.Webster.LabelTwo
