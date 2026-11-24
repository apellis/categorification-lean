/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.DiagramWeightCorner
import Categorification.WeightedKLR.RedStrands.BraidingFunctor
import Categorification.WeightedKLR.RedStrands.BraidedStandardGrading

/-!
# Derived braiding with the auxiliary integer grading

The actual braided Stendhal bimodule has a restricted auxiliary grading
between the degree-zero projections of its two red orders. The associated
derived right tensor retains that grading. The degree of a red/red crossing
uses the augmented KLR grading here.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR

variable {I k : Type*} [DecidableEq I] [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

/-- The projection to an arbitrary red order has auxiliary degree zero. -/
theorem redProj_mem_violAuxiliaryGrade (κ : List (Fin ℓ)) :
    violMk k Q Λ ν (redProj k Q Λ ν κ) ∈ violAuxiliaryGrade G 0 := by
  rw [redProj, redIdem, map_sum, map_sum]
  exact Submodule.sum_mem _ fun j _ =>
    Graded.mem_map_of_mem _ (violMk k Q Λ ν).toLinearMap
      (Graded.mem_map_of_mem _ (ofKLR k Q Λ ν).toLinearMap (G.e_mem_grade j))


end Categorification.Stendhal.BraidedStendhalAlgebra

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR DG CategoryTheory
open scoped DG.DegreeZero

universe u v

variable {I : Type*} {k : Type u} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "V" => violAuxiliaryGrade (ν := ν) G
local notation "hE" => isIdempotentElem_violMk_redProj k Q Λ ν
local notation "S" => fun κ => Graded.oppositeGrade (Graded.cornerGrading V (hE κ))

/-- The derived right tensor of the actual braiding coefficient in its auxiliary
integer grading. The red/red crossing normalization supplies an additional shift. -/
def auxiliaryGradedBraidingFunctor (κ' κ : List (Fin ℓ)) :
    letI := Graded.cornerGradedAlgebra V (hE κ')
      (redProj_mem_violAuxiliaryGrade G κ')
    letI := Graded.cornerGradedAlgebra V (hE κ)
      (redProj_mem_violAuxiliaryGrade G κ)
    letI := gradedAlgebraInternalGrading (S κ')
    letI := gradedAlgebraInternalGrading (S κ)
    letI := gradedAlgebraBigradedDGRing (S κ')
    letI := gradedAlgebraBigradedDGRing (S κ)
    [CatModule.HasDerivedCategory.{v,_} (WeightCategory (hE κ').Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{v,_} (WeightCategory (hE κ).Cornerᵐᵒᵖ)] →
    CatModule.DerivedCategory.{v,_} (WeightCategory (hE κ').Cornerᵐᵒᵖ) ⥤
      CatModule.DerivedCategory.{v,_} (WeightCategory (hE κ).Cornerᵐᵒᵖ) :=
  diagramCornerWeightDerivedRightTensor V (hE κ') (hE κ)
    (redProj_mem_violAuxiliaryGrade G κ') (redProj_mem_violAuxiliaryGrade G κ)

end Categorification.Stendhal.BraidedStendhalAlgebra
