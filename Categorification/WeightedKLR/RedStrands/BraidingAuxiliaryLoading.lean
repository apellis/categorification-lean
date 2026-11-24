/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidingAuxiliaryDerived
import Categorification.WeightedKLR.RedStrands.BraidedStandardDerived

/-!
# Loading support for the auxiliary graded braid

Webster, arXiv:1309.3796v2, Lemma 6.11. Actual loading idempotents act at each
weight of the braid corner. The support criterion tests annihilation on the
underlying rectangular braid coefficient.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR DG CategoryTheory CategoryTheory.Limits
open scoped DG.DegreeZero

universe u v

variable {I : Type} {k : Type u} [DecidableEq I] [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "V" => violAuxiliaryGrade (ν := ν) G
local notation "hE" => isIdempotentElem_violMk_redProj k Q Λ ν
local notation "S" κ:arg => Graded.oppositeGrade (Graded.cornerGrading V (hE κ))

/-- The ordinary loading projector determines a degree-zero endomorphism of every
weight in the auxiliary graded braid source category of Webster's Lemma 6.11. -/
def auxiliaryGradedLoadingHom {s : Seq (stendhalWeight ℓ ν)} {κ : List (Fin ℓ)}
    (hs : redWord s = κ) :
    letI := Graded.cornerGradedAlgebra V (hE κ) (redProj_mem_violAuxiliaryGrade G κ)
    letI := gradedAlgebraInternalGrading (S κ)
    letI := gradedAlgebraBigradedDGRing (S κ)
    (Z : WeightCategory (hE κ).Cornerᵐᵒᵖ) → (Z ⟶ Z) := by
  letI := Graded.cornerGradedAlgebra V (hE κ) (redProj_mem_violAuxiliaryGrade G κ)
  letI := gradedAlgebraInternalGrading (S κ)
  letI := gradedAlgebraBigradedDGRing (S κ)
  intro Z
  refine WeightCategory.homMk (MulOpposite.op (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs)) ?_
  rw [sub_self]
  change (violLoadingIdem (k := k) (Q := Q) (Λ := Λ) hs).val ∈ V 0
  exact Graded.mem_map_of_mem _ (violMk k Q Λ ν).toLinearMap
    (Graded.mem_map_of_mem _ (ofKLR k Q Λ ν).toLinearMap (G.e_mem_grade s))

/-- The loading-support vanishing criterion on the actual auxiliary graded braid
coefficient, with the annihilation checked by ordinary left multiplication. -/
theorem auxiliaryGradedBraiding_cohomology_isZero_of_loading_support
    (κ' κ : List (Fin ℓ)) :
    letI := Graded.cornerGradedAlgebra V (hE κ') (redProj_mem_violAuxiliaryGrade G κ')
    letI := Graded.cornerGradedAlgebra V (hE κ) (redProj_mem_violAuxiliaryGrade G κ)
    letI := gradedAlgebraInternalGrading (S κ')
    letI := gradedAlgebraInternalGrading (S κ)
    letI := gradedAlgebraBigradedDGRing (S κ')
    letI := gradedAlgebraBigradedDGRing (S κ)
    ∀ [CatModule.HasDerivedCategory.{v,u} (WeightCategory (hE κ').Cornerᵐᵒᵖ)]
      [CatModule.HasDerivedCategory.{v,u} (WeightCategory (hE κ).Cornerᵐᵒᵖ)]
      {K M : CatModule.{u} (WeightCategory (hE κ').Cornerᵐᵒᵖ)} (q : K ⟶ M),
      CatModule.IsKProjective K → CatModule.IsQuasiIso q →
      ∀ (X : WeightCategory (hE κ).Cornerᵐᵒᵖ) (n : ℤ)
        {ι : Type} (labels : ι → {s : Seq (stendhalWeight ℓ ν) // redWord s = κ'}),
        (∀ Z (m : K.obj Z), m ∈ DG.grading n →
          m ∈ AddSubgroup.closure (diagramWeightLoadingGenerators K
            (fun W (i : ι) => auxiliaryGradedLoadingHom G (labels i).2 W) Z)) →
        (∀ i (p : braidingBimodule k Q Λ ν κ' κ),
          (violLoadingIdem (labels i).2).val * p.val = 0) →
        IsZero ((CatModule.DerivedCategory.cohomologyFunctor X n).obj
          ((auxiliaryGradedBraidingFunctor G κ' κ).obj (CatModule.DerivedCategory.Q.obj M))) := by
  intro iK iM K M q hK hq X n ι labels hspan hkill
  exact diagramCornerWeightDerivedRightTensor_cohomology_isZero_of_loading_support
    V (hE κ') (hE κ) (redProj_mem_violAuxiliaryGrade G κ')
    (redProj_mem_violAuxiliaryGrade G κ) q hK hq X n
    (fun Z i => auxiliaryGradedLoadingHom G (labels i).2 Z) hspan
    (fun _ i p => hkill i p)

end Categorification.Stendhal.BraidedStendhalAlgebra
