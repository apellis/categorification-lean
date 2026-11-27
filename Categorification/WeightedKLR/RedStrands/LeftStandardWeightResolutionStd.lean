/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardWeightResolution
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd

/-!
# The graded ordered resolution for Rouquier parameters

Use Webster's Corollary 5.21 to supply the higher trace filtration in the
direct left loading resolution of Lemma 6.11.
-/

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup KL3.Diagram KLR ModuleFiltration DG CategoryTheory
open scoped DG.DegreeZero Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [Field k] {C : CartanDatum I} {Q : I → I → MvPolynomial (Fin 2) k}
  {l : ℕ} (Λ : Fin l → I →₀ ℕ) (ν : Multiset I)

variable (G : GradingDatum (stendhalQ Q Λ))
  (hR : IsRouquierQ C Q)
  (s : {t : Seq (stendhalWeight l ν) // IsRedOrdered t})

/-- Corollary 5.21 supplies the higher traces for the graded ordered
resolution for Rouquier parameters. -/
def leftStandardOrderedWeightResolution_of_rouquier :=
  leftStandardOrderedWeightResolution G
    (fun t => exists_hasFiltration_leftUpper_of_rouquier hR 
      (fun a b h => (hR.symm a b h).symm) Λ ν t.val t.property) s

/-- The augmentation of the Rouquier-parameter ordered resolution. -/
def leftStandardOrderedWeightAugmentation_of_rouquier :=
  leftStandardOrderedWeightAugmentation G
    (fun t => exists_hasFiltration_leftUpper_of_rouquier hR 
      (fun a b h => (hR.symm a b h).symm) Λ ν t.val t.property) s

theorem leftStandardOrderedWeightResolution_of_rouquier_isKProjective :
    letI := gradedAlgebraInternalGrading (tensorProductGrade G ν)
    letI := gradedAlgebraBigradedDGRing (tensorProductGrade G ν)
    CatModule.IsKProjective (leftStandardOrderedWeightResolution_of_rouquier Λ ν G hR s) :=
  leftStandardOrderedWeightResolution_isKProjective G
    (fun t => exists_hasFiltration_leftUpper_of_rouquier hR 
      (fun a b h => (hR.symm a b h).symm) Λ ν t.val t.property) s

theorem leftStandardOrderedWeightAugmentation_of_rouquier_quasiIso :
    letI := gradedAlgebraInternalGrading (tensorProductGrade G ν)
    letI := gradedAlgebraBigradedDGRing (tensorProductGrade G ν)
    CatModule.IsQuasiIso (leftStandardOrderedWeightAugmentation_of_rouquier Λ ν G hR s) :=
  leftStandardOrderedWeightAugmentation_quasiIso G
    (fun t => exists_hasFiltration_leftUpper_of_rouquier hR 
      (fun a b h => (hR.symm a b h).symm) Λ ν t.val t.property) s

end Categorification.Stendhal
