/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LeftStandardWeightResolution
import Categorification.WeightedKLR.RedStrands.StandardStratificationStd

/-!
# The graded ordered resolution at standard Khovanov–Lauda parameters

Use Webster's Corollary 5.21 to supply the higher trace filtration in the
direct left loading resolution of Lemma 6.11.
-/

noncomputable section

namespace Categorification.Stendhal

open QuantumGroup KL3.Diagram KLR ModuleFiltration DG CategoryTheory
open scoped DG.DegreeZero Classical
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I k : Type} [Field k] {C : CartanDatum I}
  {l : ℕ} (Λ : Fin l → I →₀ ℕ) (ν : Multiset I)

private abbrev klParameter (C : CartanDatum I) (k : Type) [Field k] :=
  CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)

variable (G : GradingDatum (stendhalQ (klParameter C k) Λ))
  (hR : IsRouquierQ C (klParameter C k))
  (s : {t : Seq (stendhalWeight l ν) // IsRedOrdered t})

/-- Corollary 5.21 supplies the higher traces for the graded ordered
resolution at the standard Khovanov–Lauda parameters. -/
def leftStandardOrderedWeightResolution_std :=
  leftStandardOrderedWeightResolution G
    (fun t => exists_hasFiltration_leftUpper_std hR (fun a b h => (hR.symm a b h).symm) Λ ν t.val t.property) s

/-- The augmentation of the standard-parameter ordered resolution. -/
def leftStandardOrderedWeightAugmentation_std :=
  leftStandardOrderedWeightAugmentation G
    (fun t => exists_hasFiltration_leftUpper_std hR (fun a b h => (hR.symm a b h).symm) Λ ν t.val t.property) s

theorem leftStandardOrderedWeightResolution_std_isKProjective :
    letI := gradedAlgebraInternalGrading (tensorProductGrade G ν)
    letI := gradedAlgebraBigradedDGRing (tensorProductGrade G ν)
    CatModule.IsKProjective (leftStandardOrderedWeightResolution_std Λ ν G hR s) :=
  leftStandardOrderedWeightResolution_isKProjective G
    (fun t => exists_hasFiltration_leftUpper_std hR (fun a b h => (hR.symm a b h).symm) Λ ν t.val t.property) s

theorem leftStandardOrderedWeightAugmentation_std_quasiIso :
    letI := gradedAlgebraInternalGrading (tensorProductGrade G ν)
    letI := gradedAlgebraBigradedDGRing (tensorProductGrade G ν)
    CatModule.IsQuasiIso (leftStandardOrderedWeightAugmentation_std Λ ν G hR s) :=
  leftStandardOrderedWeightAugmentation_quasiIso G
    (fun t => exists_hasFiltration_leftUpper_std hR (fun a b h => (hR.symm a b h).symm) Λ ν t.val t.property) s

end Categorification.Stendhal
