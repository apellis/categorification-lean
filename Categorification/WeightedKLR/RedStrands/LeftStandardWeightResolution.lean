/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.OrderedWeightDGProjectivity
import Categorification.Algebra.DiagramBigrading
import Categorification.WeightedKLR.RedStrands.GradedLeftStandard
import Categorification.WeightedKLR.RedStrands.OrderedStandardResolution

/-!
# The ordered weight-dg resolution of a left loading standard

Apply the graded ordered resolution in Webster, arXiv:1309.3796v2, Lemma 6.11,
to the actual graded left standard of Definition 5.1. The required higher
filtrations are the ordinary standard-stratification input. The prescribed
quotient and scalar action preserve the diagram grading.
-/

noncomputable section

namespace Categorification.Stendhal
open KLR DG CategoryTheory ModuleFiltration DirectSum
open scoped DG.DegreeZero

private abbrev orderedWeightLabels {I : Type} (l : ℕ) (v : Multiset I) :=
  {x : Seq (stendhalWeight l v) // IsRedOrdered x}

variable {I k : Type} [DecidableEq I] [Field k] {l : ℕ} {ν : Multiset I}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin l → I →₀ ℕ}
  (G : KLR.GradingDatum (stendhalQ Q Λ))

local notation "DAlg" => TensorProductAlgebra k Q Λ ν
local notation "DGrade" => tensorProductGrade G ν

private abbrev standardModule (Q : I → I → MvPolynomial (Fin 2) k)
    (Λ : Fin l → I →₀ ℕ) (s : orderedWeightLabels l ν) :=
  ModuleCat.of (TensorProductAlgebra k Q Λ ν) (leftStandard Q Λ s.val s.property)

private abbrev standardKernel (Q : I → I → MvPolynomial (Fin 2) k)
    (Λ : Fin l → I →₀ ℕ) (s : orderedWeightLabels l ν) :=
  (leftUpper Q Λ s.val s.property).comap (lIdeal (seqIdem Q Λ s.val s.property)).subtype

variable (hU : ∀ s : orderedWeightLabels l ν, ∃ m : List (orderedWeightLabels l ν),
  (∀ t ∈ m, StendhalLT s.val t.val) ∧ HasFiltration (standardModule Q Λ) m
    (ModuleCat.of (TensorProductAlgebra k Q Λ ν) (standardKernel Q Λ s)))
  (s : orderedWeightLabels l ν)

local notation "IG" => gradedAlgebraInternalGrading DGrade
local notation "BG" => gradedAlgebraBigradedDGRing DGrade

private abbrev leftStandardOrderedCovers :=
  orderedStandardCovers Q Λ hU

private abbrev leftStandardWeightGrade (n : ℤ) : AddSubgroup (standardModule Q Λ s) :=
  (gradedLeftStandard G s.val s.property n).toAddSubgroup

local instance instActualLeftStandardGradeDecomposition :
    Decomposition (leftStandardWeightGrade G s) := by
  let Γ := gradedLeftStandard G s.val s.property
  letI : Decomposition Γ := gradedLeftStandardDecomposition G s.val s.property
  exact {
    decompose' := Decomposition.decompose' (ℳ := Γ)
    left_inv := Decomposition.left_inv (ℳ := Γ)
    right_inv := Decomposition.right_inv (ℳ := Γ) }

private theorem leftOrderedIdemWeight (t : orderedWeightLabels l ν) :
    seqIdem Q Λ t.val t.property ∈ DGrade 0 :=
  mk_e_mem_tensorProductGrade G ν t.val t.property

private theorem leftOrderedIsIdem (t : orderedWeightLabels l ν) :
    IsIdempotentElem (seqIdem Q Λ t.val t.property) :=
  seqIdem_mul_self Q Λ t.val t.property

private theorem leftOrderedTrans (a b c : orderedWeightLabels l ν)
    (hab : StendhalLT a.val b.val) (hbc : StendhalLT b.val c.val) :
    StendhalLT a.val c.val :=
  ⟨fun r i => (hab.1 r i).trans (hbc.1 r i), fun hca =>
    hab.2 (fun r i => (hbc.1 r i).trans (hca r i))⟩

private theorem leftOrderedQuotientWeight ⦃n : ℤ⦄ ⦃x : lIdeal (seqIdem Q Λ s.val s.property)⦄
    (hx : x.val ∈ DGrade n) :
    (leftStandardOrderedCovers hU).quotient s x ∈ leftStandardWeightGrade G s n :=
  gradedLeftStandard_mkQ_mem G s.val s.property x hx

private theorem leftStandardWeightSmul {i j : ℤ} {a : DAlg} {x : standardModule Q Λ s}
    (ha : a ∈ DGrade i) (hx : x ∈ leftStandardWeightGrade G s j) :
    a • x ∈ leftStandardWeightGrade G s (i+j) :=
  gradedLeftStandard_smul_mem G s.val s.property ha hx

/-- The K-projective ordered dg model of the diagrammatic left standard. -/
def leftStandardOrderedWeightResolution :
    letI := IG
    letI := BG
    CatModule (WeightCategory DAlg) := by
  letI := IG
  letI := BG
  exact orderedWeightDgResolution (leftStandardOrderedCovers hU) s (leftOrderedIdemWeight G)
    (leftOrderedIsIdem (Q := Q) (Λ := Λ)) leftOrderedTrans (leftStandardWeightGrade G s)
    (leftOrderedQuotientWeight G hU s)

theorem leftStandardOrderedWeightResolution_isKProjective :
    letI := IG
    letI := BG
    CatModule.IsKProjective (leftStandardOrderedWeightResolution G hU s) := by
  let := IG
  let := BG
  exact orderedWeightDgResolution_isKProjective (leftStandardOrderedCovers hU) s (leftOrderedIdemWeight G)
    (leftOrderedIsIdem (Q := Q) (Λ := Λ)) leftOrderedTrans (leftStandardWeightGrade G s)
    (leftOrderedQuotientWeight G hU s)

/-- The actual graded left standard viewed as a weight dg module. -/
def leftStandardWeightModule :
    letI := IG
    letI := BG
    CatModule (WeightCategory DAlg) := by
  letI := IG
  letI := BG
  exact orderedWeightDgTarget (S := standardModule Q Λ) s (leftStandardWeightGrade G s) (leftStandardWeightSmul G s)

/-- The projective resolution's augmentation is the actual homogeneous standard quotient. -/
def leftStandardOrderedWeightAugmentation :
    letI := IG
    letI := BG
    leftStandardOrderedWeightResolution G hU s ⟶ leftStandardWeightModule G s := by
  letI := IG
  letI := BG
  exact orderedWeightDgAugmentation (leftStandardOrderedCovers hU) s (leftOrderedIdemWeight G)
    (leftOrderedIsIdem (Q := Q) (Λ := Λ)) leftOrderedTrans (leftStandardWeightGrade G s)
    (leftStandardWeightSmul G s) (leftOrderedQuotientWeight G hU s)

theorem leftStandardOrderedWeightAugmentation_quasiIso :
    letI := IG
    letI := BG
    CatModule.IsQuasiIso (leftStandardOrderedWeightAugmentation G hU s) := by
  let := IG
  let := BG
  exact orderedWeightDgAugmentation_quasiIso (leftStandardOrderedCovers hU) s (leftOrderedIdemWeight G)
    (leftOrderedIsIdem (Q := Q) (Λ := Λ)) leftOrderedTrans (leftStandardWeightGrade G s)
    (leftStandardWeightSmul G s) (leftOrderedQuotientWeight G hU s)

end Categorification.Stendhal
