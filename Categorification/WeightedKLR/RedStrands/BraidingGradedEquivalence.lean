/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CornerGradedEquivalence
import Categorification.WeightedKLR.RedStrands.BraidingEquivalence

/-!
# The graded braiding functors are equivalences

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Theorem 6.15, for the graded braiding functors of Definition 6.6: every graded braiding functor
`𝔅(κ', κ)` between red orders, the derived right tensor with the braided Stendhal bimodule
retaining its auxiliary grading, is an equivalence of derived categories of dg modules over the
weight categories of the corners (`isEquivalence_auxiliaryGradedBraidingFunctor`).

The ungraded braiding functors are equivalences (`isEquivalence_braidingFunctor`), and a graded
derived corner tensor is an equivalence when the ungraded one is
(`Categorification.isEquivalence_diagramCornerWeightDerivedRightTensor`). Route hypotheses:
those of the ungraded theorem, namely the injectivity hypothesis of Lemma 6.8 inside
`RowFigureFiveHypotheses`, at the Khovanov–Lauda scalars.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open CategoryTheory KLR DG
open scoped DG.DegreeZero

section KhovanovLauda

open QuantumGroup KL3.Diagram
open scoped Classical

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} {k : Type} [Field k] (C : CartanDatum I)
  (hQ : IsRouquierQ C (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k))) {ℓ : ℕ}
  {Y : Type*} [AddCommGroup Y] [Finite I]
  {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I),
    Module.Finite k (TensorProductAlgebra k (CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) Ω ν)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)]
  [∀ (Ω : Fin (ℓ + 1) → I →₀ ℕ) (ν : Multiset I) (κ₀ : List (Fin (ℓ + 1))),
    DG.HasDerivedCategory.{0, 0} (ViolOrderCorner (k := k)
      (Q := CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)) (Λ := Ω) (ν := ν) κ₀)ᵐᵒᵖ]
  [DG.HasDerivedCategory.{0, 0} ℤ]
  (H : ∀ (n m : ℕ), n + 2 + m = ℓ + 1 → ∀ (Ω : Fin (n + 2 + m) → I →₀ ℕ)
    (u : Fin (n + 2 + m) → List I) (hu : u (FirstWeight.rightPos n m) = []),
    FirstWeight.RowFigureFiveHypotheses C hQ Ω u hu)

local notation "QL" => CL.qCL (CL.CLScalars.kl : CL.CLScalars C k)
local notation "fin" => List.finRange (ℓ + 1)

include hQ hR H in
/-- **Webster, Theorem 6.15, for the graded braiding functors of Definition 6.6**
(arXiv:1309.3796v3): every graded braiding functor `𝔅(κ', κ)` between red orders, in the
auxiliary grading, is an equivalence of derived categories. Route hypotheses: those of the
ungraded theorem (`isEquivalence_braidingFunctor`), at the Khovanov–Lauda scalars. -/
theorem isEquivalence_auxiliaryGradedBraidingFunctor (Λ : Fin (ℓ + 1) → I →₀ ℕ)
    (ν : Multiset I) (wt : Fin (ℓ + 1) → LieLean.QuantumGroup.GrandLoop.Dom R)
    (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i)) {κ' κ : List (Fin (ℓ + 1))}
    (h' : κ'.Perm fin) (h : κ.Perm fin) (G : KLR.GradingDatum (stendhalQ QL Λ)) :
    letI := Graded.cornerGradedAlgebra (violAuxiliaryGrade (ν := ν) G)
      (isIdempotentElem_violMk_redProj k QL Λ ν κ') (redProj_mem_violAuxiliaryGrade G κ')
    letI := Graded.cornerGradedAlgebra (violAuxiliaryGrade (ν := ν) G)
      (isIdempotentElem_violMk_redProj k QL Λ ν κ) (redProj_mem_violAuxiliaryGrade G κ)
    letI := gradedAlgebraInternalGrading (Graded.oppositeGrade (Graded.cornerGrading
      (violAuxiliaryGrade (ν := ν) G) (isIdempotentElem_violMk_redProj k QL Λ ν κ')))
    letI := gradedAlgebraInternalGrading (Graded.oppositeGrade (Graded.cornerGrading
      (violAuxiliaryGrade (ν := ν) G) (isIdempotentElem_violMk_redProj k QL Λ ν κ)))
    letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade (Graded.cornerGrading
      (violAuxiliaryGrade (ν := ν) G) (isIdempotentElem_violMk_redProj k QL Λ ν κ')))
    letI := gradedAlgebraBigradedDGRing (Graded.oppositeGrade (Graded.cornerGrading
      (violAuxiliaryGrade (ν := ν) G) (isIdempotentElem_violMk_redProj k QL Λ ν κ)))
    [CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (isIdempotentElem_violMk_redProj k QL Λ ν κ').Cornerᵐᵒᵖ)] →
    [CatModule.HasDerivedCategory.{0, 0}
      (WeightCategory (isIdempotentElem_violMk_redProj k QL Λ ν κ).Cornerᵐᵒᵖ)] →
    Functor.IsEquivalence
      (C := CatModule.DerivedCategory.{0, 0}
        (WeightCategory (isIdempotentElem_violMk_redProj k QL Λ ν κ').Cornerᵐᵒᵖ))
      (D := CatModule.DerivedCategory.{0, 0}
        (WeightCategory (isIdempotentElem_violMk_redProj k QL Λ ν κ).Cornerᵐᵒᵖ))
      (auxiliaryGradedBraidingFunctor G κ' κ) := by
  intro _ _
  exact isEquivalence_auxiliaryGradedBraidingFunctor_of_isEquivalence G κ' κ
    (isEquivalence_braidingFunctor C hQ hR H Λ ν wt hwt h' h)

end KhovanovLauda

end Categorification.Stendhal.BraidedStendhalAlgebra
