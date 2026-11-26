/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.ProjectiveCharacterIso
import Categorification.WeightedKLR.RedStrands.IteratedLeftStandard
import Categorification.WeightedKLR.RedStrands.IteratedStandardK0
import Categorification.WeightedKLR.RedStrands.LeftStandardGFin

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 5.6 for the standard modules of Definition 5.1

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, §5,
Definition 5.1 and Proposition 5.6. For a row of black words `u_1, …, u_n`, the standard module
`S_s = T e(s) / U_s` of Definition 5.1 at the loading `s` with the word `u_j` after the `j`-th
red strand (`rowLoading`) is graded isomorphic to the iterated standardization
(`rowLoading_gradedEquiv`). Hence its Hom functional on the projective group is the
componentwise form against `F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_n} v_{λ_n}` through Webster's
identification `η` of Theorem 4.38 (`rowStandard_projectiveCharacter_eq`), read in the bar
coproduct convention.
-/

noncomputable section

namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded QuantumGroup LieLean LieLean.QuantumGroup
  LieLean.QuantumGroup.GrandLoop LusztigF

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "LP" => LaurentPolynomial ℤ

variable {I : Type} [DecidableEq I] [Finite I] {k : Type} [Field k]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : QuantumGroup.CartanDatum I) (hQ : IsRouquierQ C Q)
  {Y : Type*} [AddCommGroup Y] {R : C.toLusztig.RootDatum Y} (hR : R.IsXRegular)

/-- The standard module of Definition 5.1 at the row loading of `u`, as a finite-dimensional
graded module over the tensor product algebra. -/
def rowStandard (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I) :
    GFin (tensorProductGrade (iteratedGrading C hQ Λ) (blockContent u)) :=
  let := tensorProductAlgebra_finite Λ (blockContent u) hQ
  leftStandardGFin (iteratedGrading C hQ Λ) (rowLoading n u) (isRedOrdered_rowLoading n u)

omit [Finite I] in
theorem rowStandard_carrier (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I) :
    (rowStandard C hQ n Λ u).carrier = leftStandard Q Λ (rowLoading n u)
      (isRedOrdered_rowLoading n u) := rfl

/-- The standard module at the row loading is graded isomorphic to the iterated
standardization `S_κ^i`. -/
def rowStandardIso (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I) :
    (rowStandard C hQ n Λ u).Iso (iteratedStandard C hQ n Λ u (blockContent u)) :=
  (rowLoading_gradedEquiv C hQ n Λ u).some

/-- **Proposition 5.6 for the standard modules of Definition 5.1** (Webster,
arXiv:1309.3796v2). For every virtual projective class `x` of black content `|u|`, the graded
Hom from `x` into the standard module at the row loading of `u`, with the grading variable sent
to `v⁻¹`, is the componentwise form of `F_{u_1} v_{λ_1} ⊗ ⋯ ⊗ F_{u_n} v_{λ_n}` with the image
of `x` under `η`, read in the bar coproduct convention. -/
theorem rowStandard_projectiveCharacter_eq (n : ℕ) (Λ : Fin n → I →₀ ℕ) (u : Fin n → List I)
    (wt : Fin n → Dom R) (hwt : ∀ r i, (Λ r i : ℤ) = (wt r).1 (R.coroot i))
    (x : tensorProjectiveGroup C hQ Λ (blockContent u)) :
    haveI := tensorProductAlgebra_finite Λ (blockContent u) hQ
    KLGamma.qToV (projectiveCharacter _ (rowStandard C hQ n Λ u) x) =
      TensorPairing.orderedFactorwise hR wt (wordTensor C wt u)
        ((tensorCoproductEquiv hR wt).symm
          (tensorModuleEquiv C hQ hR Λ wt hwt
            (DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ) (blockContent u) x) :
              TensorSpace wt)) := by
  let := tensorProductAlgebra_finite Λ (blockContent u) hQ
  rw [projectiveCharacter_congr _ (rowStandardIso C hQ n Λ u)]
  exact iteratedStandardTest_eq C hQ hR n Λ u wt hwt (blockContent u) x

end Categorification.Stendhal.FirstWeight
