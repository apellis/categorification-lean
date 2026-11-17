/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicRationalAction
import Categorification.KLR.CyclotomicMixedCommutatorK0
import Categorification.KLR.Rouquier.PolynomialDegree
import Categorification.QuantumGroup.RaisingSerre

/-!
# The quantum group action on cyclotomic projectives

Kang–Kashiwara, arXiv:1102.4677v4, §6, Lemma 6.1 and Theorem 6.2.
The scalar extension sends the grading shift to the inverse indeterminate.
The presentations at the two inverse parameters agree upon reversing the
torus: in both presentations the Chevalley generators are the scalar
extensions of the same projective induction and normalized restriction.
-/

noncomputable section
namespace Categorification.KLR.CycKLR

open KLRAlgebra KLRAlgebra.AbsentColour Categorification.Graded QuantumGroup QuantumGroup.UDot
open KLGamma LieLean
open scoped TensorProduct
attribute [local instance] KLGamma.qToVAlgebra
local notation "LP" => LaurentPolynomial ℤ
local notation "L" => RatFunc ℚ

variable {k I : Type*} [Field k] [DecidableEq I] {Q : I → I → MvPolynomial (Fin 2) k}
    (Λ : I → ℕ) {C : CartanDatum I} {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (RD : WeightDatum C X Y) (highest : X)
    (hΛ : ∀ i, (Λ i : ℤ) = RD.pair (RD.iY i) highest) (hP : IsRouquierQ C Q)

local notation "G" => hP.gradingDatum
local notation "D" => C.toLusztig
local notation "R" => projectiveRootDatum RD
local notation "M" => projectiveK0Q G Λ
local notation "B" => Module.End.baseChangeHom LP L (projectiveK0 G Λ)
local notation "E" => fun i : I => B (raise G Λ i hP.klrSymm hP.polyInY_leading C)
local notation "F" => fun i : I => B (lower G Λ i)
local notation "κ" => torusQ G Λ RD highest
local notation "q" => projectiveParameter
local notation "v" => (RatFunc.X : L)

include hΛ in
private theorem projectivePreRelations : LieLean.QuantumGroup.PreRelations R q E F κ where
  K_mul_E := torusQ_raise G Λ RD highest hP.klrSymm hP.polyInY_leading
  K_mul_F := torusQ_lower G Λ RD highest
  E_mul_F i j := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      exact rational_commutator G Λ RD highest hP.klrSymm hP.polyInY_leading hΛ
        (hP.polyInY_degree_pair RD) (fun i => (two_mul_di C i).symm) i
    · rw [ite_eq_right hij, sub_eq_zero]
      have H := congrArg (fun a : Module.End LP (projectiveK0 G Λ) => B a)
        (raise_lower_commute_of_ne G Λ i j hP.klrSymm hP.polyInY_leading C hij rfl).eq
      simpa only [map_mul] using H

include hΛ in
/-- The actual cyclotomic projective functors satisfy the Drinfeld–Jimbo
relations on the whole rational Grothendieck group (Kang–Kashiwara, Lemma 6.1). -/
theorem projectiveRelations : LieLean.QuantumGroup.Relations R q E F κ where
  toPreRelations := projectivePreRelations Λ RD highest hΛ hP
  serre_E i j hij := by
    apply Categorification.QuantumGroup.raisingSerre_of_cyclic («D» := D) («R» := R) («v» := q)
      («M» := M) (e := E) (f := F) («κ» := κ) (w := projectiveVacuum G Λ)
      (projectivePreRelations Λ RD highest hΛ hP) (Units.ne_zero (vQ⁻¹ : Lˣ)) _ _ hij
    · exact raiseQ_vacuum G Λ hP.klrSymm hP.polyInY_leading (C := C)
    · exact eq_top_of_lower_stable hP Λ
  serre_F i j hij := rational_lower_serre (i := i) (j := j) Λ hP hij

/-- The scalar-extended cyclotomic action with grading-shift parameter
(Kang–Kashiwara, arXiv:1102.4677v4, Theorem 6.2). -/
def projectiveRepresentation : LieLean.QuantumGroup R q →ₐ[L] Module.End L M :=
  LieLean.QuantumGroup.lift (projectiveRelations Λ RD highest hΛ hP)

@[simp] theorem projectiveRepresentation_E (i : I) :
    projectiveRepresentation Λ RD highest hΛ hP (LieLean.QuantumGroup.E R q i) = E i :=
  LieLean.QuantumGroup.lift_E _ _

@[simp] theorem projectiveRepresentation_F (i : I) :
    projectiveRepresentation Λ RD highest hΛ hP (LieLean.QuantumGroup.F R q i) = F i :=
  LieLean.QuantumGroup.lift_F _ _

@[simp] theorem projectiveRepresentation_K (y : Y) :
    projectiveRepresentation Λ RD highest hΛ hP (LieLean.QuantumGroup.K R q y) = κ (.ofAdd y) :=
  LieLean.QuantumGroup.lift_K _ _

include hΛ in
private theorem projectiveRelationsX :
    LieLean.QuantumGroup.Relations R v E F ((κ).comp invMonoidHom) := by
  have he : q⁻¹ = v := by simp [projectiveParameter]
  rw [← he]
  exact Categorification.QuantumGroup.relations_inv (projectiveRelations Λ RD highest hΛ hP)

/-- The cyclotomic action at the highest-weight library's parameter `RatFunc.X`.
Its torus evaluates the negative coweight in the grading-shift convention. -/
def projectiveRepresentationX : LieLean.QuantumGroup R v →ₐ[L] Module.End L M :=
  LieLean.QuantumGroup.lift (projectiveRelationsX Λ RD highest hΛ hP)

@[simp] theorem projectiveRepresentationX_E (i : I) :
    projectiveRepresentationX Λ RD highest hΛ hP (LieLean.QuantumGroup.E R v i) = E i :=
  LieLean.QuantumGroup.lift_E _ _

@[simp] theorem projectiveRepresentationX_F (i : I) :
    projectiveRepresentationX Λ RD highest hΛ hP (LieLean.QuantumGroup.F R v i) = F i :=
  LieLean.QuantumGroup.lift_F _ _

@[simp] theorem projectiveRepresentationX_K (y : Y) :
    projectiveRepresentationX Λ RD highest hΛ hP (LieLean.QuantumGroup.K R v y) =
      κ (.ofAdd (-y)) := LieLean.QuantumGroup.lift_K _ _

/-- In the indeterminate-parameter presentation the vacuum is a highest-weight
torus eigenvector with character `y ↦ ⟨y, Λ⟩`. -/
theorem projectiveRepresentationX_K_vacuum (y : Y) :
    projectiveRepresentationX Λ RD highest hΛ hP (LieLean.QuantumGroup.K R v y)
      (projectiveVacuum G Λ) = v ^ RD.pair y highest • projectiveVacuum G Λ := by
  rw [projectiveRepresentationX_K, torusQ_vacuum]
  simp [projectiveParameter]

end Categorification.KLR.CycKLR
