/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.NormalizedBlackProjectives
import Categorification.WeightedKLR.RedStrands.TensorModuleRaising
import Categorification.Algebra.Graded.KrullSchmidtUnique
import Categorification.WeightedKLR.RedStrands.RedLabelRootDatum

/-! # Raising after terminal-red induction

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.35. On projective classes the
normalized raising operator commutes with adjoining the final highest vector.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded QuantumGroup LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification
local notation "v" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero v := ⟨RatFunc.X_ne_zero⟩

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {ℓ : ℕ} (Λ : Fin (ℓ+1) → I →₀ ℕ)

local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "G₀" => stendhalGradingDatum (Λ ∘ Fin.castSucc) hQ.gradingDatum
  (fun i => C.dot i i / 2) (dotDegree C hQ)

/-- The terminal-red case of Webster, arXiv:1309.3796v2, §4.7, Lemma 4.35,
on the integral projective Grothendieck group for weights realized in the root datum. -/
private theorem blackRaise_totalLastRedIndK0 (i : I)
    (x : DirectSum (Multiset I) (tensorProjectiveGroup C hQ (Λ ∘ Fin.castSucc))) :
    blackRaise G i C hQ (totalLastRedIndK0 C hQ Λ x) =
      totalLastRedIndK0 C hQ Λ (blackRaise G₀ i C hQ x) := by
  let wt := redLabelWeight C ∘ Λ
  have hwt (r : Fin (ℓ+1)) (a : I) :
      (Λ r a : ℤ) = (wt r).1 ((redLabelDatum C).coroot a) := (redLabelWeight_coroot C (Λ r) a).symm
  apply (tensorModuleEquiv C hQ (redLabelDatum_xRegular C) Λ wt hwt).injective
  apply Subtype.ext
  rw [tensorModuleEquiv_E, tensorModuleEquiv_lastRed, tensorModuleEquiv_lastRed,
    tensorModuleEquiv_E, tensorRepresentation_E_append, IrreducibleModule.E_smul_hwv]
  simp [appendTensor]

local notation "LP" => LaurentPolynomial ℤ
local notation "D₀" => restrictRedGrading Q Λ G
local notation "ι" => DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ)

/-- Terminal-red induction with the standard grading at both ends. -/
def redIndProj (β : Multiset I) (P : GProj (tensorProductGrade G₀ β)) :
    GProj (tensorProductGrade G β) :=
  lastRedIndProj G β ((show D₀ = G₀ from restrictRedGrading_wordGrading Λ C hQ).symm ▸ P)

/-- Terminal-red induction on the projective group with the standard grading. -/
def redIndK0 (β : Multiset I) : tensorProjectiveGroup C hQ (Λ ∘ Fin.castSucc) β →ₗ[LP]
    tensorProjectiveGroup C hQ Λ β :=
  (show K0 (tensorProductGrade G₀ β) →ₗ[LP] tensorProjectiveGroup C hQ Λ β from
    (show D₀ = G₀ from restrictRedGrading_wordGrading Λ C hQ) ▸ lastRedIndK0 G β)

omit [Finite I] in
private theorem lastRed_of_transport (D : GradingDatum (stendhalQ Q (Λ ∘ Fin.castSucc)))
    (e : D₀ = D) (β : Multiset I) (P : GProj (tensorProductGrade D β)) :
    (e ▸ lastRedIndK0 G β : K0 (tensorProductGrade D β) →ₗ[LP] _)
      (K0.of P) = K0.of (lastRedIndProj G β (e.symm ▸ P)) := by
  subst D
  exact lastRedIndK0_of G β P

omit [Finite I] in
@[simp] theorem redIndK0_of (β : Multiset I) (P : GProj (tensorProductGrade G₀ β)) :
    redIndK0 C hQ Λ β (K0.of P) = K0.of (redIndProj C hQ Λ β P) :=
  lastRed_of_transport C hQ Λ _ (show D₀ = G₀ from restrictRedGrading_wordGrading Λ C hQ) β P

omit [Finite I] in
private theorem totalLastRed_of (β : Multiset I) (P : GProj (tensorProductGrade G₀ β)) :
    totalLastRedIndK0 C hQ Λ (DirectSum.lof LP _ (tensorProjectiveGroup C hQ (Λ ∘ Fin.castSucc))
      β (K0.of P)) = ι β (K0.of (redIndProj C hQ Λ β P)) := by
  rw [totalLastRedIndK0, DirectSum.toModule_lof, LinearMap.comp_apply]
  exact congrArg _ (redIndK0_of C hQ Λ β P)

/-- In a block containing the restricted colour, Webster’s terminal-red slide
(arXiv:1309.3796v2, Lemma 4.35) lands in the block with that strand removed. -/
theorem blackRaiseProj_redIndProj_iso (i : I) (β : Multiset I)
    (P : GProj (tensorProductGrade G₀ ((Singleton.singleton i : Multiset I) + β))) :
    Nonempty ((blackRaiseProj (Q := Q) (Λ := Λ) G i β C hQ
      (redIndProj C hQ Λ ((Singleton.singleton i : Multiset I) + β) P)).Iso
      (redIndProj C hQ Λ β (blackRaiseProj (Q := Q) (Λ := Λ ∘ Fin.castSucc) G₀ i β C hQ P))) := by
  let := tensorProductAlgebra_finite Λ β hQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade G β)
  apply K0.of_eq_of_iff.mp
  apply DirectSum.of_injective (β := tensorProjectiveGroup C hQ Λ) β
  change ι _ _ = ι _ _
  rw [← blackRaiseK0_of, ← blackRaise_lof, ← totalLastRed_of,
    blackRaise_totalLastRedIndK0 C hQ Λ, blackRaise_lof, blackRaiseK0_of, totalLastRed_of]

/-- For Webster, arXiv:1309.3796v2, Lemma 4.35, normalized restriction
slides past terminal-red induction on each graded projective. -/
theorem blackRaiseProjAt_redIndProj_iso (i : I) (β : Multiset I)
    (P : GProj (tensorProductGrade G₀ β)) :
    Nonempty ((blackRaiseProjAt G i β C hQ (redIndProj C hQ Λ β P)).Iso
      (redIndProj C hQ Λ (β.erase i) (blackRaiseProjAt G₀ i β C hQ P))) := by
  let := tensorProductAlgebra_finite Λ (β.erase i) hQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade G (β.erase i))
  apply K0.of_eq_of_iff.mp
  apply DirectSum.of_injective (β := tensorProjectiveGroup C hQ Λ) (β.erase i)
  change ι _ _ = ι _ _
  rw [← blackRaise_lof_of_projAt, ← totalLastRed_of,
    blackRaise_totalLastRedIndK0 C hQ Λ, blackRaise_lof_of_projAt, totalLastRed_of]

end Categorification.Stendhal.FirstWeight
