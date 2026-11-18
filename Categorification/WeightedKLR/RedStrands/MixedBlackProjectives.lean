/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.NormalizedBlackProjectives
import Categorification.WeightedKLR.RedStrands.TensorModuleRaising
import Categorification.WeightedKLR.RedStrands.RedLabelRootDatum
import Categorification.Algebra.Graded.KrullSchmidtUnique

/-! # Distinct-colour mixed products on graded projectives

Webster, arXiv:1309.3796v2, §4.7, Lemma 4.35, evaluated on individual
projectives. The canonical comparison of Theorem 4.38 and graded
Krull–Schmidt give the degree-preserving isomorphism class.
-/

noncomputable section
namespace Categorification.Stendhal.FirstWeight

open KLR Categorification.Graded QuantumGroup LieLean LieLean.QuantumGroup LieLean.QuantumGroup.GrandLoop
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "LP" => LaurentPolynomial ℤ

section Comparison

variable {I : Type} {k : Type*} [DecidableEq I] [Field k] [Finite I]
  {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)
  {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ)

local notation "q" => (RatFunc.X : RatFunc ℚ)
local instance : NeZero q := ⟨RatFunc.X_ne_zero⟩
local notation "G" => stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation "ι" => DirectSum.lof LP _ (tensorProjectiveGroup C hQ Λ)

private theorem blackRaise_blackLower_comm (i j : I) (hij : i ≠ j)
    (x : DirectSum (Multiset I) (tensorProjectiveGroup C hQ Λ)) :
    blackRaise G i C hQ (blackLower G j x) = blackLower G j (blackRaise G i C hQ x) := by
  let wt := redLabelWeight C ∘ Λ
  have hwt (r : Fin ℓ) (a : I) :
      (Λ r a : ℤ) = (wt r).1 ((redLabelDatum C).coroot a) :=
    (redLabelWeight_coroot C (Λ r) a).symm
  let η := tensorModuleEquiv C hQ (redLabelDatum_xRegular C) Λ wt hwt
  apply η.injective
  apply Subtype.ext
  change (η (blackRaise G i C hQ (blackLower G j x)) : TensorSpace wt) =
    (η (blackLower G j (blackRaise G i C hQ x)) : TensorSpace wt)
  dsimp only [η]
  rw [tensorModuleEquiv_E, tensorModuleEquiv_F, tensorModuleEquiv_F, tensorModuleEquiv_E]
  simpa only [map_mul, Module.End.mul_apply] using
    congrArg (fun a => tensorRepresentation wt a (η x : TensorSpace wt))
      (E_mul_F_of_ne (R := redLabelDatum C) (v := q) hij)

/-- The distinct-colour commutation of Webster, arXiv:1309.3796v2, §4.7,
Lemma 4.35, evaluated on each projective. When the restricted colour is
absent, the normalized restriction has zero projective value. -/
theorem blackRaiseProjAt_blackIndProj_iso_of_ne (i j : I) (hij : i ≠ j) (ν : Multiset I)
    (P : GProj (tensorProductGrade G ν)) :
    Nonempty ((blackRaiseProjAt G i ({j} + ν) C hQ (blackIndProj G j ν P)).Iso
      (projectiveBlockCast G
        (Multiset.erase_add_right_neg (a := i) (s := {j}) ν (by simpa using hij)).symm
        (blackIndProj G j (ν.erase i) (blackRaiseProjAt G i ν C hQ P)))) := by
  let := tensorProductAlgebra_finite Λ (({j} + ν).erase i) hQ
  let := HasGdim.of_finiteDimensional (tensorProductGrade G (({j} + ν).erase i))
  apply K0.of_eq_of_iff.mp
  apply DirectSum.of_injective (β := tensorProjectiveGroup C hQ Λ) (({j} + ν).erase i)
  change ι (({j} + ν).erase i) _ = ι (({j} + ν).erase i) _
  rw [← blackRaise_lof_of_projAt, projectiveBlockCast, lof_of_transport,
    ← blackIndK0_of G j ν, ← blackLower_lof G j ν,
    ← blackIndK0_of G j (ν.erase i), ← blackLower_lof G j (ν.erase i),
    ← blackRaise_lof_of_projAt G i ν C hQ P, blackRaise_blackLower_comm C hQ Λ i j hij]

end Comparison
end Categorification.Stendhal.FirstWeight
