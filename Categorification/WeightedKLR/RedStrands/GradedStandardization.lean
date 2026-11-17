/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicInputGrading
import Categorification.WeightedKLR.RedStrands.ParabolicStandardGrading
import Categorification.KLR.Crystal.GradedIndShuffle

/-!
# Graded standardization and its shuffle character

Webster, arXiv:1309.3796v2, §5, standardization and Theorem 5.8.
A finite graded module for the earlier tensor block and final cyclotomic
factor gives a finite graded module for the entire tensor block. On an
ordered loading its character is given by the graded parabolic shuffle
lemma of Khovanov–Lauda I, arXiv:0803.4121v2, §2.6, Lemma 2.20.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded DirectSum
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w
variable {I : Type} [DecidableEq I] {k : Type w} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ)
  (G : GradingDatum (stendhalQ Q Λ)) (θ β : Multiset I) (hsym : KLRSymm Q)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "𝓣" => tensorProductGrade G (θ+β)
local notation "S" => stendhalQ Q Λ
variable (N : GFin (tensorGrading (tensorProductGrade (restrictRedGrading Q Λ G) θ)
  (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β)))
local notation "input" => parabolicInputGFin Λ G θ β N
local notation "raw" => G.indParabolicGFin (stendhalQ_swap_symm Q Λ hsym) (input)
local notation "Wsh" => ParabolicShuffle Q Λ θ β N.carrier
local notation "eₜ" => parabolicAffineTensorProjection (P := Q) Λ θ β

/-- Standardization of a finite graded module over the tensor product of the
earlier red block and the final cyclotomic block (Webster, §5). -/
def standardizationGFin : GFin 𝓣 := by
  let ℳ : ℤ → Submodule k Wsh := (raw).grading
  let : Decomposition ℳ := (raw).decomposition
  let : SetLike.GradedSMul (G.grade (α+δ)) ℳ := (raw).gradedSMul
  let : FiniteDimensional k Wsh := (raw).finiteDimensional
  exact parabolicStandardGFin Λ G θ β N.carrier hsym ℳ

/-- Every ordered loading has precisely the graded fixed subspace from
the affine induction before projection. -/
def standardizationFixedEquiv (s : Seq (α+δ)) (ho : IsRedOrdered s) :
    idem (raw).grading (e (Q := S) s) ≃ᵍ[k]
      idem (standardizationGFin Λ G θ β hsym N).grading ((eₜ) (e s)) := by
  let ℳ : ℤ → Submodule k Wsh := (raw).grading
  let : Decomposition ℳ := (raw).decomposition
  let : SetLike.GradedSMul (G.grade (α+δ)) ℳ := (raw).gradedSMul
  let : FiniteDimensional k Wsh := (raw).finiteDimensional
  exact parabolicStandardFixedEquiv Λ G θ β N.carrier hsym ℳ s ho

/-- At an ordered loading, the graded character of the tensor product
module is the sum of the shifted input characters indexed by parabolic
shuffles (Webster, §5, and KL I, Lemma 2.20). -/
theorem gdimPoly_standardization (s : Seq (α+δ)) (ho : IsRedOrdered s) :
    gdimPoly (idem (standardizationGFin Λ G θ β hsym N).grading
      (TensorProductAlgebra.mk Q Λ (θ+β) (StendhalAlgebra.e
        (Seq.cast (parabolicInputWeights_add (ℓ := ℓ) θ β) s) ((isRedOrdered_cast_iff _ s).mpr ho)))) =
      ∑ u : TypeA.Shuffle (Seq.card_add' α δ), LaurentPolynomial.T (G.indShuffleDegree u s) *
        gdimPoly (idem (input).grading (concatIdem (Q := S) (u.1 • s))) := by
  rw [← parabolicAffineTensorProjection_e Λ θ β s ho]
  exact (gdimPoly_congr (standardizationFixedEquiv Λ G θ β hsym N s ho)).symm.trans
    (G.gdimPoly_ind_shuffle (stendhalQ_swap_symm Q Λ hsym) (input) s)

end Categorification.Stendhal
