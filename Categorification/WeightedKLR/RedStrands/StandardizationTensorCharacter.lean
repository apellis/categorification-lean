/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.GradedStandardization

/-!
# Shuffle characters for standardization of external tensor products

Webster, arXiv:1309.3796v2, §5, standardization; Khovanov–Lauda I,
arXiv:0803.4121v2, §2.6, Lemma 2.20. The character of an external
tensor product after standardization is the weighted sum of the products
of its two boundary characters at the corresponding split loadings.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w
variable {I : Type} [DecidableEq I] {k : Type w} [Field k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (ℓ+1) → I →₀ ℕ)
  (G : GradingDatum (stendhalQ Q Λ)) (θ β : Multiset I) (hsym : KLRSymm Q)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "S" => stendhalQ Q Λ
variable (X : GFin (tensorProductGrade (restrictRedGrading Q Λ G) θ))
  (Y : GFin (CycKLR.grade (restrictBlackGrading Q Λ G) (Λ (Fin.last ℓ)) β))
local notation "N" => X.extTensor Y

/-- The homogeneous word multiplicities of the standardization of two
finite graded modules are the products of the word multiplicities in the
two factors, with the affine degrees of the shuffles. -/
theorem gdimPoly_standardization_extTensor (s : Seq (α+δ)) (ho : IsRedOrdered s) :
    gdimPoly (idem (standardizationGFin Λ G θ β hsym (N)).grading
      (TensorProductAlgebra.mk Q Λ (θ+β) (StendhalAlgebra.e
        (Seq.cast (parabolicInputWeights_add (ℓ := ℓ) θ β) s) ((isRedOrdered_cast_iff _ s).mpr ho)))) =
      ∑ u : ShuffleOf α δ s, LaurentPolynomial.T (G.indShuffleDegree u.1 s) *
        (gdimPoly (idem X.grading (parabolicPrefixProjection Q Λ θ (e u.split.1))) *
          gdimPoly (idem Y.grading (parabolicLastCyclotomic Q Λ β (e u.split.2)))) := by
  classical
  rw [← parabolicAffineTensorProjection_e Λ θ β s ho,
    ← gdimPoly_congr (standardizationFixedEquiv Λ G θ β hsym (N) s ho),
    G.gdimPoly_ind_shuffle_admissible]
  refine Finset.sum_congr rfl fun u _ => ?_
  apply congrArg (_ * ·)
  let x := parabolicPrefixProjection Q Λ θ (e u.split.1)
  let y := parabolicLastCyclotomic Q Λ β (e u.split.2)
  change gdimPoly (idem (N).grading (x ⊗ₜ[k] y)) = _
  exact gdimPoly_idem_extTensor X Y ((show IsIdempotentElem (e u.split.1 : KLRAlgebra k S α) from
    e_mul_self _).map (parabolicPrefixProjection Q Λ θ)) ((show IsIdempotentElem (e u.split.2 : KLRAlgebra k S δ) from
    e_mul_self _).map (parabolicLastCyclotomic Q Λ β))
    (redSubfamilyProjection_mem_grade Λ Fin.castSucc (Fin.castSucc_injective ℓ) G θ (G.e_mem_grade _))
    (parabolicLastCyclotomic_mem_grade Λ G β (G.e_mem_grade _))

end Categorification.Stendhal
