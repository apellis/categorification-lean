/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicInputGrading
import Categorification.WeightedKLR.RedStrands.ParabolicStandardGrading
import Categorification.WeightedKLR.RedStrands.PartialStandardizationDescent
import Categorification.WeightedKLR.RedStrands.BraidedStendhal
import Categorification.KLR.Crystal.GradedIndShuffle

/-!
# Graded partial standardization at a cut

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1, the
partial standardization functors `𝕊^{λ_1…λ_a; λ_{a+1}…λ_{a+r}}` after Definition 5.4, with
the grading of §5 (Theorem 5.8); used in §7.3 (Lemma 7.19 and the proof of Proposition 7.20)
for the block `(μ, μ*)` with two red strands.

The partial standardization at a cut (`CutStandard`) of a module `N` over
`T^{λ_1…λ_a}(θ) ⊗ T^{λ_{a+1}…λ_{a+r}}(β)` is the affine induced module modulo the part
supported on loadings with red strands out of order. For a finite graded `N` (with the
tensor product of the diagram gradings of the two blocks, restricted from the grading `G` of
all strands) it is a finite graded module over `T^λ(θ + β)` (`cutStandardGFin`). This is the
graded standardization of `GradedStandardization` (one red strand in the second block, whose
algebra is the cyclotomic quotient) for an arbitrary number `r` of red strands in the second
block. At an ordered loading its graded dimension is the sum over the shuffles of the input
dimensions with the affine shuffle degrees (`gdimPoly_cutStandardization`), and for an
external tensor product `X ⊠ Y` the sum of products of the dimensions of `X` and `Y` at the
two split loadings (`gdimPoly_cutStandardization_extTensor`): Khovanov–Lauda I,
arXiv:0803.4121v2, §2.6, Lemma 2.20.

## Main definitions

* `Stendhal.cutPrefixGrading`, `Stendhal.cutSuffixGrading`: the restricted gradings.
* `Stendhal.cutInputGFin`: the graded input module of affine induction.
* `Stendhal.cutStandardGFin`: the graded partial standardization at a cut.

## Main results

* `Stendhal.cutInputMap_mem_grade`: the affine quotient map of the two blocks is graded.
* `Stendhal.cutStandardFixedEquiv`: an ordered loading has the same graded space before and
  after excluding the unordered loadings.
* `Stendhal.gdimPoly_cutStandardization`, `Stendhal.gdimPoly_cutStandardization_extTensor`.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded DirectSum
open scoped TensorProduct
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe w
variable {I : Type} [DecidableEq I] {k : Type w} [Field k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} (Λ : Fin (a + r) → I →₀ ℕ)
  (G : GradingDatum (stendhalQ Q Λ)) (θ β : Multiset I) (hsym : KLRSymm Q)
local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

/-- The diagram grading of the first block `λ_1, …, λ_a` of a cut, restricted from `G`. -/
abbrev cutPrefixGrading : GradingDatum (stendhalQ Q (Λ ∘ Fin.castAdd r)) :=
  redSubfamilyGrading Λ (Fin.castAdd r) (Fin.castAdd_injective a r) G

/-- The diagram grading of the second block `λ_{a+1}, …, λ_{a+r}` of a cut, restricted
from `G`. -/
abbrev cutSuffixGrading : GradingDatum (stendhalQ Q (Λ ∘ Fin.natAdd a)) :=
  redSubfamilyGrading Λ (Fin.natAdd a) (Fin.natAdd_injective r a) G

local notation "Earlier" => tensorProductGrade (cutPrefixGrading Λ G) θ
local notation "Later" => tensorProductGrade (cutSuffixGrading Λ G) β
local notation "In" => tensorGrading (G.grade α) (G.grade δ)
local notation "Out" => tensorGrading (Earlier) (Later)

/-- The affine quotient map onto the tensor product of the algebras of the two blocks is
graded. -/
theorem cutInputMap_mem_grade {d : ℤ} {z} (hz : z ∈ In d) :
    cutInputMap Q Λ θ β z ∈ Out d := by
  induction hz using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨i, j, x, y, rfl, hx, hy, rfl⟩ := ht
    exact tmul_mem_tensorGrading
      (redSubfamilyProjection_mem_grade Λ (Fin.castAdd r) (Fin.castAdd_injective a r) G θ hx)
      (redSubfamilyProjection_mem_grade Λ (Fin.natAdd a) (Fin.natAdd_injective r a) G β hy)
  | zero => simp
  | add a b _ _ ha hb => simpa using add_mem ha hb
  | smul scalar a _ ha =>
    rw [AlgHom.map_smul_of_tower]
    exact Submodule.smul_mem _ scalar ha

/-- The restriction of a finite graded module over the two blocks along the affine quotient
map. Its carrier and graded pieces are those of the module. -/
def cutInputGFin (N : GFin (Out)) : GFin (In) := by
  let V := CutInput Q Λ θ β N.carrier
  let ℳ : ℤ → Submodule k V := N.grading
  let : DirectSum.Decomposition ℳ := N.decomposition
  let : SetLike.GradedSMul (In) ℳ := ⟨fun i j a x ha hx => by
    change cutInputMap Q Λ θ β a • (x : N.carrier) ∈ N.grading (i + j)
    exact N.gradedSMul.smul_mem (cutInputMap_mem_grade Λ G θ β ha) hx⟩
  let : FiniteDimensional k V := N.finiteDimensional
  exact {carrier := V, grading := ℳ}

local notation "H" => cutInputWeights_add (a := a) (r := r) θ β
local notation "𝓣" => tensorProductGrade G (θ + β)
local notation "ord" => cutOrderedLoadings (a := a) (r := r) θ β

/-- The affine projection of the two blocks to `T^λ(θ + β)`, after adding the weights. -/
abbrev cutAffineTensorProjection := (stendhalTensorProjection (Q := Q) Λ (θ + β)).comp
  (castKLR (stendhalQ Q Λ) (H)).toAlgHom
local notation "π" => cutAffineTensorProjection (Q := Q) Λ θ β

/-- Projection of an ordered loading of the two blocks. -/
theorem cutAffineTensorProjection_e (s : Seq (α + δ)) (hs : IsRedOrdered s) :
    (π) (e s) = TensorProductAlgebra.mk Q Λ (θ + β)
      (StendhalAlgebra.e (Seq.cast (H) s) ((isRedOrdered_cast_iff (H) s).mpr hs)) := by
  change stendhalTensorProjection (Q := Q) Λ (θ + β) (castKLR _ _ (e s)) = _
  rw [castKLR_e, stendhalTensorProjection_e]

private theorem cutProjection_grade_lift (d : ℤ) (t) (ht : t ∈ 𝓣 d) :
    ∃ x ∈ G.grade (α + δ) d, (π) x = t := by
  obtain ⟨z, hz, h⟩ := stendhalTensorProjection_grade_lift Λ G (θ + β) ht
  exact ⟨castKLR (stendhalQ Q Λ) (H).symm z, G.castKLR_mem_grade _ hz,
    (congrArg (stendhalTensorProjection (Q := Q) Λ (θ + β)) (castKLR_castAlg_symm (H) z)).trans h⟩

section Standard

variable (N : Type w) [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]
local notation "Wsh" => CutShuffle Q Λ θ β N
local notation "σ" => cutStandardAction Q Λ θ β N hsym

private theorem cutProjection_act (x) (y : Wsh) :
    (σ) ((π) x) ((excludedSpace (cutShuffleAction Q Λ θ β N) (ord)).mkQ y) =
      (excludedSpace (cutShuffleAction Q Λ θ β N) (ord)).mkQ (x • y) := by
  rw [show (σ) ((π) x) = _ from cutStandardAction_affine Q Λ θ β N hsym x]
  rfl

variable (ℳ : ℤ → Submodule k (CutShuffle Q Λ θ β N)) [Decomposition ℳ]
  [SetLike.GradedSMul (G.grade
    ((stendhalWeight a θ).map (Sum.map (id : I → I) (Fin.castAdd r)) +
      (stendhalWeight r β).map (Sum.map (id : I → I) (Fin.natAdd a)))) ℳ]
  [FiniteDimensional k (CutShuffle Q Λ θ β N)]

/-- The finite graded module over `T^λ(θ + β)` carried by the ordered quotient of a finite
graded affine induced module of the two blocks. -/
def cutStandardOfGrading : GFin 𝓣 :=
  orderedShuffleGFin G (ord) Wsh ℳ 𝓣 (π) (σ) (cutProjection_act Λ θ β hsym N)
    (cutProjection_grade_lift Λ G θ β)

/-- On an ordered loading the ordered quotient map is a graded isomorphism. -/
def cutStandardOfGradingFixedEquiv (s : Seq (α + δ)) (ho : IsRedOrdered s) :
    idem ℳ (e (Q := stendhalQ Q Λ) s) ≃ᵍ[k]
      idem (cutStandardOfGrading Λ G θ β hsym N ℳ).grading ((π) (e s)) :=
  orderedShuffleFixedGradedEquiv G (ord) Wsh ℳ 𝓣 (π) (σ) (cutProjection_act Λ θ β hsym N)
    (cutProjection_grade_lift Λ G θ β) s
    (by classical simpa [cutOrderedLoadings] using ho)

end Standard

variable (N : GFin (tensorGrading (tensorProductGrade (cutPrefixGrading Λ G) θ)
  (tensorProductGrade (cutSuffixGrading Λ G) β)))
local notation "input" => cutInputGFin Λ G θ β N
local notation "raw" => G.indParabolicGFin (stendhalQ_symm Q Λ hsym) (input)

/-- **The graded partial standardization at a cut** (Webster, arXiv:1309.3796v3, §5.1): a
finite graded module over `T^{λ_1…λ_a}(θ) ⊗ T^{λ_{a+1}…λ_{a+r}}(β)` gives a finite graded
module over `T^λ(θ + β)`. Its carrier is `CutStandard` of the carrier of `N`. -/
def cutStandardGFin : GFin 𝓣 := by
  let ℳ : ℤ → Submodule k (CutShuffle Q Λ θ β N.carrier) := (raw).grading
  let : Decomposition ℳ := (raw).decomposition
  let : SetLike.GradedSMul (G.grade (α + δ)) ℳ := (raw).gradedSMul
  let : FiniteDimensional k (CutShuffle Q Λ θ β N.carrier) := (raw).finiteDimensional
  exact cutStandardOfGrading Λ G θ β hsym N.carrier ℳ

/-- Every ordered loading has the graded space of the affine induced module. -/
def cutStandardFixedEquiv (s : Seq (α + δ)) (ho : IsRedOrdered s) :
    idem (raw).grading (e (Q := S) s) ≃ᵍ[k]
      idem (cutStandardGFin Λ G θ β hsym N).grading ((π) (e s)) := by
  let ℳ : ℤ → Submodule k (CutShuffle Q Λ θ β N.carrier) := (raw).grading
  let : Decomposition ℳ := (raw).decomposition
  let : SetLike.GradedSMul (G.grade (α + δ)) ℳ := (raw).gradedSMul
  let : FiniteDimensional k (CutShuffle Q Λ θ β N.carrier) := (raw).finiteDimensional
  exact cutStandardOfGradingFixedEquiv Λ G θ β hsym N.carrier ℳ s ho

/-- **Graded character of a partial standardization at a cut** (Webster, §5; Khovanov–Lauda I,
arXiv:0803.4121v2, §2.6, Lemma 2.20): at an ordered loading, the graded dimension is the sum
over the shuffles of the two blocks of the input dimensions with the affine shuffle degrees. -/
theorem gdimPoly_cutStandardization (s : Seq (α + δ)) (ho : IsRedOrdered s) :
    gdimPoly (idem (cutStandardGFin Λ G θ β hsym N).grading
      (TensorProductAlgebra.mk Q Λ (θ + β) (StendhalAlgebra.e
        (Seq.cast (H) s) ((isRedOrdered_cast_iff _ s).mpr ho)))) =
      ∑ u : TypeA.Shuffle (Seq.card_add' α δ), LaurentPolynomial.T (G.indShuffleDegree u s) *
        gdimPoly (idem (input).grading (concatIdem (Q := S) (u.1 • s))) := by
  rw [← cutAffineTensorProjection_e Λ θ β s ho]
  exact (gdimPoly_congr (cutStandardFixedEquiv Λ G θ β hsym N s ho)).symm.trans
    (G.gdimPoly_ind_shuffle (stendhalQ_symm Q Λ hsym) (input) s)

section ExtTensor

variable (X : GFin (tensorProductGrade (cutPrefixGrading Λ G) θ))
  (Y : GFin (tensorProductGrade (cutSuffixGrading Λ G) β))

/-- **Graded character of the partial standardization of an external tensor product**: at an
ordered loading `s`, the graded dimension of `𝕊(X ⊠ Y)` is the sum over the shuffles `u`
compatible with `s` of the products of the graded dimensions of `X` and `Y` at the projections
of the two split loadings, with the affine shuffle degrees (Webster, arXiv:1309.3796v3, §5.1;
Khovanov–Lauda I, arXiv:0803.4121v2, §2.6, Lemma 2.20). -/
theorem gdimPoly_cutStandardization_extTensor (s : Seq (α + δ)) (ho : IsRedOrdered s) :
    gdimPoly (idem (cutStandardGFin Λ G θ β hsym (X.extTensor Y)).grading
      (TensorProductAlgebra.mk Q Λ (θ + β) (StendhalAlgebra.e
        (Seq.cast (H) s) ((isRedOrdered_cast_iff _ s).mpr ho)))) =
      ∑ u : ShuffleOf α δ s, LaurentPolynomial.T (G.indShuffleDegree u.1 s) *
        (gdimPoly (idem X.grading (cutPrefixProjection Q Λ θ (e u.split.1))) *
          gdimPoly (idem Y.grading (cutSuffixProjection Q Λ β (e u.split.2)))) := by
  classical
  rw [← cutAffineTensorProjection_e Λ θ β s ho,
    ← gdimPoly_congr (cutStandardFixedEquiv Λ G θ β hsym (X.extTensor Y) s ho),
    G.gdimPoly_ind_shuffle_admissible]
  refine Finset.sum_congr rfl fun u _ => ?_
  apply congrArg (_ * ·)
  let x := cutPrefixProjection Q Λ θ (e u.split.1)
  let y := cutSuffixProjection Q Λ β (e u.split.2)
  change gdimPoly (idem (X.extTensor Y).grading (x ⊗ₜ[k] y)) = _
  exact gdimPoly_idem_extTensor X Y
    ((show IsIdempotentElem (e u.split.1 : KLRAlgebra k S α) from e_mul_self _).map
      (cutPrefixProjection Q Λ θ))
    ((show IsIdempotentElem (e u.split.2 : KLRAlgebra k S δ) from e_mul_self _).map
      (cutSuffixProjection Q Λ β))
    (redSubfamilyProjection_mem_grade Λ (Fin.castAdd r) (Fin.castAdd_injective a r) G θ
      (G.e_mem_grade _))
    (redSubfamilyProjection_mem_grade Λ (Fin.natAdd a) (Fin.natAdd_injective r a) G β
      (G.e_mem_grade _))

end ExtTensor

end Categorification.Stendhal
