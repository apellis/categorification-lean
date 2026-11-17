/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.OrderedShuffleGrading
import Categorification.WeightedKLR.RedStrands.ParabolicShuffleDescent
import Categorification.WeightedKLR.RedStrands.StendhalTensorGrading

/-!
# The graded standardization module

Webster, arXiv:1309.3796v2, §5, standardization and Theorem 5.8.
The descended tensor-product action on the ordered quotient of parabolic
induction is graded. Each ordered idempotent has the same graded vector
space in the quotient as in the affine induced module.
-/

noncomputable section
namespace Categorification.Stendhal
open KLR KLRAlgebra Categorification.Graded DirectSum
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Standard
universe w
variable {J : Type} [DecidableEq J] {K : Type w} [Field K] {ℓ : ℕ}
  {P : J → J → MvPolynomial (Fin 2) K} (Λ : Fin (ℓ+1) → J →₀ ℕ)
  (G : GradingDatum (stendhalQ P Λ)) (θ β : Multiset J)
  (N : Type w) [AddCommGroup N] [Module K N] [Module (parabolicFactorAlgebra P Λ θ β) N]
  [IsScalarTower K (parabolicFactorAlgebra P Λ θ β) N] (hsym : KLRSymm P)
local notation "α" => Multiset.map (addRedColor ℓ) (stendhalWeight ℓ θ)
local notation "δ" => Multiset.map (Sum.map (id : J → J) (fun _ : Fin 1 => Fin.last ℓ)) (stendhalWeight 1 β)
local notation "Wsh" => ParabolicShuffle P Λ θ β N
local notation "H" => parabolicInputWeights_add (ℓ := ℓ) θ β
local notation "𝓣" => tensorProductGrade G (θ+β)
local notation "ord" => parabolicOrderedLoadings (ℓ := ℓ) θ β
local notation "σ" => parabolicStandardAction P Λ θ β N hsym
/-- The affine projection after adding the two standardization input weights. -/
abbrev parabolicAffineTensorProjection := (stendhalTensorProjection (Q := P) Λ (θ+β)).comp
  (castKLR (stendhalQ P Λ) (H)).toAlgHom
local notation "π" => parabolicAffineTensorProjection (P := P) Λ θ β
omit [DecidableEq J] in
/-- Equality of the total weight preserves the order of all red labels. -/
theorem isRedOrdered_cast_iff {m : ℕ} {μ μ' : Multiset (J ⊕ Fin m)} (h : μ=μ') (s : Seq μ) :
    IsRedOrdered (Seq.cast h s) ↔ IsRedOrdered s := by cases h; rfl

/-- Projection of a relabelled ordered boundary in the two-block affine algebra. -/
theorem parabolicAffineTensorProjection_e (s : Seq (α+δ)) (hs : IsRedOrdered s) :
    (π) (e s) = TensorProductAlgebra.mk P Λ (θ+β)
      (StendhalAlgebra.e (Seq.cast (H) s) ((isRedOrdered_cast_iff (H) s).mpr hs)) := by
  change stendhalTensorProjection (Q := P) Λ (θ+β) (castKLR _ _ (e s)) = _
  rw [castKLR_e,stendhalTensorProjection_e]

private theorem parabolicProjection_grade_lift (d : ℤ) (t) (ht : t ∈ 𝓣 d) :
    ∃ a ∈ G.grade (α+δ) d, (π) a=t := by
  obtain ⟨z,hz,h⟩ := stendhalTensorProjection_grade_lift Λ G (θ+β) ht
  exact ⟨castKLR (stendhalQ P Λ) (H).symm z,G.castKLR_mem_grade _ hz,
    (congrArg (stendhalTensorProjection (Q := P) Λ (θ+β)) (castKLR_castAlg_symm (H) z)).trans h⟩

private theorem parabolicProjection_act (a) (x : Wsh) :
    (σ) ((π) a) ((excludedSpace (parabolicShuffleAction P Λ θ β N) (ord)).mkQ x) =
      (excludedSpace (parabolicShuffleAction P Λ θ β N) (ord)).mkQ (a • x) := by
  rw [show (σ) ((π) a) = _ from parabolicStandardAction_affine P Λ θ β N hsym a]
  rfl

variable (ℳ : ℤ → Submodule K (ParabolicShuffle P Λ θ β N)) [Decomposition ℳ]
  [SetLike.GradedSMul (G.grade ((stendhalWeight ℓ θ).map (addRedColor ℓ) +
    (stendhalWeight 1 β).map (Sum.map (id : J → J) (fun _ : Fin 1 => Fin.last ℓ)))) ℳ] [FiniteDimensional K (ParabolicShuffle P Λ θ β N)]

/-- The finite graded module over the tensor product algebra carried by
the ordered quotient of a finite graded parabolic induction. -/
def parabolicStandardGFin : GFin 𝓣 :=
  orderedShuffleGFin G (ord) Wsh ℳ 𝓣 (π) (σ) (parabolicProjection_act Λ θ β N hsym)
    (parabolicProjection_grade_lift Λ G θ β)

/-- The ordered quotient map is an isomorphism on an ordered word in each
degree, before and after passing to the tensor product action. -/
def parabolicStandardFixedEquiv (s : Seq (α+δ)) (ho : IsRedOrdered s) :
    idem ℳ (e (Q := stendhalQ P Λ) s) ≃ᵍ[K]
      idem (parabolicStandardGFin Λ G θ β N hsym ℳ).grading ((π) (e s)) :=
  orderedShuffleFixedGradedEquiv G (ord) Wsh ℳ 𝓣 (π) (σ) (parabolicProjection_act Λ θ β N hsym)
    (parabolicProjection_grade_lift Λ G θ β) s (by classical simpa [parabolicOrderedLoadings] using ho)

end Standard

end Categorification.Stendhal
