/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.IdempotentQuotientLayerCorner
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyLayer

/-!
# The corner of an ordered loading in a layer of a partial standardization

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, trace half (Claim B at one loading).

The partial standardization `𝕊(N)` of a cut is `Ind N` modulo the kernel of `P = Σ e(t)` over
the ordered loadings `t`. For an ordered loading `l`, `e(l) P = e(l) = P e(l)`
(`cutExcludedIdem_e_smul`, `e_smul_cutExcludedIdem`). Hence the layer map
`F_c / F_{c-1} → F_c(𝕊) / F_{c-1}(𝕊)` is injective on the corner `e(l) (F_c / F_{c-1})`
and maps it onto the corner `e(l) (F_c(𝕊) / F_{c-1}(𝕊))` (`cutLoadingLayerEquiv`).

Webster's proof does not spell this out. Any commutative ring `k`, symmetric `Q`. No new
hypothesis.

## Main results

* `Stendhal.cutExcludedIdem_e_smul`, `Stendhal.e_smul_cutExcludedIdem`,
  `Stendhal.mapQ_e_eq_cutStandardAction`, `Stendhal.cutLoadingLayerEquiv`,
  `Stendhal.cutLoadingLayerEquiv_apply`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA

variable {I k : Type*} [DecidableEq I] [CommRing k] {a r : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin (a + r) → I →₀ ℕ} {θ β : Multiset I}

local notation "α" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd r)) (stendhalWeight a θ)
local notation "δ" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd a)) (stendhalWeight r β)
local notation "S" => stendhalQ Q Λ

variable {N : Type*} [AddCommGroup N] [Module k N] [Module (cutFactorAlgebra Q Λ θ β) N]
  [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N]

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- `P e(l) = e(l)` for an ordered loading `l`. -/
theorem cutExcludedIdem_e_smul (l : Seq (α + δ))
    (hl : l ∈ cutOrderedLoadings (a := a) (r := r) θ β)
    (y : CutShuffle Q Λ θ β N) :
    cutExcludedIdem Q Λ θ β N ((e l : KLRAlgebra k S (α + δ)) • y) =
      (e l : KLRAlgebra k S (α + δ)) • y := by
  change (eSum S (cutOrderedLoadings (a := a) (r := r) θ β) : KLRAlgebra k S (α + δ)) •
    ((e l : KLRAlgebra k S (α + δ)) • y) = _
  rw [smul_smul, eSum_mul_e]
  simp only [hl, ↓reduceIte]

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- `e(l) P = e(l)` for an ordered loading `l`. -/
theorem e_smul_cutExcludedIdem (l : Seq (α + δ))
    (hl : l ∈ cutOrderedLoadings (a := a) (r := r) θ β)
    (y : CutShuffle Q Λ θ β N) :
    (e l : KLRAlgebra k S (α + δ)) • cutExcludedIdem Q Λ θ β N y =
      (e l : KLRAlgebra k S (α + δ)) • y := by
  change (e l : KLRAlgebra k S (α + δ)) •
    ((eSum S (cutOrderedLoadings (a := a) (r := r) θ β) : KLRAlgebra k S (α + δ)) • y) = _
  rw [smul_smul, e_mul_eSum]
  simp only [hl, ↓reduceIte]

variable (hQ : KLRSymm Q)

/-- On `V / ker P`, the map induced by `e(l)` is the action of `e(l)` on `𝕊(N)`. -/
theorem mapQ_e_eq_cutStandardAction (z : KLRAlgebra k S (α + δ))
    (hK : ∀ v ∈ LinearMap.ker (cutExcludedIdem Q Λ θ β N),
      DistribSMul.toLinearMap k (CutShuffle Q Λ θ β N) z v ∈
        LinearMap.ker (cutExcludedIdem Q Λ θ β N)) :
    (LinearMap.ker (cutExcludedIdem Q Λ θ β N)).mapQ
        (LinearMap.ker (cutExcludedIdem Q Λ θ β N))
        (DistribSMul.toLinearMap k (CutShuffle Q Λ θ β N) z) hK =
      cutStandardAction Q Λ θ β N hQ (affineToTensor Q Λ θ β z) := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
  exact (cutStandardAction_affineToTensor (N := N) Q Λ θ β hQ z y).symm

/-- **Claim B at an ordered loading** (Webster v3, Lemma 7.19, trace half): the corner
`e(l) (F_c / F_{c-1})` of the layer of `Ind N` is isomorphic, by the layer map, to the corner
`e(l) (F_c(𝕊) / F_{c-1}(𝕊))` of the layer of the partial standardization. -/
def cutLoadingLayerEquiv (l : Seq (α + δ)) (hl : l ∈ cutOrderedLoadings (a := a) (r := r) θ β)
    (n c : ℕ) :
    LinearMap.range (indLayerAct (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c) ≃ₗ[k]
      LinearMap.range (cutLayerAct hQ (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c) :=
  (idemLayerCornerEquiv (cutExcludedIdem Q Λ θ β N)
      (DistribSMul.toLinearMap k (CutShuffle Q Λ θ β N) (e l : KLRAlgebra k S (α + δ)))
      cutExcludedIdem_idem (cutExcludedIdem_mem Q Λ θ β N n c)
      (cutExcludedIdem_mem_lower Q Λ θ β N n c) _ _ (cutExcludedIdem_e_smul l hl)
      (e_smul_cutExcludedIdem l hl)).trans
    (LinearEquiv.ofEq _ _ (congrArg LinearMap.range (subLayerAct_congr
      (mapQ_e_eq_cutStandardAction hQ _ _) _ _ _ _)))

theorem cutLoadingLayerEquiv_apply (l : Seq (α + δ))
    (hl : l ∈ cutOrderedLoadings (a := a) (r := r) θ β) (n c : ℕ)
    (y : LinearMap.range (indLayerAct (N := N) (preservesMackeyFilt_e (Q := S) (n := n)
        (n'' := Multiset.card α) l) c)) :
    ((cutLoadingLayerEquiv hQ l hl n c).toLinearMap y : SubLayer _ _) =
      cutMackeyLayerMap Q Λ θ β N n c (y : SubLayer _ _) :=
  rfl

end Categorification.Stendhal
