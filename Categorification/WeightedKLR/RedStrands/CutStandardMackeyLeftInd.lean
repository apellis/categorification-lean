/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.CutStandardMackeyLayer
import Categorification.KLR.MackeyIndIdempotent

/-!
# The Mackey layers of a partial standardization, factor by factor

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19, Claim B: the layers of the Mackey
filtration of the partial standardization `𝕊(N) = Ind N / ker P` of a cut, on the image of a top
cut `ν | ν'` of the weight. By KL I, Prop. 2.18 (`MackeyIndAssoc`), the `1_{ν,ν'}`-part of the
layer of `Ind N` is `⊕_λ MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗_{R''} N)`, through the injective
maps `Ξ_λ` with independent images. The idempotent `P` of the ordered loadings acts on the image
of `Ξ_λ` through the element `P_{ν,ν'} = concatLoadIdem` of `R(ν) ⊗ R(ν')`
(`cutExcludedIdem_indMackeyLeftMap`). Hence the composite of `Ξ_λ` with the passage to `𝕊(N)`

* depends only on `P_{ν,ν'} w` (`cutMackeyLayerMap_indMackeyLeftMap_concatLoadIdem`), and
* kills exactly the `w` with `P_{ν,ν'} w = 0` (`cutMackeyLayerMap_indMackeyLeftMap_eq_zero_iff`).

So the image of `Ξ_λ` in the layer of `𝕊(N)` is `P_{ν,ν'} (MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗ N))`.

Symmetric `Q` (`KLRSymm Q`), any commutative ring `k`, any choice `σ` of reduced words for the
shuffles.
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

variable {ν ν' : Multiset (I ⊕ Fin (a + r))}

variable (Q Λ θ β) in
/-- The element `P_{ν,ν'}` of `R(ν) ⊗ R(ν')` through which the ordered loadings act on the image
of the top cut `ν | ν'`. -/
abbrev cutConcatIdem (h : α + δ = ν + ν') : TensorKLR S ν ν' :=
  concatLoadIdem S h (cutOrderedLoadings (a := a) (r := r) θ β)

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **The ordered loadings on the image of `Ξ_λ`**: `P Ξ_λ(w) = Ξ_λ(P_{ν,ν'} w)`. -/
theorem cutExcludedIdem_indMackeyLeftMap (h : α + δ = ν + ν') (q : MackeyQuad ν ν' α δ) {c : ℕ}
    (hc : Multiset.card q.β = c) (w : MackeyLeftInd S (CutInput Q Λ θ β N) q) :
    subLayerAct (cutExcludedIdem Q Λ θ β N)
        (cutExcludedIdem_mem Q Λ θ β N (Multiset.card ν) c)
        (cutExcludedIdem_mem_lower Q Λ θ β N (Multiset.card ν) c)
        (indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q hc w) =
      indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q hc
        ((cutConcatIdem Q Λ θ β h : TensorKLR S ν ν') • w) :=
  indMackeyLayerAct_eSum_indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) _ q hc w

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
theorem cutMackeyLayerMap_eq_zero_iff {n c : ℕ}
    (y : SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c)) :
    cutMackeyLayerMap Q Λ θ β N n c y = 0 ↔
      subLayerAct (cutExcludedIdem Q Λ θ β N) (cutExcludedIdem_mem Q Λ θ β N n c)
        (cutExcludedIdem_mem_lower Q Λ θ β N n c) y = 0 := by
  have hk := ker_idemLayerMap (cutExcludedIdem Q Λ θ β N) cutExcludedIdem_idem
    (cutExcludedIdem_mem Q Λ θ β N n c) (cutExcludedIdem_mem_lower Q Λ θ β N n c)
  rw [← LinearMap.mem_ker, ← LinearMap.mem_ker]
  exact SetLike.ext_iff.1 hk y

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- The passage to `𝕊(N)` does not see the difference between `y` and `P̄ y`. -/
theorem cutMackeyLayerMap_subLayerAct {n c : ℕ}
    (y : SubLayer (indMackeyFilt Q Λ θ β N n c) (indMackeyFiltLower Q Λ θ β N n c)) :
    cutMackeyLayerMap Q Λ θ β N n c
        (subLayerAct (cutExcludedIdem Q Λ θ β N) (cutExcludedIdem_mem Q Λ θ β N n c)
          (cutExcludedIdem_mem_lower Q Λ θ β N n c) y) =
      cutMackeyLayerMap Q Λ θ β N n c y := by
  rw [← sub_eq_zero, ← map_sub, cutMackeyLayerMap_eq_zero_iff, map_sub, sub_eq_zero]
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [subLayerAct_mk, subLayerAct_mk]
  congr 1
  exact Subtype.ext (cutExcludedIdem_idem (v : CutShuffle Q Λ θ β N))

omit [IsScalarTower k (cutFactorAlgebra Q Λ θ β) N] in
/-- **The image of `Ξ_λ` in `𝕊(N)` depends only on `P_{ν,ν'} w`.** -/
theorem cutMackeyLayerMap_indMackeyLeftMap_concatLoadIdem (h : α + δ = ν + ν')
    (q : MackeyQuad ν ν' α δ) {c : ℕ}
    (hc : Multiset.card q.β = c) (w : MackeyLeftInd S (CutInput Q Λ θ β N) q) :
    cutMackeyLayerMap Q Λ θ β N (Multiset.card ν) c
        (indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q hc
          ((cutConcatIdem Q Λ θ β h : TensorKLR S ν ν') • w)) =
      cutMackeyLayerMap Q Λ θ β N (Multiset.card ν) c
        (indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q hc w) := by
  exact (congrArg (cutMackeyLayerMap Q Λ θ β N (Multiset.card ν) c)
    (cutExcludedIdem_indMackeyLeftMap h q hc w)).symm.trans (cutMackeyLayerMap_subLayerAct _)

/-- **The kernel of `Ξ_λ` followed by the passage to `𝕊(N)`** is the kernel of `P_{ν,ν'}` on
`MackeyTop_λ ⊗_{R'} (MackeyBot_λ ⊗ N)`. -/
theorem cutMackeyLayerMap_indMackeyLeftMap_eq_zero_iff (h : α + δ = ν + ν') (hsym : KLRSymm S)
    {σ : Shuffle (Seq.card_add' α δ) → List ℕ}
    (hσ : ∀ u : Shuffle (Seq.card_add' α δ), IsReduced (Multiset.card (α + δ)) (σ u) ∧
      wordProd (Multiset.card (α + δ)) (σ u) = u.1)
    {c : ℕ} (q : {q : MackeyQuad ν ν' α δ // Multiset.card q.β = c})
    (w : MackeyLeftInd S (CutInput Q Λ θ β N) q.1) :
    cutMackeyLayerMap Q Λ θ β N (Multiset.card ν) c
        (indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q.1 q.2 w) = 0 ↔
      (cutConcatIdem Q Λ θ β h : TensorKLR S ν ν') • w = 0 := by
  have hinj := indMackeyLeftMap_injective (Q := S) h (CutInput Q Λ θ β N) hsym hσ q
  have e1 := cutExcludedIdem_indMackeyLeftMap h q.1 q.2 w
  constructor
  · intro h0
    have h1 := (cutMackeyLayerMap_eq_zero_iff
      (indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q.1 q.2 w)).1 h0
    rw [e1] at h1
    exact hinj (h1.trans (map_zero (indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q.1 q.2)).symm)
  · intro h0
    refine (cutMackeyLayerMap_eq_zero_iff
      (indMackeyLeftMap (Q := S) h (CutInput Q Λ θ β N) q.1 q.2 w)).2 ?_
    rw [e1, h0, map_zero]
    rfl

end Categorification.Stendhal
