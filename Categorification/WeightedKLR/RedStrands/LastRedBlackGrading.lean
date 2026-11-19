/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedBlackMirror
import Categorification.WeightedKLR.RedStrands.StendhalTensorGrading

/-!
# The grading shift of Proposition 4.32

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32: `IR^μ F_i I^μ ≅ F_i(-μ_i)` and `IR^μ E_i I^μ ≅ E_i(μ_i)`. The crossing of the
black strand `i` with the last red strand `λ_ℓ` has the degree `δ = degΨ(λ_ℓ, i)` of
Definition 4.4, which for Webster's grading is `⟨α_i, λ_ℓ⟩ = d_i λ_ℓ^i`. Since adding strands
preserves degrees (`appendRed_mem_grade`, `appendBlack_mem_grade`), the isomorphisms
`lastRedBlackMap` and `lastRedBlackMirror` raise the degree of every homogeneous element by
exactly `δ`. This is the grading shift of the proposition.

## Main results

* `lastRedBlackCrossing_mem_grade`: the crossing is homogeneous of degree `δ`.
* `lastRedBlackMap_mem_grade`: `lastRedBlackMap` sends degree `d` to degree `d + δ`.
* `tensorFlip_mem_grade`: horizontal reflection preserves degrees (symmetric crossing degrees).
* `lastRedBlackMirror_mem_grade`: `lastRedBlackMirror` sends degree `d` to degree `d + δ`.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra

section Grading

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)
  (G : GradingDatum (stendhalQ Q Λ))

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "μ" => stendhalWeight ℓ ν
local notation "μ'" => stendhalWeight (ℓ + 1) νᵢ
local notation "N₀" => Multiset.card (stendhalWeight ℓ ν)
local notation "A" => StendhalAlgebraAllOrders k Q Λ νᵢ
local notation "δ" => G.degΨ (Sum.inr (Fin.last ℓ)) (Sum.inl i)

private theorem redBlackValue_sum (F : Finset (Seq μ)) :
    redBlackValue Q Λ i ν (∑ s ∈ F, StendhalAlgebraAllOrders.e s) =
      ∑ s ∈ F, StendhalAlgebraAllOrders.e (redBlackLoading i ν s) := by
  classical
  induction F using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, redBlackValue_zero]
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, redBlackValue_add, ih, redBlackValue_e]

private theorem ψ_mul_e_redBlack_mem (s : Seq μ) :
    (StendhalAlgebraAllOrders.ψ N₀ : A) * StendhalAlgebraAllOrders.e (redBlackLoading i ν s) ∈
      allOrdersGrade G νᵢ δ := by
  have hN : N₀ + 1 < Multiset.card μ' := by rw [card_stendhalWeight_append]; omega
  have h := G.ψ_mul_e_mem_grade hN (redBlackLoading i ν s)
  rw [redBlackLoading_lbl_of_eq s _ rfl, redBlackLoading_lbl_of_last s _ rfl] at h
  have h' := Graded.mem_map_of_mem (G.grade μ') (StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ).toLinearMap h
  rw [AlgHom.toLinearMap_apply, map_mul] at h'
  exact h'

/-- The crossing of the black strand `i` with the last red strand has degree `degΨ(λ_ℓ, i)`. -/
theorem lastRedBlackCrossing_mem_grade :
    lastRedBlackCrossing Q Λ i ν ∈ tensorProductGrade G νᵢ δ := by
  classical
  apply Graded.mem_map_of_mem (stendhalGrade G νᵢ) (TensorProductAlgebra.mk Q Λ νᵢ).toLinearMap
  change (crossingStendhalCut Q Λ i ν).val ∈ allOrdersGrade G νᵢ δ
  rw [crossingStendhalCut_val]
  change _ * redBlackValue Q Λ i ν (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ₀ ν) ∈ _
  unfold StendhalAlgebraAllOrders.redOrderedIdem
  rw [redBlackValue_sum, Finset.mul_sum]
  exact Submodule.sum_mem _ fun s _ => ψ_mul_e_redBlack_mem Q Λ i ν G s

/-- **Grading shift in Webster's Proposition 4.32, `F_i` part** (arXiv:1309.3796v3): the map
`g ↦ appendRed(g) · (crossing)` raises degrees by `degΨ(λ_ℓ, i)`. -/
theorem lastRedBlackMap_mem_grade {d : ℤ} {g : TensorProductAlgebra k Q Λ₀ νᵢ}
    (hg : g ∈ tensorProductGrade (restrictRedGrading Q Λ G) νᵢ d) :
    lastRedBlackMap Q Λ i ν g ∈ tensorProductGrade G νᵢ (d + δ) :=
  SetLike.GradedMul.mul_mem (appendRed_mem_grade Q Λ νᵢ G hg)
    (lastRedBlackCrossing_mem_grade Q Λ i ν G)

end Grading

section Reflection

variable {I k : Type*} [DecidableEq I] [Field k] {Q : I → I → MvPolynomial (Fin 2) k}
  {ℓ : ℕ} {Λ : Fin ℓ → I →₀ ℕ} {ν : Multiset I}

/-- Horizontal reflection preserves degrees when the crossing degrees are symmetric. -/
theorem tensorFlip_mem_grade (G : GradingDatum (stendhalQ Q Λ))
    (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) {d : ℤ} {z : TensorProductAlgebra k Q Λ ν}
    (hz : z ∈ tensorProductGrade G ν d) : tensorFlip z ∈ tensorProductGrade G ν d := by
  obtain ⟨a, ha, rfl⟩ := stendhalTensorProjection_grade_lift Λ G ν hz
  rw [tensorFlip_projection]
  exact stendhalTensorProjection_mem_grade Λ G ν (G.hflip_mem_grade hsymm ha)

end Reflection

section Mirror

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [Field k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)
  (G : GradingDatum (stendhalQ Q Λ))

local notation "Λ₀" => (Λ ∘ Fin.castSucc)
local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "δ" => G.degΨ (Sum.inr (Fin.last ℓ)) (Sum.inl i)

/-- **Grading shift in Webster's Proposition 4.32, `E_i` part** (arXiv:1309.3796v3): the map
`g ↦ (crossing)ᵗ · appendRed(g)` raises degrees by `degΨ(λ_ℓ, i)`, for symmetric crossing
degrees. -/
theorem lastRedBlackMirror_mem_grade (hsymm : ∀ a b, G.degΨ a b = G.degΨ b a) {d : ℤ}
    {g : TensorProductAlgebra k Q Λ₀ νᵢ}
    (hg : g ∈ tensorProductGrade (restrictRedGrading Q Λ G) νᵢ d) :
    lastRedBlackMirror Q Λ i ν g ∈ tensorProductGrade G νᵢ (d + δ) := by
  have hsymm₀ : ∀ a b, (restrictRedGrading Q Λ G).degΨ a b =
      (restrictRedGrading Q Λ G).degΨ b a := fun a b => hsymm _ _
  have hflip : tensorFlip g ∈ tensorProductGrade (restrictRedGrading Q Λ G) νᵢ d :=
    tensorFlip_mem_grade (restrictRedGrading Q Λ G) hsymm₀ hg
  rw [lastRedBlackMirror_eq_tensorFlip]
  exact tensorFlip_mem_grade G hsymm (lastRedBlackMap_mem_grade Q Λ i ν G hflip)

end Mirror

end Categorification.Stendhal
