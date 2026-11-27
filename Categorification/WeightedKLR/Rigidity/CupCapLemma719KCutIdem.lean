/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutMap
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutSeq

/-!
# The comparison map of Lemma 7.19 (K) at the cut on idempotents

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof: the map `y ⊠ v ↦ cap(|h|, v) ⊗ (1 ⊗ y)`
intertwines the idempotents. The idempotent `e(i) ⊗ e(w) ⊗ e(l)` of the three blocks of `λ⁺`
selects, in the sum of the cap generators, the generator whose top loading is the loading
`i ⊔ l` of `λ` (`op_e_smul_capSum`), and then acts on it as the idempotent of its bottom loading
`i ⊔ w ⊔ l` (`capGen_box_e`). On the other side the idempotent `e(i ⊔ w ⊔ l)` of all strands
of `λ⁺` kills every other cap generator (`botMap_e_smul_capSum`).

## Main results

* `Stendhal.CupCap.botMap_e_smul_capSum`: an idempotent of an inserted loading selects the cap
  generator of the loading it was inserted into.
* `Stendhal.CupCap.kCut_e`: the intertwining condition at the triples of idempotents.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Collapse

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {ν ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **An idempotent of an inserted loading selects the cap generator of the loading it was
inserted into.** -/
theorem botMap_e_smul_capSum (s : Seq (stendhalWeight ℓ ν))
    (n : Fin (Multiset.card (stendhalWeight ℓ ν) + 1))
    (t : Seq ((stendhalWeight 2 ν₀).map (cupColour j hj))) (v : L) :
    TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (e (insertSeq s n (Nat.lt_succ_iff.1 n.2) t))) •
        capSum j hj Q Λ Λc ν ν₀ n v =
      TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) (ν + ν₀)
        (botMap k Q Λ Λc j hj ν ν₀ (e (insertSeq s n (Nat.lt_succ_iff.1 n.2) t))) •
        capGen j hj Q Λ Λc ν ν₀ s n v := by
  rw [capSum, Finset.smul_sum]
  refine Finset.sum_eq_single s (fun s' _ hs' => ?_) (fun h => absurd (Finset.mem_univ s) h)
  have he : (e (insertSeq s n (Nat.lt_succ_iff.1 n.2) t) :
      KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))) =
      KLRAlgebra.eSum _ {insertSeq s n (Nat.lt_succ_iff.1 n.2) t} := by
    rw [KLRAlgebra.eSum, Finset.sum_singleton]
  rw [he]
  refine eSum_smul_capGen_of_disjoint _ s' n v (Finset.disjoint_singleton_right.2 fun hm => ?_)
  obtain ⟨t', -, ht'⟩ := Finset.mem_image.1 hm
  exact hs' (insertSeq_left_injective hj ht')

end Collapse

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "σK" => kCutOneStepRep j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "fK" => kCutInputMap j hj Q Λ Λc θ γ ν₀ Y hQ L'

/-- **The idempotents of the three blocks.** -/
theorem kCut_e (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) :
    IsInd3At σK fK (plusHeadEmb j hj Q Λ Λc θ (e i) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ (e w) ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (e l))) := by
  refine isInd3At_of_tmul j hj Q Λ Λc θ γ ν₀ Y hQ L' _ fun y v => ?_
  have hφ : plusHeadEmb j hj Q Λ Λc θ (e i) ⊗ₜ[k]
      (plusMidEmb j hj Q Λ Λc ν₀ (e w) ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (e l)) =
      e (Seq.map (Sum.map (id : I → I) (Fin.castAdd (2 + (ℓ - j)))) i) ⊗ₜ[k]
        (e (Seq.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) w)) ⊗ₜ[k]
        e (Seq.map (Sum.map (id : I → I) (Fin.natAdd j))
          (Seq.map (Sum.map (id : I → I) (Fin.natAdd 2)) l))) := by
    simp only [plusHeadEmb, plusMidEmb, plusMidEmb₀, plusTailEmb, plusTailEmb₀,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, relabelEquiv_apply, relabelHom_e]
    rfl
  have hc := castLabels_cutAffineMap_concat_smul_kCutUnit j hj Q Λ θ γ Y hQ
    (cutHeadEmb j hj Q Λ θ (e i) ⊗ₜ[k] cutTailEmb j hj Q Λ γ (e l)) y
  rw [cutInputMap_emb] at hc
  rw [plusInput_tmul_smul]
  erw [relabel_tensorOfKLR_e Q (Λ₂ := cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j))
      (plusBlockLabels_head Λ Λc j hj) θ i,
    relabel_tensorOfKLR_e Q (Λ₂ := cutLabels j hj Λ ∘ Fin.natAdd j)
      (plusBlockLabels_tail Λ Λc j hj) γ l,
    relabel_tensorOfKLR_e Q (Λ₂ := Λc) (plusBlockLabels_cup Λ Λc j hj) ν₀ w,
    kCutInputMap_tmul, kCutInputMap_tmul]
  rw [← hc]
  have hcat : concat (stendhalQ Q (cutLabels j hj Λ)) _ _
      (cutHeadEmb j hj Q Λ θ (e i) ⊗ₜ[k] cutTailEmb j hj Q Λ γ (e l)) =
      e ((Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) i).append
        (Seq.map (Sum.map (id : I → I) (Fin.natAdd j)) l)) := by
    rw [relabelEquiv_apply, relabelEquiv_apply, relabelHom_e, relabelHom_e, concat_e_tmul_e]
    rfl
  rw [hcat, cast_c_cutAffineMap_e j hj Q Λ θ γ _ (cutSeq hj i l)
      (fun p q hpq => (castLabelsSeq_lbl _ _ _ p).trans (congrArg _ (Seq.apply_congr _
        (by simp [hpq]))))]
  rw [← hflip_e, toCapCoef_tensorOfKLR_smul, ← BalancedTensor.op_smul_tmul, op_e_smul_capSum,
    capGen_box_e, ← BalancedTensor.smul_tmul', hφ, concat3_e_tmul_e_tmul_e]
  erw [kCutOneStepRep_e _ _ _ _ _ _ _ _ _ _ _ (plusSeq i w l)
      (insertSeq (cutSeq hj i l) (cutPos j hj θ γ) (Nat.lt_succ_iff.1 (cutPos j hj θ γ).2)
        (Seq.map (cupColour j hj) w))
      (fun p q hpq => insertSeq_cutSeq_lbl hj i w l _ p q hpq)]
  rw [BalancedTensor.smul_tmul', BalancedTensor.smul_tmul', botMap_e_smul_capSum]

end Categorification.Stendhal.CupCap
