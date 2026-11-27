/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutIdem

/-!
# The idempotents of `T^λ` on the unit of the partial standardization at the cut

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof that `Φ` is onto: the idempotent `e(s)` of
`T^λ(θ + γ)` acts on the unit `1 ⊗ y` of `S_cut Y` by `0` unless `s` is the loading `i ⊔ l` of
the two blocks, where it acts through `e(i) ⊗ e(l)` on `Y`.

## Main results

* `Stendhal.CupCap.kCut_e_cutSeq_smul_unit`: `e(i ⊔ l)` on the unit.
* `Stendhal.CupCap.kCutUnit_eq_sum`: the unit is the sum of its parts at the loadings `i ⊔ l`.
* `Stendhal.CupCap.kCut_e_smul_unit`: `e(s)` on the unit.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ)
  (θ γ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)

set_option hygiene false in
local notation "Sc" => stendhalQ Q (cutLabels j hj Λ)
set_option hygiene false in
local notation "αc" => Multiset.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j)))
  (stendhalWeight j θ)
set_option hygiene false in
local notation "δc" => Multiset.map (Sum.map (id : I → I) (Fin.natAdd j))
  (stendhalWeight (ℓ - j) γ)
set_option hygiene false in
local notation "cast_c" => castLabelsTensorProductAlgebra Q (Nat.add_sub_of_le hj) Λ (θ + γ)
set_option hygiene false in
local notation "Th" => tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.castAdd (ℓ - j)) θ
set_option hygiene false in
local notation "Tt" => tensorOfKLR Q (cutLabels j hj Λ ∘ Fin.natAdd j) γ
set_option hygiene false in
local notation "Et" s:max =>
  TensorProductAlgebra.mk Q Λ (θ + γ) (topMap k Q Λ (θ + γ) (KLRAlgebra.e s))
set_option hygiene false in
local notation "u" y:max => kCutUnit j hj Q Λ θ γ Y hQ y

/-- **The idempotent of `i ⊔ l` acts on the unit through `e(i) ⊗ e(l)`.** -/
theorem kCut_e_cutSeq_smul_unit (i : Seq (stendhalWeight j θ))
    (l : Seq (stendhalWeight (ℓ - j) γ)) (y : Y) :
    Et (cutSeq hj i l) • u y =
      u ((Th (e i) ⊗ₜ[k] Tt (e l) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y) := by
  have hc := castLabels_cutAffineMap_concat_smul_kCutUnit j hj Q Λ θ γ Y hQ
    (cutHeadEmb j hj Q Λ θ (e i) ⊗ₜ[k] cutTailEmb j hj Q Λ γ (e l)) y
  rw [cutInputMap_emb] at hc
  rw [← hc]
  have hcat : concat Sc αc δc
      (cutHeadEmb j hj Q Λ θ (e i) ⊗ₜ[k] cutTailEmb j hj Q Λ γ (e l)) =
      e ((Seq.map (Sum.map (id : I → I) (Fin.castAdd (ℓ - j))) i).append
        (Seq.map (Sum.map (id : I → I) (Fin.natAdd j)) l)) := by
    rw [relabelEquiv_apply, relabelEquiv_apply, relabelHom_e, relabelHom_e, concat_e_tmul_e]
    rfl
  rw [hcat, cast_c_cutAffineMap_e j hj Q Λ θ γ _ (cutSeq hj i l)
      (fun p q hpq => (castLabelsSeq_lbl _ _ _ p).trans (congrArg _ (Seq.apply_congr _
        (by simp [hpq]))))]

/-- **The unit is the sum of its parts at the loadings `i ⊔ l` of the two blocks.** -/
theorem kCutUnit_eq_sum (y : Y) :
    u y = ∑ i : Seq (stendhalWeight j θ), ∑ l : Seq (stendhalWeight (ℓ - j) γ),
      Et (cutSeq hj i l) • u y := by
  have h1 : (1 : TensorKLR Sc αc δc) = ∑ i : Seq (stendhalWeight j θ),
      ∑ l : Seq (stendhalWeight (ℓ - j) γ),
        cutHeadEmb j hj Q Λ θ (e i) ⊗ₜ[k] cutTailEmb j hj Q Λ γ (e l) := by
    simp only [← TensorProduct.tmul_sum, ← TensorProduct.sum_tmul, ← map_sum, sum_e, map_one,
      Algebra.TensorProduct.one_def]
  have hu := castLabels_cutAffineMap_concat_smul_kCutUnit j hj Q Λ θ γ Y hQ 1 y
  rw [show cutInputMap Q (cutLabels j hj Λ) θ γ 1 = 1 from map_one _, one_smul] at hu
  conv_lhs => rw [← hu, h1]
  simp only [map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [castLabels_cutAffineMap_concat_smul_kCutUnit, kCut_e_cutSeq_smul_unit, cutInputMap_emb]

/-- **An idempotent of `T^λ` on the unit**: `e(s)` acts by `0` unless `s = i ⊔ l`. -/
theorem kCut_e_smul_unit (s : Seq (stendhalWeight ℓ (θ + γ))) (y : Y) :
    Et s • u y = ∑ i : Seq (stendhalWeight j θ), ∑ l : Seq (stendhalWeight (ℓ - j) γ),
      if s = cutSeq hj i l then
        u ((Th (e i) ⊗ₜ[k] Tt (e l) : cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) • y)
      else 0 := by
  conv_lhs => rw [kCutUnit_eq_sum]
  simp only [Finset.smul_sum, ← mul_smul, ← map_mul, e_mul_e]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · rw [h, kCut_e_cutSeq_smul_unit]
  · rw [map_zero, map_zero, zero_smul]

end Categorification.Stendhal.CupCap
