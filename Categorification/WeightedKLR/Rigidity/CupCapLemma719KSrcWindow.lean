/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KSrcUnit
import Categorification.WeightedKLR.Rigidity.CupCapLemma719KCutGood

/-!
# The window at the maximum acting on the unit of the right side

Webster, arXiv:1309.3796v3, Lemma 7.19 (K), proof of the inverse `Ψ`: the cap generators of the
model of `K̃^{λ⁺}_λ` have their window at `midPos`. On the unit `1 ⊗ (y ⊠ v)` of `S_+(Y ⊠ L')`,
the idempotents of these windows select the loadings `i ⊔ l` at the cut: the part of the unit
at the block loadings `i, w, l` vanishes when the tail `l` is violated or out of red order
(`kSrcPart_eq_zero_of_bad`), and otherwise the window at `midPos s` meets it only for
`s = i ⊔ l` (`kSrc_e_insertSeq_smul_unit`, `kSrc_eSum_insertSet_smul_unit`).

## Main definitions

* `Stendhal.CupCap.kSrcPart`: the part of the unit at the block loadings `i, w, l`.

## Main results

* `Stendhal.CupCap.kSrcPart_eq_zero_of_bad`: the parts with a bad tail vanish.
* `Stendhal.CupCap.kSrc_e_insertSeq_smul_unit`: an idempotent of the window at the maximum on
  the unit.
* `Stendhal.CupCap.kSrc_eSum_insertSet_smul_unit`: the idempotent of the whole window.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite
open scoped TensorProduct

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [Field k] {ℓ : ℕ} (j : ℕ) (hj : j ≤ ℓ)
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (θ γ ν₀ : Multiset I)
  (Y : Type) [AddCommGroup Y] [Module k Y]
  [Module (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y]
  [IsScalarTower k (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) Y] (hQ : KLRSymm Q)
  (L' : Type) [AddCommGroup L'] [Module k L']
  [Module (TensorProductAlgebra k Q Λc ν₀) L'] [IsScalarTower k (TensorProductAlgebra k Q Λc ν₀) L']

set_option hygiene false in
local notation "Xs" => KCutSrc j hj Q Λ Λc θ γ ν₀ Y hQ L'
set_option hygiene false in
local notation "mkp" => TensorProductAlgebra.mk Q (plusLabels Λ Λc j hj) ((θ + γ) + ν₀)
set_option hygiene false in
local notation "botp" => botMap k Q Λ Λc j hj (θ + γ) ν₀
set_option hygiene false in
local notation "Np" => BlocksOneStepInput Q (plusBlockLabels Λ Λc j hj) θ ν₀ γ
  (PlusInput Q Λ Λc j hj θ ν₀ γ (MidSpect (k := k) Y L'))

/-- **The part of the unit at the block loadings `i, w, l`**: `1 ⊗ (e(i) ⊗ e(w) ⊗ e(l))(y ⊠ v)`. -/
def kSrcPart (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) (y : Y) (v : L') : Xs :=
  kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' ((plusHeadEmb j hj Q Λ Λc θ (e i) ⊗ₜ[k]
    (plusMidEmb j hj Q Λ Λc ν₀ (e w) ⊗ₜ[k] plusTailEmb j hj Q Λ Λc γ (e l))) •
      (show Np from midSpectTmul (k := k) y v))

set_option hygiene false in
local notation "Pt" => kSrcPart j hj Q Λ Λc θ γ ν₀ Y hQ L'

theorem midSpectTmul_zero_left (v : L') : midSpectTmul (k := k) (0 : Y) v = 0 :=
  TensorProduct.zero_tmul _ _

/-- **The parts of the unit with a violated or red-unordered tail vanish**: the idempotent of
the tail is zero in `T^{λ_{j+1}…λ_ℓ}`. -/
theorem kSrcPart_eq_zero_of_bad (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    {l : Seq (stendhalWeight (ℓ - j) γ)} (hl : ¬ (IsRedOrdered l ∧ ¬ IsViolated l)) (y : Y)
    (v : L') : Pt i w l y v = 0 := by
  have h0 : tensorOfKLR Q (blocksTailLabels (plusBlockLabels Λ Λc j hj) ∘ Fin.natAdd 2) γ
      (e l) = 0 := by
    by_cases ho : IsRedOrdered l
    · exact tensorOfKLR_e_of_isViolated (not_not.1 fun h => hl ⟨ho, h⟩)
    · exact tensorOfKLR_e_of_not_isRedOrdered ho
  rw [kSrcPart, plusInput_tmul_smul, h0, map_zero, TensorProduct.tmul_zero]
  erw [zero_smul (cutFactorAlgebra Q (cutLabels j hj Λ) θ γ) y, midSpectTmul_zero_left]
  exact map_zero _

/-- **The condition that an inserted loading at the maximum has given block loadings**, on the
parts of the unit: it is `s = i ⊔ l` and `t = w`, the bad tails contributing zero. -/
theorem kSrc_ite_insertSeq (s : Seq (stendhalWeight ℓ (θ + γ))) (t : Seq (stendhalWeight 2 ν₀))
    (i : Seq (stendhalWeight j θ)) (w : Seq (stendhalWeight 2 ν₀))
    (l : Seq (stendhalWeight (ℓ - j) γ)) (y : Y) (v : L') :
    (if insertSeq (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s)
        (Seq.map (cupColour j hj) t) = plusCutSeq hj i w l then
      Pt i w l y v else 0) =
      if s = cutSeq hj i l ∧ t = w then Pt i w l y v else 0 := by
  by_cases hl : IsRedOrdered l ∧ ¬ IsViolated l
  · simp only [insertSeq_midPos_eq_iff hj s t i w hl.1 hl.2]
  · rw [kSrcPart_eq_zero_of_bad j hj Q Λ Λc θ γ ν₀ Y hQ L' i w hl y v, ite_self, ite_self]

/-- **An idempotent of the window at the maximum acts on the unit** through the part at the
loadings at the cut it is inserted into. -/
theorem kSrc_e_insertSeq_smul_unit (s : Seq (stendhalWeight ℓ (θ + γ)))
    (t : Seq (stendhalWeight 2 ν₀)) (y : Y) (v : L') :
    mkp (botp (e (insertSeq (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s) (midPos_le j s)
        (Seq.map (cupColour j hj) t)))) •
        kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v) =
      ∑ i : Seq (stendhalWeight j θ), ∑ l : Seq (stendhalWeight (ℓ - j) γ),
        if s = cutSeq hj i l then Pt i t l y v else 0 := by
  rw [kSrc_e_smul_unit]
  change (∑ i, ∑ w, ∑ l, if _ = plusCutSeq hj i w l then Pt i w l y v
    else 0) = _
  simp only [kSrc_ite_insertSeq, ite_and]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · rw [Finset.sum_ite_eq]
    simp
  · simp

/-- **The idempotent of the window at the maximum acts on the unit** through the parts at the
loadings at the cut equal to `s`. -/
theorem kSrc_eSum_insertSet_smul_unit (s : Seq (stendhalWeight ℓ (θ + γ))) (y : Y) (v : L') :
    mkp (botp (KLRAlgebra.eSum _ (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (midPos j s)
        (midPos_le j s)))) •
        kSrcUnit j hj Q Λ Λc θ γ ν₀ Y hQ L' (show Np from midSpectTmul (k := k) y v) =
      ∑ i : Seq (stendhalWeight j θ), ∑ l : Seq (stendhalWeight (ℓ - j) γ),
        if s = cutSeq hj i l then ∑ w : Seq (stendhalWeight 2 ν₀), Pt i w l y v
        else 0 := by
  rw [eSum_insertSet, map_sum, map_sum, Finset.sum_smul]
  simp only [kSrc_e_insertSeq_smul_unit]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

end Categorification.Stendhal.CupCap
