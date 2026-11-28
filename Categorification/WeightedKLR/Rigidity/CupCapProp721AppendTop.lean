/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendPos
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeStagedLoopRight
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftFreeMackeyPass

/-!
# `𝔉_i` of the model for a cap at the right end

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap at the right end (`j = ℓ`). There the window of a loading `s` sits at
its right end `m`, while the window of the appended loading `s i` sits at `m + 1`, to the right of
the new black strand `i`. Passing that strand under the window (`CupCap.posPassRightEquiv`, under
the hypotheses of Lemma 7.17) identifies the staged modules, so `L ⊗ (appended corner)` is the
product of the staged modules of the appended loadings at their own windows
(`CupCap.appendTopPiEquiv`).

## Main definitions

* `CupCap.appendTopPassEquiv`: `L ⊗ e_{s i, m} T̃^{λ⁺} ≅ L ⊗ e_{s i, m + 1} T̃^{λ⁺}`.
* `CupCap.appendTopPiEquiv`: `L ⊗ (appended corner) ≅ ∏_s L ⊗ e_{s i, midPos (s i)} T̃^{λ⁺}`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν ν₀ : Multiset I}
  {L : Type*} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)

variable (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Tᵢ" => (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (νᵢ + ν₀))ᵐᵒᵖ

variable (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
  (hκ : IsUnit (cupScalar Q ν₀ i))

omit [DecidableEq I] in
theorem midPos_appendBlackLoading_of_not_lt (h : ¬ j < ℓ) (s : Seq (stendhalWeight ℓ ν)) :
    midPos j (appendBlackLoading i ν s) = midPos j s + 1 := by
  rw [midPos_of_not_lt j _ h, midPos_of_not_lt j _ h, card_appendBlackWeight]

/-- **Passing the appended strand under the window at the right end** (arXiv:1309.3796v3, §7.3,
proof of Proposition 7.21), for `j = ℓ`: the staged module of `s i` with the window at
`midPos s = m`, to the left of the new strand `i`, is isomorphic to the one with the window at
`midPos (s i) = m + 1`, to its right. -/
def appendTopPassEquiv (h : ¬ j < ℓ) (s : Seq (stendhalWeight ℓ ν)) :
    PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s) (midPos j s)
        (midPos_le_appendBlackLoading j ν i s) L ≃ₗ[Tᵢ]
      PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s) (midPos j (appendBlackLoading i ν s))
        (midPos_le j _) L :=
  (posPassRightEquiv (j := j) (hj := hj) (Λ := Λ) L hP hPL hL i (appendBlackLoading i ν s)
      (n := midPos j s)
      (by rw [← midPos_appendBlackLoading_of_not_lt i h]; exact midPos_le j _)
      (appendBlackLoading_lbl_of_eq i ν s _ (by
        rw [Fin.val_mk, midPos_of_not_lt j _ h])) hκ).trans
    (posModelCongr j hj Q Λ Λc ν₀ L _ _ _
      (midPos_appendBlackLoading_of_not_lt i h s).symm)

variable (L) in
/-- **`𝔉_i` of the model for a cap at the right end, window by window** (arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21), for `j = ℓ`: the induced module of the appended corner is the
product of the staged modules of the appended loadings `s i` at their windows `midPos (s i)`. -/
def appendTopPiEquiv (h : ¬ j < ℓ) (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i')) :
    Ind L (appendMidOp Q Λ Λc j hj ν ν₀ i) ≃ₗ[Tᵢ]
      ((s : Seq (stendhalWeight ℓ ν)) →
        PosModel j hj Q Λ Λc ν₀ (appendBlackLoading i ν s)
          (midPos j (appendBlackLoading i ν s)) (midPos_le j _) L) :=
  (appendPosPiEquiv i L).trans
    (LinearEquiv.piCongrRight fun s => appendTopPassEquiv i (hP := hP) (hPL := hPL) (hL := hL)
      (hκ := hκ i) (h := h) s)

end Categorification.Stendhal.CupCap
