/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendCut

/-!
# The appended model and the sliding diagrams

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, for a cap not at the right end (`j < ℓ`). The left action of `T̃^λ` on the
model of the cap bimodule is through sliding diagrams of `λ⁺` placed above the maximum
(`CupCap.midEnd`). The comparison `𝔉_i(model_ν) → model_{{i} + ν}`
(`CupCap.appendMidMap`, from `CupCap.appendMidEquiv` and `CupCap.toAppendMid`) intertwines the
action of a sliding diagram `Y` at `ν` with the action of the appended diagram `appendPlus Y` at
`{i} + ν`, whenever the latter slides (`CupCap.appendMidMap_comp_map_midEnd`). The proof uses that
`σ(1) e⁺ = e'` (`CupCap.midStendhal_one_mul_appendBlackPlus_one`): above the maximum, the
appended diagram only meets the appended loadings.

## Main definitions

* `CupCap.appendMidMap`: the comparison map.

## Main results

* `CupCap.appendMidMap_comp_map_midEnd`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  (j : ℕ) (hj : j ≤ ℓ) (ν ν₀ : Multiset I) (i : I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "Λ⁺" => plusLabels Λ Λc j hj
local notation "Tᵢ" => (StendhalAlgebra k Q Λ⁺ (νᵢ + ν₀))ᵐᵒᵖ
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The comparison of `𝔉_i` of the model at `ν` with the model at `{i} + ν`**, for `j < ℓ`:
`Z ⊗ (W ⊗ v) ↦ e' appendBlack(W) Z ⊗ v`. -/
def appendMidMap (h : j < ℓ) :
    Ind (MidModel j hj Q Λ Λc ν ν₀ L) (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i) →ₗ[Tᵢ]
      MidModel j hj Q Λ Λc νᵢ ν₀ L :=
  (toAppendMid Q Λ Λc j hj ν ν₀ i L h).comp (appendMidEquiv Q Λ Λc j hj ν ν₀ i L).toLinearMap

variable {Q Λ Λc j hj ν₀}

omit [DecidableEq I] in
theorem sandwich_absorb {R : Type*} [Ring R] {e s a B X : R} (h1 : e * s = e) (h2 : s * e = e)
    (h3 : e * e = e) (h4 : s * a = e) (h5 : a * B = B) :
    e * s * (e * B * e * X) = s * B * s * (e * s * X) :=
  calc e * s * (e * B * e * X) = e * s * e * B * e * X := by simp only [mul_assoc]
    _ = e * B * e * X := by rw [h1, h3]
    _ = s * a * B * e * X := by rw [h4]
    _ = s * (a * B) * (e * s) * X := by rw [h1]; simp only [mul_assoc]
    _ = s * B * (s * e) * s * X := by rw [h5, h2]; simp only [mul_assoc]
    _ = s * B * s * (e * s * X) := by simp only [mul_assoc]

/-- The algebra behind `CupCap.appendMidMap_comp_map_midEnd`. -/
theorem appendBlackPlus_midElt (h : j < ℓ) (Y : Rp)
    (W : StendhalAlgebra k Q Λ⁺ (ν + ν₀)) :
    appendIdemPlus Q Λ Λc j hj ν ν₀ i * midStendhal j hj Q Λ Λc νᵢ ν₀ 1 *
        appendBlackPlus Q Λ Λc j hj ν ν₀ i
          (midStendhal j hj Q Λ Λc ν ν₀ 1 * botMap k Q Λ Λc j hj ν ν₀ Y *
            midStendhal j hj Q Λ Λc ν ν₀ 1 * W) =
      midStendhal j hj Q Λ Λc νᵢ ν₀ 1 *
          botMap k Q Λ Λc j hj νᵢ ν₀ (appendPlus Q Λ Λc j hj ν ν₀ i Y) *
          midStendhal j hj Q Λ Λc νᵢ ν₀ 1 *
        (appendIdemPlus Q Λ Λc j hj ν ν₀ i * midStendhal j hj Q Λ Λc νᵢ ν₀ 1 *
          appendBlackPlus Q Λ Λc j hj ν ν₀ i W) := by
  rw [map_mul, map_mul, map_mul, appendBlackPlus_midStendhal_one ν i h, appendBlackPlus_botMap]
  exact sandwich_absorb (appendIdemPlus_mul_midStendhal_one ν i h)
    (midStendhal_one_mul_appendIdemPlus ν i h) (appendIdemPlus_mul_self ν i h)
    (midStendhal_one_mul_appendBlackPlus_one ν i h)
    (by rw [← appendBlackPlus_botMap, ← map_mul, one_mul])

variable {L}
variable (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
  op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)

/-- **The comparison intertwines the sliding diagrams with the appended ones**
(arXiv:1309.3796v3, §7.3, proof of Proposition 7.21), for `j < ℓ`: if `Y` slides at `ν` and
`appendPlus Y` slides at `{i} + ν`, then the comparison carries `𝔉_i` of the action of `Y` to the
action of `appendPlus Y`. -/
theorem appendMidMap_comp_map_midEnd (h : j < ℓ) {Y : Rp}
    (hY : MidSlides j hj Q Λ Λc ν ν₀ Y)
    (hY' : MidSlides j hj Q Λ Λc νᵢ ν₀ (appendPlus Q Λ Λc j hj ν ν₀ i Y)) :
    (appendMidMap Q Λ Λc j hj ν ν₀ i L h).comp (Ind.map (midEnd L hL hY)) =
      (midEnd L hL hY').comp (appendMidMap Q Λ Λc j hj ν ν₀ i L h) := by
  refine Ind.ext fun z t => ?_
  induction t using Ind.induction_on with
  | zero => simp only [Ind.tmul_zero, map_zero]
  | add a b ha hb => simp only [Ind.tmul_add, map_add] at ha hb ⊢; rw [ha, hb]
  | tmul w v =>
    have hA : ∀ x, (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i x).unop =
        appendBlackPlus Q Λ Λc j hj ν ν₀ i x.unop := fun _ => rfl
    have key := congrArg (· * z.1.unop) (appendBlackPlus_midElt ν i h Y w.1.unop)
    change Ind.tmul ⟨z.1 * appendBlackPlusOp Q Λ Λc j hj ν ν₀ i
        (w.1 * midElt j hj Q Λ Λc ν ν₀ Y) * appendMidOp Q Λ Λc j hj ν ν₀ i 1, _⟩ v =
      Ind.tmul ⟨z.1 * appendBlackPlusOp Q Λ Λc j hj ν ν₀ i w.1 *
        appendMidOp Q Λ Λc j hj ν ν₀ i 1 * midElt j hj Q Λ Λc νᵢ ν₀
          (appendPlus Q Λ Λc j hj ν ν₀ i Y), _⟩ v
    congr 1
    apply Subtype.ext
    apply MulOpposite.unop_injective
    simp only [midElt, unop_mul, unop_op, hA, appendMidOp_apply ν i h, midOp_apply, unop_one]
    simp only [mul_assoc] at key ⊢
    exact key

end Categorification.Stendhal.CupCap
