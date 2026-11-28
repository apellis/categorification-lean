/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendDotMid
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendIota
import Categorification.WeightedKLR.Rigidity.CupCapMidModelMap

/-!
# Appending a strand to the model carries the new dot to the new dot

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the compatibility of `K ∘ 𝔈_i ≅ 𝔈_i ∘ K` with the dot, for `j < ℓ`. On the
image of the map `ι` appending a black strand to the model, the left action of the dot on the
appended strand of `T̃^λ` (times the unit of the appended strand) is the right action of the dot
`X` on the appended strand of `T̃^{λ⁺}` (times the unit of the appended strand)
(`CupCap.appendIota_appendedDot`): the dot of `λ`, placed above the maximum, is `X` cut by the
unit at the maximum (`CupCap.botMap_midDot_last`), and `X` commutes with every factor of the
image of `ι`.

## Main results

* `CupCap.newDotStendhal_eq_mul`: the dot on the appended strand times its unit, in `T̃^λ`.
* `CupCap.appendIota_appendedDot`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

section Generic

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {n : ℕ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ' : Fin n → I →₀ ℕ) (i : I) (μ : Multiset I)

/-- The dot on the appended strand times the unit of the appended strand, as an element of
`T̃^λ`: it is the projection of the dot times the image of the unit. -/
theorem newDotStendhal_eq_mul :
    (⟨StendhalAlgebraAllOrders.newDot Q Λ' i μ *
        appendBlackValue Q Λ' i μ (StendhalAlgebraAllOrders.redOrderedIdem k Q Λ' μ),
      newDot_mul_E1_mem Q Λ' i μ⟩ :
        StendhalAlgebra k Q Λ' ((Singleton.singleton i : Multiset I) + μ)) =
      orderProjection Q Λ' ((Singleton.singleton i : Multiset I) + μ)
          (StendhalAlgebraAllOrders.newDot Q Λ' i μ) *
        appendBlackStendhal Q Λ' i μ 1 := by
  apply Subtype.ext
  have hE := (Subsemigroup.mem_corner_iff
    StendhalAlgebraAllOrders.isIdempotentElem_redOrderedIdem).mp (E1_mem Q Λ' i μ)
  change _ = StendhalAlgebraAllOrders.newDot Q Λ' i μ * _ * appendBlackValue Q Λ' i μ _
  rw [mul_assoc]
  erw [hE.1]

end Generic

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} (ν : Multiset I) {ν₀ : Multiset I} (i : I)
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "MM" => MidModel j hj Q Λ Λc ν ν₀ L
local notation "aB⁺" => appendBlackPlus Q Λ Λc j hj ν ν₀ i
local notation "σ'" => midStendhal j hj Q Λ Λc νᵢ ν₀
local notation "X" => lastDotPlus k Q Λ Λc j hj ν₀ ν i

/-- The dot on the appended strand of `T̃^λ` is the dot on the last strand. -/
theorem newDot_eq_ofKLR_lastLoading :
    StendhalAlgebraAllOrders.newDot Q Λ i ν =
      StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ (KLRAlgebra.x (lastLoading ℓ ν i)) := by
  have h1 := congrArg Multiset.card (stendhalWeight_addBlack (ℓ := ℓ) i ν)
  rw [Multiset.card_add, Multiset.card_singleton] at h1
  change StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ (KLRAlgebra.x _) = _
  refine congrArg (fun a => StendhalAlgebraAllOrders.ofKLR k Q Λ νᵢ (KLRAlgebra.x a))
    (Fin.ext ?_)
  change Multiset.card (stendhalWeight ℓ ν) = Multiset.card (stendhalWeight ℓ νᵢ) - 1
  omega

/-- The dot `X` commutes with the image of `1 ⊗ (W ⊗ v)` under appending the strand. -/
theorem commute_lastDotPlus_appendIotaElt (W : StendhalAlgebra k Q
    (plusLabels Λ Λc j hj) (ν + ν₀)) :
    Commute X (appendIdemPlus Q Λ Λc j hj ν ν₀ i * σ' 1 * aB⁺ W * aB⁺ 1) :=
  (((commute_lastDotPlus_appendIdemPlus ν i).mul_right
    (commute_lastDotPlus_midStendhal_one (hj := hj) (Λc := Λc) ν i)).mul_right
    (commute_lastDotPlus_appendBlackPlus ν i W)).mul_right
    (commute_lastDotPlus_appendBlackPlus ν i 1)

/-- **Appending a strand carries the new dot to the new dot**, for `j < ℓ` (arXiv:1309.3796v3,
§7.3, proof of Proposition 7.21): on the image of `ι`, the left action of the dot on the
appended strand of `T̃^λ` times the unit of the appended strand is the right action of the dot
`X` on the appended strand of `T̃^{λ⁺}` times the unit of the appended strand. -/
theorem appendIota_appendedDot (h : j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hR' : MidKLRRel j hj Q Λ Λc νᵢ ν₀ L hL) (y : MM) :
    midLeftAlg L hL hR' (orderProjection Q Λ νᵢ (StendhalAlgebraAllOrders.newDot Q Λ i ν) *
        appendBlackStendhal Q Λ i ν 1) (appendIota ν i L h y) =
      op (X * aB⁺ 1) • appendIota ν i L h y := by
  rw [map_mul, Module.End.mul_apply, ← appendIota_midLeftAlg ν i h hR hR' 1, map_one,
    Module.End.one_apply, newDot_eq_ofKLR_lastLoading]
  change midLeftAlg L hL hR' (topMap k Q Λ νᵢ (KLRAlgebra.x (lastLoading ℓ ν i))) _ = _
  rw [midLeftAlg_topMap, midKLRAct_x]
  induction y using Ind.induction_on with
  | zero =>
    have h0 : appendIota (j := j) (hj := hj) (Q := Q) (Λ := Λ) (Λc := Λc) (ν₀ := ν₀) ν i L h 0 =
        0 := by
      rw [appendIota, Ind.tmul_zero, map_zero]
    rw [h0, map_zero, smul_zero]
  | add a b ha hb => rw [appendIota_add, map_add, ha, hb, smul_add]
  | tmul w v =>
    rw [midEnd]
    change natMapOn _ (Ind.tmul _ v) = op (X * aB⁺ 1) • Ind.tmul _ v
    rw [natMapOn_tmul, Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    apply MulOpposite.unop_injective
    change (_ * midElt j hj Q Λ Λc νᵢ ν₀ _).unop = (op (X * aB⁺ 1) * _).unop
    simp only [midElt, unop_mul, unop_op, appendMidOp_apply ν i h, midOp_apply, unop_one,
      botMap_midDot_last ν i h]
    have hc := commute_lastDotPlus_appendIotaElt (hj := hj) (Λc := Λc) ν i w.1.unop
    have hσ : σ' 1 * σ' 1 = σ' 1 := by rw [← map_mul, one_mul]
    have hXσ : X * σ' 1 = σ' 1 * X := (commute_lastDotPlus_midStendhal_one ν i).eq
    have hσe : appendIdemPlus Q Λ Λc j hj ν ν₀ i * σ' 1 =
        σ' 1 * appendIdemPlus Q Λ Λc j hj ν ν₀ i :=
      (commute_appendIdemPlus ν i 1).eq
    have hBB : aB⁺ 1 * aB⁺ 1 = aB⁺ 1 := by rw [← map_mul, one_mul]
    simp only [cornerMul, compMul, unitGen]
    have hA : ∀ x, (appendBlackPlusOp Q Λ Λc j hj ν ν₀ i x).unop = aB⁺ x.unop := fun _ => rfl
    simp only [unop_mul, hA, midOp_apply, unop_op, unop_one]
    set W := appendIdemPlus Q Λ Λc j hj ν ν₀ i * σ' 1 * (aB⁺ w.1.unop * aB⁺ 1) with hWdef
    have hc' : X * W = W * X := by
      have := hc.eq
      rw [hWdef]
      simp only [mul_assoc] at this ⊢
      exact this
    have hW1 : σ' 1 * W = W := by
      rw [hWdef]
      simp only [← mul_assoc]
      rw [← hσe, mul_assoc (appendIdemPlus Q Λ Λc j hj ν ν₀ i) (σ' 1) (σ' 1), hσ]
    have hW2 : W * aB⁺ 1 = W := by
      rw [hWdef]
      simp only [mul_assoc, hBB]
    calc σ' 1 * (X * σ' 1) * σ' 1 * W = σ' 1 * X * (σ' 1 * (σ' 1 * W)) := by
          simp only [mul_assoc]
      _ = X * W := by rw [hW1, hW1, ← hXσ, mul_assoc, hW1]
      _ = W * (X * aB⁺ 1) := by rw [← mul_assoc W X, ← hc', mul_assoc X W, hW2]

end Categorification.Stendhal.CupCap
