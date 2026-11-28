/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedPlus

/-!
# Appending two strands of different colours carries the crossing to the crossing, in the model

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the mixed crossing for `j < ℓ`. For colours `a`, `b`, on the image of appending
`b`, then `a`, the left action of minus the crossing of the two appended strands of `T̃^λ` is the
right action of minus the crossing `Y` of the two appended strands of `T̃^{λ⁺}` on the image of
appending `a`, then `b`, transported to the content `{a} + ({b} + ν)`
(`CupCap.appendIota_two_mixedCross`).
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

section Cast

variable {μ μ' : Multiset I} (h : μ = μ')

theorem midModel_cast_tmul (w : Corner (midOp j hj Q Λ Λc μ ν₀)) (v : L) :
    (h ▸ (Ind.tmul w v : MidModel j hj Q Λ Λc μ ν₀ L) : MidModel j hj Q Λ Λc μ' ν₀ L) =
      Ind.tmul (h ▸ w : Corner (midOp j hj Q Λ Λc μ' ν₀)) v := by
  subst h; rfl

theorem midModel_cast_add (y y' : MidModel j hj Q Λ Λc μ ν₀ L) :
    (h ▸ (y + y') : MidModel j hj Q Λ Λc μ' ν₀ L) =
      (h ▸ y : MidModel j hj Q Λ Λc μ' ν₀ L) + (h ▸ y' : MidModel j hj Q Λ Λc μ' ν₀ L) := by
  subst h; rfl

theorem midModel_cast_zero :
    (h ▸ (0 : MidModel j hj Q Λ Λc μ ν₀ L) : MidModel j hj Q Λ Λc μ' ν₀ L) = 0 := by
  subst h; rfl

theorem midCorner_cast_unop (w : Corner (midOp j hj Q Λ Λc μ ν₀)) :
    ((h ▸ w : Corner (midOp j hj Q Λ Λc μ' ν₀)) : (StendhalAlgebra k Q (plusLabels Λ Λc j hj)
        (μ' + ν₀))ᵐᵒᵖ).unop =
      castPlusStendhal Q (plusLabels Λ Λc j hj) (congrArg (· + ν₀) h)
        (w : (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (μ + ν₀))ᵐᵒᵖ).unop := by
  subst h; rfl

theorem castPlusStendhal_midStendhal_one :
    castPlusStendhal Q (plusLabels Λ Λc j hj) (congrArg (· + ν₀) h)
        (midStendhal j hj Q Λ Λc μ ν₀ 1) = midStendhal j hj Q Λ Λc μ' ν₀ 1 := by
  subst h; rfl

end Cast

section Corner

variable (μ : Multiset I) (c d : I)

/-- The value of appending `d`, then `c`, to a generator of the model, for `j < ℓ`. -/
theorem appendIdemPlus_two_corner (h : j < ℓ) (w' : StendhalAlgebra k Q (plusLabels Λ Λc j hj)
    (μ + ν₀)) :
    appendIdemPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c *
        midStendhal j hj Q Λ Λc (({c} : Multiset I) + (({d} : Multiset I) + μ)) ν₀ 1 *
        (appendBlackPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c
          (appendIdemPlus Q Λ Λc j hj μ ν₀ d *
            midStendhal j hj Q Λ Λc (({d} : Multiset I) + μ) ν₀ 1 *
            (appendBlackPlus Q Λ Λc j hj μ ν₀ d w' * appendBlackPlus Q Λ Λc j hj μ ν₀ d 1)) *
          appendBlackPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c 1) =
      appendBlackPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c
        (appendBlackPlus Q Λ Λc j hj μ ν₀ d (midStendhal j hj Q Λ Λc μ ν₀ 1 * w')) := by
  rw [appendIdemPlus_mul_midStendhal_one _ c h, appendIdemPlus_mul_midStendhal_one μ d h,
    ← appendBlackPlus_midStendhal_one _ c h, ← appendBlackPlus_midStendhal_one μ d h,
    ← map_mul (appendBlackPlus Q Λ Λc j hj μ ν₀ d) w' 1, mul_one,
    ← map_mul (appendBlackPlus Q Λ Λc j hj μ ν₀ d),
    ← map_mul (appendBlackPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c) _ 1, mul_one,
    ← map_mul (appendBlackPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c),
    midStendhal_one_mul_appendBlackPlus μ d h]

end Corner

section Model

variable (ν : Multiset I) (a b : I)
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}

local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "νba" =>
  ((Singleton.singleton b : Multiset I) + ((Singleton.singleton a : Multiset I) + ν))
local notation "aBb" => appendBlackPlus Q Λ Λc j hj ν ν₀ b
local notation "aBa" => appendBlackPlus Q Λ Λc j hj νb ν₀ a
local notation "Y" => mixedLastCross k Q Λ Λc j hj ν ν₀ a b

/-- **Appending two strands of different colours carries the crossing to the crossing**, for
`j < ℓ` (arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): on the image of appending `b`,
then `a`, the left action of minus the crossing of the two appended strands of `T̃^λ` times their
unit is the right action of minus the crossing `Y` of the two appended strands of `T̃^{λ⁺}` times
their unit, on the image of appending `a`, then `b`, transported to `{a} + ({b} + ν)`. -/
theorem appendIota_two_mixedCross (h : j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hRb : MidKLRRel j hj Q Λ Λc νb ν₀ L hL) (hRab : MidKLRRel j hj Q Λ Λc νab ν₀ L hL)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midLeftAlg L hL hRab (orderProjection Q Λ νab
        (-StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight ℓ ν))) *
        appendBlackStendhal Q Λ a νb (appendBlackStendhal Q Λ b ν 1))
        (appendIota νb a L h (appendIota ν b L h y)) =
      op (-(Y * aBa (aBb 1))) •
        (mixedSwap ν a b ▸ appendIota νa b L h (appendIota ν a L h y) :
          MidModel j hj Q Λ Λc νab ν₀ L) := by
  rw [map_mul, Module.End.mul_apply, ← appendIota_midLeftAlg νb a h hRb hRab,
    ← appendIota_midLeftAlg ν b h hR hRb 1, map_one, Module.End.one_apply]
  have hY : orderProjection Q Λ νab
      (-StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight ℓ ν))) =
      topMap k Q Λ νab (-(KLRAlgebra.ψ (Multiset.card (stendhalWeight ℓ ν)))) := by
    rw [map_neg, map_neg]; rfl
  rw [hY, map_neg, map_neg, midLeftAlg_topMap, LinearMap.neg_apply, midKLRAct_ψ, op_neg, neg_smul,
    neg_inj]
  induction y using Ind.induction_on with
  | zero =>
    have h0 : ∀ (μ : Multiset I) (c : I), appendIota (j := j) (hj := hj) (Q := Q) (Λ := Λ)
        (Λc := Λc) (ν₀ := ν₀) μ c L h 0 = 0 := fun μ c => by
      rw [appendIota, Ind.tmul_zero, map_zero]
    rw [h0, h0, h0, h0, map_zero, midModel_cast_zero, smul_zero]
  | add x y hx hy =>
    rw [appendIota_add, appendIota_add, appendIota_add, appendIota_add, map_add, hx, hy,
      midModel_cast_add, smul_add]
  | tmul w v =>
    rw [appendIota_tmul, appendIota_tmul, appendIota_tmul, appendIota_tmul, midEnd,
      midModel_cast_tmul]
    change natMapOn _ (Ind.tmul _ v) = _
    rw [natMapOn_tmul, Ind.smul_tmul]
    congr 1
    apply Subtype.ext
    apply MulOpposite.unop_injective
    have hA : ∀ (μ : Multiset I) (c : I) x, (appendBlackPlusOp Q Λ Λc j hj μ ν₀ c x).unop =
        appendBlackPlus Q Λ Λc j hj μ ν₀ c x.unop := fun _ _ _ => rfl
    change (_ * midElt j hj Q Λ Λc νab ν₀ _).unop = (op (Y * aBa (aBb 1)) * _).unop
    rw [unop_mul, unop_mul, midCorner_cast_unop]
    simp only [midElt, unop_mul, unop_op, appendMidOp_apply _ _ h, midOp_apply, unop_one,
      cornerMul, compMul, unitGen, hA]
    rw [appendIdemPlus_two_corner ν a b h, appendIdemPlus_two_corner ν b a h]
    set w' := (w : (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ).unop
    set W := aBa (aBb (midStendhal j hj Q Λ Λc ν ν₀ 1 * w')) with hWdef
    set W' := appendBlackPlus Q Λ Λc j hj νa ν₀ b
      (appendBlackPlus Q Λ Λc j hj ν ν₀ a (midStendhal j hj Q Λ Λc ν ν₀ 1 * w')) with hW'def
    have f1 : midStendhal j hj Q Λ Λc νab ν₀ 1 * W = W :=
      midStendhal_one_mul_appendBlackPlus_mixed ν a b h w'
    have f2 : botMap k Q Λ Λc j hj νab ν₀
        (midCross j hj Q Λ Λc νab ν₀ (Multiset.card (stendhalWeight ℓ ν))) * W = Y * W := by
      have e : W = aBa (aBb (midStendhal j hj Q Λ Λc ν ν₀ 1)) * W := by
        rw [hWdef, ← map_mul, ← map_mul, ← mul_assoc, ← map_mul, one_mul]
      rw [e, ← mul_assoc, botMap_midCross_mul_appendBlackPlus_mixed ν a b h, mul_assoc, ← e]
    have f4 := lastCross_mul_appendBlackPlus_mixed (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
      (hj := hj) (ν₀ := ν₀) ν a b (midStendhal j hj Q Λ Λc ν ν₀ 1 * w')
    have f5 : midStendhal j hj Q Λ Λc νab ν₀ 1 *
        castPlusStendhal Q (plusLabels Λ Λc j hj) (congrArg (· + ν₀) (mixedSwap ν a b)) W' =
        castPlusStendhal Q (plusLabels Λ Λc j hj) (congrArg (· + ν₀) (mixedSwap ν a b)) W' := by
      rw [← castPlusStendhal_midStendhal_one (mixedSwap ν a b), ← map_mul,
        midStendhal_one_mul_appendBlackPlus_mixed ν b a h]
    have f3 := lastCross_mul_appendBlackPlus_mixed (Q := Q) (Λ := Λ) (Λc := Λc) (j := j)
      (hj := hj) (ν₀ := ν₀) ν a b 1
    have f6 : W' * appendBlackPlus Q Λ Λc j hj νa ν₀ b (appendBlackPlus Q Λ Λc j hj ν ν₀ a 1) =
        W' := by
      rw [hW'def, ← map_mul, ← map_mul, mul_one]
    rw [mul_assoc _ _ W, f1, mul_assoc, f2, f4, ← mul_assoc, f5, f3, ← mul_assoc, ← map_mul, f6]

end Model

end Categorification.Stendhal.CupCap
