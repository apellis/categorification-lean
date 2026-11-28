/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedModel
import Categorification.WeightedKLR.Rigidity.CupCapProp721AppendMixedTopPass

/-!
# Appending two strands of different colours under the window, in the model

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §7.3, proof of
Proposition 7.21, the mixed crossing for a cap at the right end (`j = ℓ`). For colours `a`, `b`,
on the image of appending `b`, then `a`, which passes the two new strands under the window, the
left action of minus the crossing of the two appended strands of `T̃^λ` is the right action of
minus the crossing `Y` of the two appended strands of `T̃^{λ⁺}` on the image of appending `a`,
then `b`, transported to the content `{a} + ({b} + ν)` (`CupCap.appendTopIota_two_mixedCross`).
The two sides differ by diagrams in which a strand leaves the window at the top
(`CupCap.midCross_mul_topPass_mixed_sub_mem`), which vanish in the model.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type} [CommRing k] {ℓ : ℕ}
  {Q : I → I → MvPolynomial (Fin 2) k} {Λ : Fin ℓ → I →₀ ℕ} {Λc : Fin 2 → I →₀ ℕ}
  {j : ℕ} {hj : j ≤ ℓ} {ν₀ : Multiset I}
  {L : Type} [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

theorem castPlusStendhal_botMap {μ μ' : Multiset I} (h : μ = μ')
    (y : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (μ + ν₀))) :
    castPlusStendhal Q (plusLabels Λ Λc j hj) (congrArg (· + ν₀) h)
        (botMap k Q Λ Λc j hj μ ν₀ y) =
      botMap k Q Λ Λc j hj μ' ν₀ (castKLR (stendhalQ Q (plusLabels Λ Λc j hj))
        (congrArg (fun μ => stendhalWeight (ℓ + 2) (μ + ν₀)) h) y) := by
  subst h; rfl

/-- Corner elements whose difference lies in the null ideal give the same element of the
model. -/
theorem midModel_tmul_eq_of_sub_mem {μ : Multiset I} {c c' : Corner (midOp j hj Q Λ Λc μ ν₀)}
    (h : c.1 - c'.1 ∈ nullIdeal L (midOp j hj Q Λ Λc μ ν₀)) (v : L) :
    (Ind.tmul c v : MidModel j hj Q Λ Λc μ ν₀ L) = Ind.tmul c' v := by
  have hsplit : c = ⟨c.1 - c'.1, mem_lIdeal_of_mem_nullIdeal h⟩ + c' :=
    Subtype.ext (by change c.1 = c.1 - c'.1 + c'.1; rw [sub_add_cancel])
  rw [hsplit, Ind.add_tmul, tmul_eq_zero_of_mem_nullIdeal h, zero_add]

section Model

variable (ν : Multiset I) (a b : I)
  (hP : PullOff k Q Λc ν₀ L) (hPL : PullOffLeft k Q Λc ν₀ L)
  {hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
    op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0}
  (hκ : ∀ i', IsUnit (cupScalar Q ν₀ i'))

local notation "νa" => ((Singleton.singleton a : Multiset I) + ν)
local notation "νb" => ((Singleton.singleton b : Multiset I) + ν)
local notation "νab" =>
  ((Singleton.singleton a : Multiset I) + ((Singleton.singleton b : Multiset I) + ν))
local notation "aBb" => appendBlackPlus Q Λ Λc j hj ν ν₀ b
local notation "aBa" => appendBlackPlus Q Λ Λc j hj νb ν₀ a
local notation "Y" => mixedLastCross k Q Λ Λc j hj ν ν₀ a b

include hL in
/-- **Diagrams in which a strand leaves the window vanish in the model**: for `y` in `midExit`,
`e y` lies in the null ideal. -/
theorem midExit_mem_nullIdeal {μ : Multiset I}
    {y : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (μ + ν₀))}
    (hy : y ∈ midExit j hj Q Λ Λc μ ν₀) :
    op (midStendhal j hj Q Λ Λc μ ν₀ 1 * botMap k Q Λ Λc j hj μ ν₀ y) ∈
      nullIdeal L (midOp j hj Q Λ Λc μ ν₀) := by
  refine Submodule.iSup_induction _ (motive := fun y => op (midStendhal j hj Q Λ Λc μ ν₀ 1 *
      botMap k Q Λ Λc j hj μ ν₀ y) ∈ nullIdeal L (midOp j hj Q Λ Λc μ ν₀)) hy
    (fun s y hy => exitSpan_midPos_mem_nullIdeal L hL s hy) ?_ ?_
  · rw [map_zero, mul_zero, op_zero]; exact zero_mem _
  · intro y y' h h'; rw [map_add, mul_add, op_add]; exact add_mem h h'

/-- **Appending two strands of different colours carries the crossing to the crossing**, for
`j = ℓ` (arXiv:1309.3796v3, §7.3, proof of Proposition 7.21): on the image of appending `b`,
then `a`, the left action of minus the crossing of the two appended strands of `T̃^λ` times their
unit is the right action of minus the crossing `Y` of the two appended strands of `T̃^{λ⁺}` times
their unit, on the image of appending `a`, then `b`, transported to `{a} + ({b} + ν)`. Route
hypotheses (tracked): `hκ`, `hP`, `hPL`. -/
theorem appendTopIota_two_mixedCross (h : ¬ j < ℓ) (hR : MidKLRRel j hj Q Λ Λc ν ν₀ L hL)
    (hRb : MidKLRRel j hj Q Λ Λc νb ν₀ L hL) (hRab : MidKLRRel j hj Q Λ Λc νab ν₀ L hL)
    (y : MidModel j hj Q Λ Λc ν ν₀ L) :
    midLeftAlg L hL hRab (orderProjection Q Λ νab
        (-StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight ℓ ν))) *
        appendBlackStendhal Q Λ a νb (appendBlackStendhal Q Λ b ν 1))
        (appendTopIota νb a hP hPL hL hκ h (appendTopIota ν b hP hPL hL hκ h y)) =
      op (-(Y * aBa (aBb 1))) •
        (mixedSwap ν a b ▸ appendTopIota νa b hP hPL hL hκ h (appendTopIota ν a hP hPL hL hκ h y) :
          MidModel j hj Q Λ Λc νab ν₀ L) := by
  rw [map_mul, Module.End.mul_apply, ← appendTopIota_midLeftAlg νb a hP hPL hL hκ h hRb hRab,
    ← appendTopIota_midLeftAlg ν b hP hPL hL hκ h hR hRb 1, map_one, Module.End.one_apply]
  have hY : orderProjection Q Λ νab
      (-StendhalAlgebraAllOrders.ψ (Multiset.card (stendhalWeight ℓ ν))) =
      topMap k Q Λ νab (-(KLRAlgebra.ψ (Multiset.card (stendhalWeight ℓ ν)))) := by
    rw [map_neg, map_neg]; rfl
  rw [hY, map_neg, map_neg, midLeftAlg_topMap, LinearMap.neg_apply, midKLRAct_ψ, op_neg, neg_smul,
    neg_inj]
  induction y using Ind.induction_on with
  | zero =>
    have h0 : ∀ (μ : Multiset I) (c : I), appendTopIota (j := j) (hj := hj) (Q := Q) (Λ := Λ)
        (Λc := Λc) (ν₀ := ν₀) μ c hP hPL hL hκ h 0 = 0 := fun μ c => by
      rw [appendTopIota, Ind.tmul_zero, map_zero]; rfl
    rw [h0, h0, h0, h0, map_zero, midModel_cast_zero, smul_zero]
  | add x y hx hy =>
    rw [appendTopIota_add, appendTopIota_add, appendTopIota_add, appendTopIota_add, map_add, hx, hy,
      midModel_cast_add, smul_add]
  | tmul w v =>
    rw [appendTopIota_tmul, appendTopIota_tmul, appendTopIota_tmul, appendTopIota_tmul, midEnd,
      midModel_cast_tmul]
    change natMapOn _ (Ind.tmul _ v) = _
    rw [natMapOn_tmul, Ind.smul_tmul]
    have hy := midCross_mul_topPass_mixed_sub_mem (Q := Q) (Λ := Λ) (Λc := Λc) (hj := hj)
      (ν₀ := ν₀) ν a b h
    set w' := (w : (StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀))ᵐᵒᵖ).unop with hw'
    refine midModel_tmul_eq_of_sub_mem ?_ v
    convert mul_mem_nullIdeal (op (aBa (aBb w'))) (midExit_mem_nullIdeal (hL := hL) hy) using 1
    apply MulOpposite.unop_injective
    have hA : ∀ (μ : Multiset I) (c : I) x, (appendBlackPlusOp Q Λ Λc j hj μ ν₀ c x).unop =
        appendBlackPlus Q Λ Λc j hj μ ν₀ c x.unop := fun _ _ _ => rfl
    rw [unop_sub, unop_mul, unop_op, unop_op]
    change _ - (op (Y * aBa (aBb 1)) * _).unop = _
    rw [unop_mul, midCorner_cast_unop]
    simp only [cornerMulOf_val, midElt, compMul, unitGen, unop_mul, unop_op, hA, unop_one]
    have hZ : ∀ (μ : Multiset I) (c d : I) (W : StendhalAlgebra k Q (plusLabels Λ Λc j hj)
        (μ + ν₀)) (X : KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj))
          (stendhalWeight (ℓ + 2) (({d} : Multiset I) + μ + ν₀))),
        appendBlackPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c
            (botMap k Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ X *
              (appendBlackPlus Q Λ Λc j hj μ ν₀ d W * appendBlackPlus Q Λ Λc j hj μ ν₀ d 1)) *
          appendBlackPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c 1 =
        botMap k Q Λ Λc j hj (({c} : Multiset I) + (({d} : Multiset I) + μ)) ν₀
            (appendPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c X) *
          appendBlackPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c
            (appendBlackPlus Q Λ Λc j hj μ ν₀ d W) := fun μ c d W X => by
      rw [← map_mul (appendBlackPlus Q Λ Λc j hj (({d} : Multiset I) + μ) ν₀ c) _ 1, mul_one,
        ← map_mul (appendBlackPlus Q Λ Λc j hj μ ν₀ d) W 1, mul_one, map_mul,
        appendBlackPlus_botMap]
    rw [hZ, hZ, ← hw']
    set σ := midStendhal j hj Q Λ Λc νab ν₀ 1 with hσ
    set B := botMap k Q Λ Λc j hj νab ν₀ with hB
    set cst := castPlusStendhal Q (plusLabels Λ Λc j hj) (congrArg (· + ν₀) (mixedSwap ν a b))
      with hcst
    have f1 : σ * B (topPass νb a) = B (topPass νb a) := by
      rw [hσ, hB, midStendhal_one_eq_botMap, ← map_mul, sum_midIdem_mul_topPass νb a h]
    have f2 : midStendhal j hj Q Λ Λc (({b} : Multiset I) + νa) ν₀ 1 *
        botMap k Q Λ Λc j hj (({b} : Multiset I) + νa) ν₀ (topPass νa b) =
        botMap k Q Λ Λc j hj (({b} : Multiset I) + νa) ν₀ (topPass νa b) := by
      rw [midStendhal_one_eq_botMap, ← map_mul, sum_midIdem_mul_topPass νa b h]
    have g1 : cst (botMap k Q Λ Λc j hj (({b} : Multiset I) + νa) ν₀ (topPass νa b) *
        (botMap k Q Λ Λc j hj (({b} : Multiset I) + νa) ν₀
          (appendPlus Q Λ Λc j hj νa ν₀ b (topPass ν a)) *
          appendBlackPlus Q Λ Λc j hj νa ν₀ b (appendBlackPlus Q Λ Λc j hj ν ν₀ a w'))) =
        σ * B (castKLR (stendhalQ Q (plusLabels Λ Λc j hj))
          (stendhalWeight_mixedSwap (ℓ := ℓ) (ν₀ := ν₀) ν a b)
          (topPass νa b * appendPlus Q Λ Λc j hj νa ν₀ b (topPass ν a))) *
        cst (appendBlackPlus Q Λ Λc j hj νa ν₀ b (appendBlackPlus Q Λ Λc j hj ν ν₀ a w')) := by
      rw [← f2, map_mul, map_mul, map_mul, hcst, castPlusStendhal_midStendhal_one (mixedSwap ν a b),
        castPlusStendhal_botMap (mixedSwap ν a b), castPlusStendhal_botMap (mixedSwap ν a b),
        map_mul (castKLR _ _), hB, map_mul]
      simp only [hσ, mul_assoc]
    have g2 : cst (appendBlackPlus Q Λ Λc j hj νa ν₀ b (appendBlackPlus Q Λ Λc j hj ν ν₀ a w')) *
        (Y * aBa (aBb 1)) = Y * aBa (aBb w') := by
      rw [← mul_assoc, hcst, ← lastCross_mul_appendBlackPlus_mixed, mul_assoc, ← map_mul,
        ← map_mul, mul_one]
    have hYψ : Y = B (KLRAlgebra.ψ (Multiset.card (stendhalWeight ℓ ν) +
        Multiset.card (stendhalWeight 2 ν₀))) := by
      rw [mixedLastCross, card_plus']
    have hσσ : ∀ X, σ * B ((∑ u, midIdem j hj Q Λ Λc νab ν₀ u) * X) = σ * B X := fun X => by
      rw [map_mul, hB, ← midStendhal_one_eq_botMap, ← hB, ← mul_assoc, hσ,
        midStendhal_one_mul_self]
    rw [g1, mul_assoc _ (cst _), g2, hσσ, hYψ, map_sub, map_mul B (castKLR _ _ _), map_mul B,
      map_mul B (topPass νb a), mul_assoc (σ * B _) σ, ← mul_assoc σ (B (topPass νb a)), f1]
    simp only [mul_sub, sub_mul, mul_assoc]

end Model

end Categorification.Stendhal.CupCap
