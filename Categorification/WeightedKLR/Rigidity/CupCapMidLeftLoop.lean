/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidNull
import Categorification.WeightedKLR.Rigidity.CupCapMidSlides
import Categorification.WeightedKLR.Rigidity.CupCapLeftLoop

/-!
# The mirrored pull-off identity in the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. Let `Y` be the model of `K̃^{λ⁺}_λ` with
the maximum of the cap just before the red strand `λ_{j+1}` (`CupCap.MidModel`). Below the cap
generators at a loading `s` of `λ`, let the strand of `s` just left of the maximum, at `n` with
`n + 1 = midPos j s`, be black of colour `i`. The block of this strand and the window at `n + 1`
(`CupCap.blockStendhal`) carries a copy of the module induced along adjoining a black strand on
the left; the window idempotent intertwines it with `Y` exactly
(`CupCap.intertwinesOn_midBlock`). This carries the left pull-off identity of `L`
(`CupCap.PullOffLeft`) to `Y` (`CupCap.leftLoop_midModel`): the strand at `n`, pulled under the
maximum to the right and back, multiplies by the scalar of (max1).

## Main results

* `CupCap.blockOpMid`: the block map on the opposite rings.
* `CupCap.intertwinesOn_midBlock`: the window idempotent intertwines the block with the model.
* `CupCap.leftLoop_midModel`: the loop on the left of the maximum in the model, from
  `PullOffLeft`.
-/

noncomputable section

namespace Categorification.Stendhal.CupCap

open KLR KLRAlgebra TypeA MulOpposite InductionAlong

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k] {ℓ : ℕ} {j : ℕ} {hj : j ≤ ℓ}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin ℓ → I →₀ ℕ) (Λc : Fin 2 → I →₀ ℕ)
  {ν ν₀ : Multiset I}

local notation "m" => Multiset.card (stendhalWeight ℓ ν)
local notation "N" => Multiset.card (stendhalWeight 2 ν₀)
local notation "Tp" => StendhalAlgebra k Q (plusLabels Λ Λc j hj) (ν + ν₀)
local notation "Rp" =>
  KLRAlgebra k (stendhalQ Q (plusLabels Λ Λc j hj)) (stendhalWeight (ℓ + 2) (ν + ν₀))
local notation "Rc" => KLRAlgebra k (stendhalQ Q Λc) (stendhalWeight 2 ν₀)
local notation "ι" => insertMap (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc
local notation "E" s:max n:max hn:max =>
  KLRAlgebra.eSum (stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s n hn)
local notation "bot" => botMap k Q Λ Λc j hj ν ν₀
local notation "σ" => midStendhal j hj Q Λ Λc ν ν₀

variable (ν₀) in
/-- The block map on the opposite rings, for a cap after `λ_j`. -/
def blockOpMid (i : I) (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) (hn : n + 1 ≤ m) :
    (StendhalAlgebra k Q Λc ({i} + ν₀))ᵐᵒᵖ →ₙ+* Tpᵐᵒᵖ :=
  NonUnitalRingHom.op (NonUnitalRingHomClass.toNonUnitalRingHom
    (blockStendhal Q Λ Λc j hj ν₀ i s n hn))

section Values

variable (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
  (hn : n + 1 ≤ Multiset.card (stendhalWeight ℓ ν))
  (hs : s.lbl ⟨n, by omega⟩ = .inl i)

include hn

local notation "θ" => blockStendhal Q Λ Λc j hj ν₀ i s n hn
local notation "lb" => leftBlockMap j hj i Q Λ Λc s n hn
local notation "RO" => redOrderedKLR k Q Λc ((Singleton.singleton i : Multiset I) + ν₀)

include hs in
theorem blockStendhal_prependBlack_one_mid :
    θ (prependBlackStendhal Q Λc i ν₀ 1) = bot (E s (n + 1) hn) := by
  have h := blockStendhal_prependBlack (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs 1
  rwa [map_one, insertMap_one] at h

theorem blockStendhal_one_mid : θ 1 = bot (lb RO).val := by
  have h := blockStendhal_cupMap (ν₀ := ν₀) (j := j) (hj := hj) Q Λ Λc i s hn 1
  rwa [map_one, blockBot_apply, blockBot_apply, ← map_mul, ← Corner.val_mul, ← map_mul,
    one_mul] at h

theorem bot_leftBlockMap_redOrdered_idem_mid :
    bot (lb RO).val * bot (lb RO).val = bot (lb RO).val := by
  classical
  rw [← map_mul, ← Corner.val_mul, ← map_mul]
  congr 3
  exact (KLRAlgebra.eSum_idem (Q := stendhalQ Q Λc) (Finset.univ.filter fun t => IsRedOrdered t)).eq

include hs in
theorem eSum_mul_eSum_leftBlockSet_mid :
    (E s (n + 1) hn * KLRAlgebra.eSum _ (leftBlockSet j hj ν₀ i s n hn) : Rp) =
      E s (n + 1) hn := by
  have h := KLR.Corner.val_mul_E (lb (prependKLR ν₀ i Q Λc 1))
  rwa [leftBlockMap_prepend_one (j := j) (hj := hj) (ν₀ := ν₀) i Q Λ Λc s hn hs] at h

include hs in
/-- The value of the transported loop. -/
theorem loop_value_mid :
    bot (E s (n + 1) hn) *
        θ (prependBlackStendhal Q Λc i ν₀ 1 * pullOffLeftLoop k Q Λc ν₀ i) * θ 1 *
          bot (E s (n + 1) hn) =
      bot (E s (n + 1) hn * (underRight N n * underLeft N n) * E s (n + 1) hn) := by
  rw [map_mul (blockStendhal Q Λ Λc j hj ν₀ i s n hn),
    blockStendhal_prependBlack_one_mid (ν₀ := ν₀) Q Λ Λc i s hn hs, pullOffLeftLoop,
    blockStendhal_cupMap, blockStendhal_one_mid, blockBot_apply, blockBot_apply]
  have hR := botMap_leftBlockMap_redOrdered_mul (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
  rw [map_mul] at hR
  have hE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (n + 1) hn)).eq
  calc bot (E s (n + 1) hn) *
        (bot (E s (n + 1) hn) * (bot (lb (underRight N 0 * underLeft N 0)).val *
          bot (lb RO).val)) * bot (lb RO).val * bot (E s (n + 1) hn) =
        bot (E s (n + 1) hn) * bot (E s (n + 1) hn) *
          bot (lb (underRight N 0 * underLeft N 0)).val *
            (bot (lb RO).val * bot (lb RO).val * bot (E s (n + 1) hn)) := by
        simp only [mul_assoc]
    _ = bot (E s (n + 1) hn * E s (n + 1) hn *
          (lb (underRight N 0 * underLeft N 0)).val * E s (n + 1) hn) := by
        rw [bot_leftBlockMap_redOrdered_idem_mid, hR]
        simp only [map_mul]
    _ = _ := by
        rw [leftBlockMap_underRight_underLeft, hE,
          ← mul_assoc (E s (n + 1) hn) (KLRAlgebra.eSum _ _),
          eSum_mul_eSum_leftBlockSet_mid Q Λ Λc i s hn hs]

include hs in
/-- The value of the transported unit. -/
theorem unit_value_mid :
    bot (E s (n + 1) hn) * θ (prependBlackStendhal Q Λc i ν₀ 1) * θ 1 *
        bot (E s (n + 1) hn) = bot (E s (n + 1) hn) := by
  have hR := botMap_leftBlockMap_redOrdered_mul (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
  rw [map_mul] at hR
  have hE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (n + 1) hn)).eq
  rw [blockStendhal_prependBlack_one_mid (ν₀ := ν₀) Q Λ Λc i s hn hs, blockStendhal_one_mid,
    mul_assoc _ _ (bot _), hR, ← map_mul, ← map_mul, hE, hE]

end Values

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The window idempotent intertwines the block with the model**: when the strand of `s` at
`n` is black and `n + 1 = midPos j s`, the black-prepending map followed by the block map is the
diagram at the maximum below the cap generators at `s`. -/
theorem intertwinesOn_midBlock (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) (hc : n + 1 = midPos j s) (hs : s.lbl ⟨n, by omega⟩ = .inl i) :
    IntertwinesOn L ((blockOpMid Q Λ Λc ν₀ i s n hn).comp (prependBlackTildeOp k Q Λc ν₀ i))
      (midOp j hj Q Λ Λc ν ν₀) (midGen j hj Q Λ Λc ν ν₀ (bot (E s (n + 1) hn))).1 where
  unit := (midGen j hj Q Λ Λc ν ν₀ (bot (E s (n + 1) hn))).2
  slide a z v := by
    refine IntertwinesOn.slide_of_eq _ ?_ z v
    obtain ⟨w, hw⟩ := cupMap_surjective Q Λc a.unop
    obtain rfl : a = op (cupMap k Q Λc ν₀ w) := by rw [hw, op_unop]
    have he : σ 1 * σ 1 = σ 1 := by rw [← map_mul, one_mul]
    have hc' := (commute_midStendhal_one_midBot (j := j) (hj := hj) (Q := Q) (Λ := Λ)
      (Λc := Λc) (ν := ν) w).eq
    have hE : (E s (n + 1) hn : Rp) = E s (midPos j s) (midPos_le j s) := by
      rw [insertSet_congr' s hn (midPos_le j s) hc]
    have hι : ι s (n + 1) hn w = ι s (midPos j s) (midPos_le j s) w :=
      insertMap_congr' s hn (midPos_le j s) hc w
    change op (blockStendhal Q Λ Λc j hj ν₀ i s n hn
        (prependBlackStendhal Q Λc i ν₀ (cupMap k Q Λc ν₀ w))) * op (σ 1 * bot (E s (n + 1) hn)) =
      op (σ 1 * bot (E s (n + 1) hn)) * op (σ (cupMap k Q Λc ν₀ w))
    rw [blockStendhal_prependBlack Q Λ Λc i s hn hs, midStendhal_cupMap', ← op_mul, ← op_mul]
    congr 1
    rw [mul_assoc, ← map_mul, ← insertMap_one Q Λ Λc s hn, ← insertMap_mul, one_mul,
      mul_assoc (σ 1), ← mul_assoc (midBot j hj Q Λ Λc ν ν₀ w), ← hc', ← mul_assoc (σ 1),
      ← mul_assoc (σ 1), he, mul_assoc, insertMap_one, hE, midBot_mul_botMap_eSum, hι]

/-- **The loop on the left of the maximum in the model of a cap after `λ_j`**, from the left
pull-off identity of `L`: below the cap generators at `s`, with the black strand of colour `i`
at `n` just left of the maximum at `n + 1 = midPos j s`, the strand pulled under the maximum to
the right and back multiplies by the scalar of (max1). -/
theorem leftLoop_midModel
    (hP : PullOffLeft k Q Λc ν₀ L) (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hn : n + 1 ≤ m) (hc : n + 1 = midPos j s) (hs : s.lbl ⟨n, by omega⟩ = .inl i) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (E s (n + 1) hn * (underRight N n * underLeft N n) *
        E s (n + 1) hn))) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (E s (n + 1) hn)))
        (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v) := by
  have hX := intertwinesOn_midBlock (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc L i s hn hc hs
  have h := congrArg (fun t => (op (bot (E s (n + 1) hn)) : Tpᵐᵒᵖ) •
    natMapOn hX (compInner (prependBlackTildeOp k Q Λc ν₀ i) (blockOpMid Q Λ Λc ν₀ i s n hn)
      (unitGen _) t)) (hP i v)
  simp only [compInner_tmul, natMapOn_tmul, Ind.smul_tmul] at h
  have hl := loop_value_mid (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
  have hu := unit_value_mid (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
  simp only [mul_assoc] at hl hu
  convert h using 2 <;> apply Subtype.ext <;>
    change (op _ : Tpᵐᵒᵖ) = (op _ : Tpᵐᵒᵖ) * ((op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ)) <;>
    simp only [← op_mul, mul_assoc]
  · conv_lhs => rw [← hl]
    rfl
  · conv_lhs => rw [← hu]
    rfl

end Categorification.Stendhal.CupCap
