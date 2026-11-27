/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftLoop
import Categorification.WeightedKLR.Rigidity.CupCapMidAction

/-!
# The mirrored pull-off identity along a passage, in the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17. Let `Y` be the model of `K̃^{λ⁺}_λ` with
the maximum of the cap just before the red strand `λ_{j+1}` (`CupCap.MidModel`), at
`c = midPos j s` below the cap generators at a loading `s` of `λ`. Let the strand of `s` at `n`,
with `n + 1 ≤ c`, be black of colour `i`. Below the passage `U` of the strands of `s` at
`n + 1, …, c - 1` under the maximum (`CupCap.passU`), the strand at `n`, pulled under the maximum
to the right and back, multiplies by the scalar of (max1) (`CupCap.leftLoop_midPass`). For
`n + 1 = c` the passage is trivial and this is `CupCap.leftLoop_midModel`; in general the
diagrams at the maximum slide through the passage up to diagrams in which a strand leaves the
window, which vanish in `Y`, so the passage element intertwines the block with the model on
`L` (`CupCap.intertwinesOn_midPassElt`).

## Main results

* `CupCap.midPassElt`: the passage element `e · E_{s,c} · U`.
* `CupCap.intertwinesOn_midPassElt`: it intertwines the block with the model.
* `CupCap.leftLoop_midPass`: (max2) along a passage, from `PullOffLeft`.
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

variable (j hj ν ν₀) in
/-- The passage of the strands at `n + 1, …, midPos j s - 1` under the maximum. -/
abbrev midPass (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) : Rp :=
  passU Q Λ Λc j hj ν ν₀ (n + 1) (midPos j s - (n + 1))

theorem midPass_mul_eSum (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hc : n + 1 ≤ midPos j s) :
    midPass j hj Q Λ Λc ν ν₀ s n * E s (n + 1) (hc.trans (midPos_le j s)) =
      E s (midPos j s) (midPos_le j s) * midPass j hj Q Λ Λc ν ν₀ s n := by
  have h := passU_mul_eSum (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc s (n + 1)
    (midPos j s - (n + 1)) (by have := midPos_le j s; omega)
  rwa [insertSet_congr' s (p := n + 1 + (midPos j s - (n + 1))) _ (midPos_le j s)
    (by omega)] at h

theorem slides_midPass (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hc : n + 1 ≤ midPos j s)
    (x : Rc) :
    ι s (midPos j s) (midPos_le j s) x * midPass j hj Q Λ Λc ν ν₀ s n -
        midPass j hj Q Λ Λc ν ν₀ s n * ι s (n + 1) (hc.trans (midPos_le j s)) x ∈
      exitSpan Q Λ Λc j hj s (midPos j s) (midPos_le j s) := by
  have h := slides_passU (j := j) (hj := hj) Q Λ Λc s (n + 1) x (midPos j s - (n + 1))
    (by have := midPos_le j s; omega)
  rwa [insertMap_congr' s (p := n + 1 + (midPos j s - (n + 1))) _ (midPos_le j s) (by omega),
    exitSpan_congr' s (p := n + 1 + (midPos j s - (n + 1))) _ (midPos_le j s) (by omega)] at h

variable (ν ν₀) in
/-- **The passage element**: `e · E_{s,c} · U`, with `U` the passage of the strands of `s` at
`n + 1, …, c - 1` under the maximum at `c = midPos j s`. -/
def midPassElt (s : Seq (stendhalWeight ℓ ν)) (n : ℕ) : Tpᵐᵒᵖ :=
  (midGen j hj Q Λ Λc ν ν₀ (bot (E s (midPos j s) (midPos_le j s) *
    midPass j hj Q Λ Λc ν ν₀ s n))).1

section Values

variable (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
  (hn : n + 1 ≤ Multiset.card (stendhalWeight ℓ ν))
  (hs : s.lbl ⟨n, by omega⟩ = .inl i)

include hn

local notation "θ" => blockStendhal Q Λ Λc j hj ν₀ i s n hn
local notation "lb" => leftBlockMap j hj i Q Λ Λc s n hn
local notation "RO" => redOrderedKLR k Q Λc ((Singleton.singleton i : Multiset I) + ν₀)

include hs in
/-- The value of the transported loop, below an arbitrary diagram `Z`. -/
theorem loop_value_pass (Z : Rp) :
    bot (Z * E s (n + 1) hn) *
        θ (prependBlackStendhal Q Λc i ν₀ 1 * pullOffLeftLoop k Q Λc ν₀ i) * θ 1 *
          bot (E s (n + 1) hn) =
      bot (Z * E s (n + 1) hn * (underRight N n * underLeft N n) * E s (n + 1) hn) := by
  rw [map_mul (blockStendhal Q Λ Λc j hj ν₀ i s n hn),
    blockStendhal_prependBlack_one_mid (ν₀ := ν₀) Q Λ Λc i s hn hs, pullOffLeftLoop,
    blockStendhal_cupMap, blockStendhal_one_mid, blockBot_apply, blockBot_apply]
  have hR := botMap_leftBlockMap_redOrdered_mul (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
  rw [map_mul] at hR
  have hE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (n + 1) hn)).eq
  calc bot (Z * E s (n + 1) hn) *
        (bot (E s (n + 1) hn) * (bot (lb (underRight N 0 * underLeft N 0)).val *
          bot (lb RO).val)) * bot (lb RO).val * bot (E s (n + 1) hn) =
        bot (Z * E s (n + 1) hn) * bot (E s (n + 1) hn) *
          bot (lb (underRight N 0 * underLeft N 0)).val *
            (bot (lb RO).val * bot (lb RO).val * bot (E s (n + 1) hn)) := by
        simp only [mul_assoc]
    _ = bot (Z * (E s (n + 1) hn * E s (n + 1) hn *
          (lb (underRight N 0 * underLeft N 0)).val * E s (n + 1) hn)) := by
        rw [bot_leftBlockMap_redOrdered_idem_mid, hR]
        simp only [map_mul, mul_assoc]
    _ = _ := by
        rw [leftBlockMap_underRight_underLeft, hE,
          ← mul_assoc (E s (n + 1) hn) (KLRAlgebra.eSum _ _),
          eSum_mul_eSum_leftBlockSet_mid Q Λ Λc i s hn hs]
        simp only [mul_assoc]

include hs in
/-- The value of the transported unit, below an arbitrary diagram `Z`. -/
theorem unit_value_pass (Z : Rp) :
    bot (Z * E s (n + 1) hn) * θ (prependBlackStendhal Q Λc i ν₀ 1) * θ 1 *
        bot (E s (n + 1) hn) = bot (Z * E s (n + 1) hn) := by
  have hR := botMap_leftBlockMap_redOrdered_mul (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
  rw [map_mul] at hR
  have hE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) s (n + 1) hn)).eq
  rw [blockStendhal_prependBlack_one_mid (ν₀ := ν₀) Q Λ Λc i s hn hs, blockStendhal_one_mid,
    mul_assoc _ _ (bot _), hR]
  calc bot (Z * E s (n + 1) hn) * bot (E s (n + 1) hn) * bot (E s (n + 1) hn) =
        bot (Z * (E s (n + 1) hn * E s (n + 1) hn) * E s (n + 1) hn) := by
        simp only [map_mul, mul_assoc]
    _ = bot (Z * E s (n + 1) hn) := by rw [hE, mul_assoc, hE]

end Values

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The passage element intertwines** the black-prepending map followed by the block map with
the diagrams at the maximum, on a module supported on the loadings `μ ⋯ μ*`. -/
theorem intertwinesOn_midPassElt
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ} (hc : n + 1 ≤ midPos j s)
    (hs : s.lbl ⟨n, by have := midPos_le j s; omega⟩ = .inl i) :
    IntertwinesOn L ((blockOpMid Q Λ Λc ν₀ i s n (hc.trans (midPos_le j s))).comp
        (prependBlackTildeOp k Q Λc ν₀ i))
      (midOp j hj Q Λ Λc ν ν₀) (midPassElt Q Λ Λc ν ν₀ s n) where
  unit := (midGen j hj Q Λ Λc ν ν₀ (bot (E s (midPos j s) (midPos_le j s) *
    midPass j hj Q Λ Λc ν ν₀ s n))).2
  slide a z v := by
    have hn : n + 1 ≤ m := hc.trans (midPos_le j s)
    refine IntertwinesOn.slide_of_mem_nullIdeal _ ?_ z v
    obtain ⟨w, hw⟩ := cupMap_surjective Q Λc a.unop
    obtain rfl : a = op (cupMap k Q Λc ν₀ w) := by rw [hw, op_unop]
    set P := midPass j hj Q Λ Λc ν ν₀ s n
    set Ec := E s (midPos j s) (midPos_le j s)
    have he : σ 1 * σ 1 = σ 1 := by rw [← map_mul, one_mul]
    have hcm := (commute_midStendhal_one_midBot (j := j) (hj := hj) (Q := Q) (Λ := Λ)
      (Λc := Λc) (ν := ν) w).eq
    have h1 : Ec * P * ι s (n + 1) hn w = P * ι s (n + 1) hn w := by
      rw [← midPass_mul_eSum Q Λ Λc s hc, mul_assoc, ← insertMap_one Q Λ Λc s hn,
        ← insertMap_mul, one_mul]
    have key : ((blockOpMid Q Λ Λc ν₀ i s n hn).comp (prependBlackTildeOp k Q Λc ν₀ i))
        (op (cupMap k Q Λc ν₀ w)) * midPassElt Q Λ Λc ν ν₀ s n -
          midPassElt Q Λ Λc ν ν₀ s n * midOp j hj Q Λ Λc ν ν₀ (op (cupMap k Q Λc ν₀ w)) =
        op (σ 1 * bot (-(ι s (midPos j s) (midPos_le j s) w * P - P * ι s (n + 1) hn w))) := by
      change op (blockStendhal Q Λ Λc j hj ν₀ i s n hn
          (prependBlackStendhal Q Λc i ν₀ (cupMap k Q Λc ν₀ w))) * op (σ 1 * bot (Ec * P)) -
        op (σ 1 * bot (Ec * P)) * op (σ (cupMap k Q Λc ν₀ w)) = _
      rw [blockStendhal_prependBlack Q Λ Λc i s hn hs, midStendhal_cupMap', ← op_mul, ← op_mul,
        ← op_sub]
      congr 1
      have l1 : σ 1 * bot (Ec * P) * bot (ι s (n + 1) hn w) =
          σ 1 * bot (P * ι s (n + 1) hn w) := by
        rw [mul_assoc, ← map_mul, h1]
      have l2 : σ 1 * midBot j hj Q Λ Λc ν ν₀ w * (σ 1 * bot (Ec * P)) =
          σ 1 * bot (ι s (midPos j s) (midPos_le j s) w * P) := by
        rw [map_mul bot (ι s (midPos j s) (midPos_le j s) w), ← midBot_mul_botMap_eSum,
          map_mul bot Ec, mul_assoc (σ 1), ← mul_assoc (midBot j hj Q Λ Λc ν ν₀ w), ← hcm,
          ← mul_assoc (σ 1), ← mul_assoc (σ 1), he]
        simp only [mul_assoc]
        rfl
      rw [l1, l2, neg_sub, map_sub, mul_sub]
    rw [key]
    exact exitSpan_midPos_mem_nullIdeal L hL s (neg_mem (slides_midPass Q Λ Λc s hc w))

/-- **(max2) along a passage in the model of a cap after `λ_j`**, from the left pull-off
identity of `L`: below the cap generators at `s`, with the black strand of colour `i` at `n` and
`n + 1 ≤ midPos j s`, the strand pulled under the maximum to the right and back, below the
passage of the strands at `n + 1, …, midPos j s - 1`, multiplies by the scalar of (max1). -/
theorem leftLoop_midPass
    (hL : ∀ (w : Seq (stendhalWeight 2 ν₀)) (v : L), ¬ IsCapGood ν₀ w →
      op (cupMap k Q Λc ν₀ (KLRAlgebra.e w)) • v = 0)
    (hP : PullOffLeft k Q Λc ν₀ L) (i : I) (s : Seq (stendhalWeight ℓ ν)) {n : ℕ}
    (hc : n + 1 ≤ midPos j s) (hs : s.lbl ⟨n, by have := midPos_le j s; omega⟩ = .inl i)
    (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (E s (midPos j s) (midPos_le j s) *
        midPass j hj Q Λ Λc ν ν₀ s n * (underRight N n * underLeft N n) *
        E s (n + 1) (hc.trans (midPos_le j s))))) v : MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (E s (midPos j s) (midPos_le j s) *
        midPass j hj Q Λ Λc ν ν₀ s n * E s (n + 1) (hc.trans (midPos_le j s)))))
        (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v) := by
  have hn : n + 1 ≤ m := hc.trans (midPos_le j s)
  have hX := intertwinesOn_midPassElt (hj := hj) Q Λ Λc L hL i s hc hs
  have h := congrArg (fun t => (op (bot (E s (n + 1) hn)) : Tpᵐᵒᵖ) •
    natMapOn hX (compInner (prependBlackTildeOp k Q Λc ν₀ i) (blockOpMid Q Λ Λc ν₀ i s n hn)
      (unitGen _) t)) (hP i v)
  simp only [compInner_tmul, natMapOn_tmul, Ind.smul_tmul] at h
  have hEP : E s (midPos j s) (midPos_le j s) * midPass j hj Q Λ Λc ν ν₀ s n =
      E s (midPos j s) (midPos_le j s) * midPass j hj Q Λ Λc ν ν₀ s n * E s (n + 1) hn := by
    rw [mul_assoc, midPass_mul_eSum Q Λ Λc s hc, ← mul_assoc,
      (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj)) _).eq]
  have hl := loop_value_pass (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
    (E s (midPos j s) (midPos_le j s) * midPass j hj Q Λ Λc ν ν₀ s n)
  have hu := unit_value_pass (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i s hn hs
    (E s (midPos j s) (midPos_le j s) * midPass j hj Q Λ Λc ν ν₀ s n)
  rw [← hEP] at hl hu
  convert h using 2 <;> apply Subtype.ext <;>
    change (op _ : Tpᵐᵒᵖ) = (op _ : Tpᵐᵒᵖ) * ((op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ))
  · conv_lhs => rw [← hl]
    simp only [← op_mul, mul_assoc]; rfl
  · conv_lhs => rw [← hEP, ← hu]
    simp only [← op_mul, mul_assoc]; rfl

end Categorification.Stendhal.CupCap
