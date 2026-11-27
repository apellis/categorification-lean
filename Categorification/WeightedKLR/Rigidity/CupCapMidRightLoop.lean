/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Rigidity.CupCapMidLeftLoop
import Categorification.WeightedKLR.Rigidity.CupCapMidSlides
import Categorification.WeightedKLR.Rigidity.CupCapModelInverse
import Categorification.WeightedKLR.Rigidity.CupCapRightDescent

/-!
# The pull-off identity in the model of a cap after `λ_j`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17 and Lemma 7.16. Let `Y` be the model of
`K̃^{λ⁺}_λ` with the maximum of the cap just before the red strand `λ_{j+1}` (`CupCap.MidModel`).
Below the cap generators at a loading `s` of `λ`, let the strand of `s` just right of `λ_{j+1}`,
at `c + 1` with `c = midPos j s`, be black of colour `i`. Crossing it with `λ_{j+1}` gives the
loading `s' = s_c • s` with the black strand at `c`; below the cap generators at `s'` and `c`, the
window of the maximum at `c` is followed by the black strand at `c + N`. The block of the window
and this strand (`CupCap.blockStendhal`) carries a copy of the module induced along adjoining a
black strand on the right, and the crossing `ψ_{c+N}` of the black strand with `λ_{j+1}`
intertwines it with `Y` exactly (`CupCap.intertwinesOn_rightBlock`). This carries the pull-off
identity of `L` (`CupCap.PullOff`) to `Y` (`CupCap.rightLoop_midModel`): the black strand, pulled
under the maximum to the left and back, multiplies by the scalar of (max1).

## Main results

* `CupCap.loop_value_right`, `CupCap.unit_value_right`: the transported loop and unit.
* `CupCap.intertwinesOn_rightBlock`: the crossing with `λ_{j+1}` intertwines the block with the
  model.
* `CupCap.rightLoop_midModel`: the loop on the right of the maximum in the model, from `PullOff`.
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

theorem mul_mul_mul_eq_of_idem {R : Type*} [Semiring R] {e el l : R} (h1 : e * e = e)
    (h2 : e * el = e) (h3 : l * e = e * l) : e * e * (el * l) * e = l * e := by
  rw [h1, ← mul_assoc e el l, h2, ← h3, mul_assoc, h1]

section Values

variable (i : I) (t : Seq (stendhalWeight ℓ ν)) {n : ℕ}
  (hn : n + 1 ≤ Multiset.card (stendhalWeight ℓ ν))
  (ht : t.lbl ⟨n, by omega⟩ = .inl i)

include hn

local notation "θ" => blockStendhal Q Λ Λc j hj ν₀ i t n hn
local notation "lb" => leftBlockMap j hj i Q Λ Λc t n hn
local notation "RO" => redOrderedKLR k Q Λc ((Singleton.singleton i : Multiset I) + ν₀)
local notation "Et" => E t n (Nat.le_of_succ_le hn)

/-- The loop of the black strand at `n + N` commutes with the window idempotent at `n`. -/
theorem underLeft_underRight_mul_eSum :
    ((underLeft N n * underRight N n : Rp) * Et) = Et * (underLeft N n * underRight N n) := by
  rw [mul_assoc, underRight_mul_eSum Q Λ Λc t hn, ← mul_assoc, underLeft_mul_eSum t hn,
    mul_assoc]

include ht in
/-- The value of the transported loop. -/
theorem loop_value_right (Z : Rp) :
    bot (Z * Et) * θ (appendBlackStendhal Q Λc i ν₀ 1 * pullOffLoop k Q Λc ν₀ i) * θ 1 * bot Et =
      bot (Z * (underLeft N n * underRight N n) * Et) := by
  rw [map_mul (blockStendhal Q Λ Λc j hj ν₀ i t n hn),
    blockStendhal_appendBlack_one (ν₀ := ν₀) Q Λ Λc i t hn ht, pullOffLoop,
    blockStendhal_cupMap, blockStendhal_one_mid, blockBot_apply, blockBot_apply]
  have hR := botMap_leftBlockMap_redOrdered_mul_append (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i t
    hn ht
  rw [map_mul] at hR
  have hE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) t n (Nat.le_of_succ_le hn))).eq
  have hEL := eSum_insertSet_mul_eSum_leftBlockSet (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i t hn ht
  calc bot (Z * Et) * (bot Et * (bot (lb (underLeft N 0 * underRight N 0)).val *
          bot (lb RO).val)) * bot (lb RO).val * bot Et =
        bot (Z * Et) * bot Et * bot (lb (underLeft N 0 * underRight N 0)).val *
          (bot (lb RO).val * bot (lb RO).val * bot Et) := by
        simp only [mul_assoc]
    _ = bot (Z * (Et * Et * (lb (underLeft N 0 * underRight N 0)).val * Et)) := by
        rw [bot_leftBlockMap_redOrdered_idem_mid, hR]
        simp only [map_mul, mul_assoc]
    _ = _ := by
        rw [leftBlockMap_underLeft_underRight,
          mul_mul_mul_eq_of_idem hE hEL (underLeft_underRight_mul_eSum Q Λ Λc t hn)]
        simp only [mul_assoc]

include ht in
/-- The value of the transported unit. -/
theorem unit_value_right (Z : Rp) :
    bot (Z * Et) * θ (appendBlackStendhal Q Λc i ν₀ 1) * θ 1 * bot Et = bot (Z * Et) := by
  have hR := botMap_leftBlockMap_redOrdered_mul_append (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i t
    hn ht
  rw [map_mul] at hR
  have hE := (KLRAlgebra.eSum_idem (Q := stendhalQ Q (plusLabels Λ Λc j hj))
    (insertSet (j := j) (hj := hj) (ν₀ := ν₀) t n (Nat.le_of_succ_le hn))).eq
  rw [blockStendhal_appendBlack_one (ν₀ := ν₀) Q Λ Λc i t hn ht, blockStendhal_one_mid,
    mul_assoc _ _ (bot _), hR]
  calc bot (Z * Et) * bot Et * bot Et = bot (Z * (Et * Et) * Et) := by
        simp only [map_mul, mul_assoc]
    _ = bot (Z * Et) := by rw [hE, mul_assoc, hE]

end Values

omit [DecidableEq I] in
/-- The black strand of `s` right of `λ_{j+1}` is at `midPos j s` after crossing it with
`λ_{j+1}`. -/
theorem lbl_sadj_midPos {i : I} (s : Seq (stendhalWeight ℓ ν)) (hc1 : midPos j s + 1 < m)
    (hs : s.lbl ⟨midPos j s + 1, hc1⟩ = .inl i) :
    (sadj m (midPos j s) • s).lbl ⟨midPos j s, by omega⟩ = .inl i :=
  (lbl_sadj_of_swapNat s hc1 _ _ (by simp [swapNat])).trans hs

variable (L : Type*) [AddCommGroup L] [Module (StendhalAlgebra k Q Λc ν₀)ᵐᵒᵖ L]

/-- **The crossing with `λ_{j+1}` intertwines the block with the model**: when the strand of `s`
right of `λ_{j+1}` is black of colour `i`, the black-appending map followed by the block map at
`s_c • s` is the diagram at the maximum below the cap generators at `s`, up to the crossing
`ψ_{c+N}` of the black strand with `λ_{j+1}`. -/
theorem intertwinesOn_rightBlock (i : I) (s : Seq (stendhalWeight ℓ ν))
    (hc1 : midPos j s + 1 < m) (hs : s.lbl ⟨midPos j s + 1, hc1⟩ = .inl i) :
    IntertwinesOn L ((blockOpMid Q Λ Λc ν₀ i (sadj m (midPos j s) • s) (midPos j s)
        (by omega)).comp (appendBlackTildeOp k Q Λc ν₀ i))
      (midOp j hj Q Λ Λc ν ν₀) (midGen j hj Q Λ Λc ν ν₀ (bot (KLRAlgebra.ψ (midPos j s + N) *
        E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s)))).1 where
  unit := (midGen j hj Q Λ Λc ν ν₀ (bot (KLRAlgebra.ψ (midPos j s + N) *
    E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s)))).2
  slide a z v := by
    refine IntertwinesOn.slide_of_eq _ ?_ z v
    obtain ⟨w, hw⟩ := cupMap_surjective Q Λc a.unop
    obtain rfl : a = op (cupMap k Q Λc ν₀ w) := by rw [hw, op_unop]
    have hn : midPos j s + 1 ≤ m := by omega
    have hs' := lbl_sadj_midPos s hc1 hs
    have he : σ 1 * σ 1 = σ 1 := by rw [← map_mul, one_mul]
    have hc' := (commute_midStendhal_one_midBot (j := j) (hj := hj) (Q := Q) (Λ := Λ)
      (Λc := Λc) (ν := ν) w).eq
    have hcr : crossPos (midPos j s) N (midPos j s) = midPos j s + N := by simp [crossPos]
    have hψι := ψ_crossPos_mul_insertMap (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
      (ν₀ := ν₀) (sadj m (midPos j s) • s) (midPos_le j s) (p := midPos j s) (Or.inr le_rfl) w
    rw [hcr, sadj_smul_sadj_smul] at hψι
    have hψE := ψ_crossPos_mul_eSum (Q := Q) (Λ := Λ) (Λc := Λc) (j := j) (hj := hj)
      (ν₀ := ν₀) (sadj m (midPos j s) • s) (midPos_le j s) (p := midPos j s) (Or.inr le_rfl)
    rw [hcr, sadj_smul_sadj_smul] at hψE
    change op (blockStendhal Q Λ Λc j hj ν₀ i (sadj m (midPos j s) • s) (midPos j s) hn
        (appendBlackStendhal Q Λc i ν₀ (cupMap k Q Λc ν₀ w))) *
        op (σ 1 * bot (KLRAlgebra.ψ (midPos j s + N) *
          E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s))) =
      op (σ 1 * bot (KLRAlgebra.ψ (midPos j s + N) *
          E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s))) *
        op (σ (cupMap k Q Λc ν₀ w))
    rw [blockStendhal_appendBlack Q Λ Λc i _ hn hs', midStendhal_cupMap', ← op_mul, ← op_mul]
    congr 1
    calc σ 1 * bot (KLRAlgebra.ψ (midPos j s + N) *
          E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s)) *
          bot (ι (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s) w) =
        σ 1 * bot (KLRAlgebra.ψ (midPos j s + N) *
          ι (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s) w) := by
          rw [mul_assoc, ← map_mul, mul_assoc,
            ← insertMap_one Q Λ Λc (sadj m (midPos j s) • s) (midPos_le j s),
            ← insertMap_mul, one_mul]
      _ = σ 1 * (midBot j hj Q Λ Λc ν ν₀ w * bot (E s (midPos j s) (midPos_le j s))) *
          bot (KLRAlgebra.ψ (midPos j s + N)) := by
          rw [hψι, midBot_mul_botMap_eSum, map_mul, mul_assoc]
      _ = σ 1 * midBot j hj Q Λ Λc ν ν₀ w * (σ 1 * bot (KLRAlgebra.ψ (midPos j s + N) *
          E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s))) := by
          rw [hψE, map_mul, ← mul_assoc (σ 1 * midBot j hj Q Λ Λc ν ν₀ w) (σ 1),
            mul_assoc (σ 1) (midBot j hj Q Λ Λc ν ν₀ w) (σ 1), ← hc', ← mul_assoc (σ 1) (σ 1), he]
          simp only [mul_assoc]

/-- **The loop on the right of the maximum in the model of a cap after `λ_j`**, from the
pull-off identity of `L` (Webster, arXiv:1309.3796v3, Lemma 7.16): below the cap generators at
`s`, with the black strand of colour `i` just right of `λ_{j+1}` at `midPos j s + 1`, crossing it
with `λ_{j+1}`, pulling it under the maximum to the left and back multiplies by the scalar of
(max1). -/
theorem rightLoop_midModel (hP : PullOff k Q Λc ν₀ L) (i : I) (s : Seq (stendhalWeight ℓ ν))
    (hc1 : midPos j s + 1 < m) (hs : s.lbl ⟨midPos j s + 1, hc1⟩ = .inl i) (v : L) :
    (Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (KLRAlgebra.ψ (midPos j s + N) *
        (underLeft N (midPos j s) * underRight N (midPos j s)) *
        E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s)))) v :
          MidModel j hj Q Λ Λc ν ν₀ L) =
      Ind.tmul (midGen j hj Q Λ Λc ν ν₀ (bot (KLRAlgebra.ψ (midPos j s + N) *
        E (sadj m (midPos j s) • s) (midPos j s) (midPos_le j s))))
        (op (algebraMap k (StendhalAlgebra k Q Λc ν₀) (cupScalar Q ν₀ i)) • v) := by
  have hn : midPos j s + 1 ≤ m := by omega
  have hs' := lbl_sadj_midPos s hc1 hs
  have hX := intertwinesOn_rightBlock (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc L i s hc1 hs
  have h := congrArg (fun t => (op (bot (E (sadj m (midPos j s) • s) (midPos j s)
      (midPos_le j s))) : Tpᵐᵒᵖ) •
    natMapOn hX (compInner (appendBlackTildeOp k Q Λc ν₀ i)
      (blockOpMid Q Λ Λc ν₀ i (sadj m (midPos j s) • s) (midPos j s) hn)
      (unitGen _) t)) (hP i v)
  simp only [compInner_tmul, natMapOn_tmul, Ind.smul_tmul] at h
  have hl := loop_value_right (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i _ hn hs'
    (KLRAlgebra.ψ (midPos j s + N))
  have hu := unit_value_right (j := j) (hj := hj) (ν₀ := ν₀) Q Λ Λc i _ hn hs'
    (KLRAlgebra.ψ (midPos j s + N))
  convert h using 2 <;> apply Subtype.ext <;>
    change (op _ : Tpᵐᵒᵖ) = (op _ : Tpᵐᵒᵖ) * ((op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ) * (op _ : Tpᵐᵒᵖ))
  · conv_lhs => rw [← hl]
    simp only [← op_mul, mul_assoc]; rfl
  · conv_lhs => rw [← hu]
    simp only [← op_mul, mul_assoc]; rfl

end Categorification.Stendhal.CupCap
