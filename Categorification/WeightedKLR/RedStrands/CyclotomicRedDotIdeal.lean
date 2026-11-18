/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicPQ

/-!
# The cyclotomic ideal under the dotted red crossing

In the proof of Webster, arXiv:1309.3796v2, §4.5, Theorem 4.25, multiplication by the
last dot to the power `d = ⟨hᵢ, λ⟩` induces one of the two red/down crossings. On the
affine last-`i` corner the smaller cyclotomic ideal maps into the sum of the larger
cyclotomic ideal and `cycL0` for the smaller weight. For nonempty old content the latter
vanishes upon balancing against a module for the smaller cyclotomic block.
-/

namespace Categorification.KLR.KLRAlgebra

open MvPolynomial

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}
  (i : I) (β : Multiset I) (a b : I → Polynomial k) (d : ℕ)

local notation "Si" => (Singleton.singleton i : Multiset I)
local notation "R" => KLRAlgebra k Q (Si + β)

/-- On the first-`i` cut, the extra `d` dots change the smaller cyclotomic polynomial to
its multiple on this colour. The braid word in `tauW` is the same on both sides. -/
private theorem firstPow_tauW_cut (hi : b i = Polynomial.X ^ d * a i) :
    (x ⟨0, zero_lt_card_single_add i β⟩ : R) ^ d * oneConcat Q Si β *
      tauW a (zero_lt_card_single_add i β) β.card =
    oneConcat Q Si β * tauW b (zero_lt_card_single_add i β) β.card := by
  simp only [tauW, ← mul_assoc]
  congr 1
  rw [oneConcat_single_eq, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [mul_assoc, ← cycAt_mul_e', ← cycAt_mul_e', cycAt_mul_e, cycAt_mul_e, cons1_zero,
    pol_aeval_X, pol_aeval_X, hi, map_mul, map_pow, Polynomial.aeval_X, mul_assoc]

/-- On the last-`i` corner, multiplying the smaller cyclotomic ideal by the last-dot
power lands in the older-strand relations plus the larger cyclotomic ideal. This is the
affine ideal calculation for the dotted crossing in Webster v2, Theorem 4.25. -/
theorem redDot_cycIdeal_cut (hi : b i = Polynomial.X ^ d * a i) {z : R}
    (hz : z ∈ cycIdeal Q a (Si + β)) :
    z * x ⟨β.card, lastPos_lt i β⟩ ^ d * cL Q i β 1 ∈
      cycL0 a (zero_lt_card_single_add i β) ⊔ (cycIdeal Q b (Si + β)).asIdeal := by
  let h0 := zero_lt_card_single_add i β
  have hn := (card_single_add i β).symm
  let t : R := x ⟨β.card, lastPos_lt i β⟩ ^ d
  let eL : R := cL Q i β 1
  let eF : R := oneConcat Q Si β
  have ht : t ∈ subR0 (k := k) (Q := Q) (Si + β) :=
    Subalgebra.pow_mem _ (x_mem_subR0 _) d
  have he := cL_one_mem_subR0 (Q := Q) i β
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (cycIdeal_le a h0 β.card hn hz)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  change (u + c * tauW a h0 β.card) * t * eL ∈ _
  rw [add_mul, add_mul]
  apply Submodule.add_mem _ (Submodule.mem_sup_left (mul_mem_cycL0 a (mul_mem_cycL0 a hu ht) he))
  have hs := pol_mul_tauW (Q := Q) a h0 β.card hn (X ⟨0, h0⟩ ^ d)
  rw [map_pow, pol_X, map_pow, rename_X, cP_apply_zero _ hn h0, map_pow, pol_X] at hs
  have hd := mul_mem_cycL0 a (Submodule.neg_mem _ hs) he
  rw [neg_sub, sub_mul] at hd
  have hcut : ((x ⟨0, h0⟩ : R) ^ d * tauW a h0 β.card) * eL = eF * tauW b h0 β.card := by
    rw [mul_assoc, ← oneConcat_mul_tauW a i β, ← mul_assoc]
    exact firstPow_tauW_cut i β a b d hi
  rw [hcut] at hd
  have hb : eF * tauW b h0 β.card ∈ cycIdeal Q b (Si + β) :=
    TwoSidedIdeal.mul_mem_left _ _ _
      (TwoSidedIdeal.mul_mem_right _ _ _ (cycAt_mem_cycIdeal b h0))
  have hsum := Submodule.add_mem (cycL0 a h0 ⊔ (cycIdeal Q b (Si + β)).asIdeal)
    (Submodule.mem_sup_left hd) (Submodule.mem_sup_right hb)
  rw [sub_add_cancel] at hsum
  simpa only [smul_eq_mul, mul_assoc] using Submodule.smul_mem _ c hsum

end Categorification.KLR.KLRAlgebra
