/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnStayIndex
import Categorification.WeightedKLR.RedStrands.CommonUpperLoading

/-!
# Webster's order lowers the number of red–black pairs

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, proof of
Theorem 6.14 (second clause). For a loading `u`, the pairs of a red strand left of a black strand
(`redBlackPairs u`) and the pairs of a black strand left of a red strand together are all pairs
of a black and a red strand (`redBlackPairs_add_sum_blacksBefore`). Moving up in Webster's order
`s ≤ t` moves black strands to the left of red strands, so it lowers the number of red–black
pairs (`redBlackPairs_le_of_stendhalLE`).
-/

namespace Categorification.Stendhal

open KLR

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

/-- The number of black strands left of the red strand `λ_r`. -/
noncomputable def blacksBefore (u : Seq μ) (r : Fin ℓ) : ℕ :=
  (Finset.univ.filter fun y : Fin m => (u.lbl y).isLeft ∧ y < redPos u r).card

omit [DecidableEq I] in
/-- A loading has `|ν|` black strands. -/
theorem card_filter_isLeft (u : Seq μ) :
    (Finset.univ.filter fun y : Fin m => (u.lbl y).isLeft).card = Multiset.card ν := by
  have h := congrArg (Multiset.countP fun x : I ⊕ Fin ℓ => x.isLeft) u.2
  rw [Multiset.countP_map] at h
  rw [← Finset.filter_val, Finset.card_val] at h
  rw [h]
  simp [stendhalWeight, Multiset.countP_map]

/-- The black strands left of `λ_r`, label by label. -/
theorem blacksBefore_eq_sum (u : Seq μ) (r : Fin ℓ) :
    blacksBefore u r = ∑ i ∈ ν.toFinset, blackCount u r i := by
  simp_rw [blackCount_eq_card_lt_redPos, blacksBefore]
  rw [← Finset.card_biUnion]
  · congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Multiset.mem_toFinset]
    constructor
    · rintro ⟨hl, hy⟩
      obtain ⟨i, hi⟩ := Sum.isLeft_iff.1 hl
      have hm := u.mem y
      rw [show u.1 y = u.lbl y from rfl, hi] at hm
      exact ⟨i, by simpa [stendhalWeight] using hm, hi, hy⟩
    · rintro ⟨i, -, hi, hy⟩
      exact ⟨by rw [hi]; rfl, hy⟩
  · intro i _ j _ hij
    refine Finset.disjoint_left.2 fun y hy hy' => hij ?_
    simp only [Finset.mem_filter] at hy hy'
    exact Sum.inl_injective (hy.2.1.symm.trans hy'.2.1)

/-- **Red–black and black–red pairs** together are all `ℓ |ν|` pairs of a black and a red
strand. -/
theorem redBlackPairs_add_sum_blacksBefore (u : Seq μ) :
    redBlackPairs u + ∑ r, blacksBefore u r = ℓ * Multiset.card ν := by
  have h1 : redBlackPairs u = ∑ y : Fin m, ∑ r : Fin ℓ,
      if (u.lbl y).isLeft ∧ redPos u r < y then 1 else 0 := by
    unfold redBlackPairs
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [redsBefore_lbl, Finset.card_filter]
    split_ifs with hl
    · exact Finset.sum_congr rfl fun r _ => if_congr ⟨fun h => ⟨hl, h⟩, fun h => h.2⟩ rfl rfl
    · exact (Finset.sum_eq_zero fun r _ => by simp [hl]).symm
  have h2 : ∑ r, blacksBefore u r = ∑ y : Fin m, ∑ r : Fin ℓ,
      if (u.lbl y).isLeft ∧ y < redPos u r then 1 else 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => by rw [blacksBefore, Finset.card_filter]
  rw [h1, h2, ← Finset.sum_add_distrib, ← card_filter_isLeft u, Finset.card_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_add_distrib]
  split_ifs with hl
  · rw [mul_one]
    refine (Finset.sum_congr rfl fun r _ => (?_ : _ = 1)).trans (by simp)
    have hne : y ≠ redPos u r := fun h => by
      have := lbl_redPos u r
      rw [← h] at this
      rw [this] at hl
      exact absurd hl (by simp)
    rcases lt_or_gt_of_ne hne with h | h
    · simp [hl, h, h.not_gt]
    · simp [hl, h, h.not_gt]
  · simp [hl]

/-- **Webster's order lowers the red–black pairs**: if `s ≤ t` then `t` has at most as many
pairs of a red strand left of a black strand as `s`. -/
theorem redBlackPairs_le_of_stendhalLE {s t : Seq μ} (h : StendhalLE s t) :
    redBlackPairs t ≤ redBlackPairs s := by
  have hs := redBlackPairs_add_sum_blacksBefore s
  have ht := redBlackPairs_add_sum_blacksBefore t
  have hle : ∑ r, blacksBefore s r ≤ ∑ r, blacksBefore t r :=
    Finset.sum_le_sum fun r _ => by
      rw [blacksBefore_eq_sum, blacksBefore_eq_sum]
      exact Finset.sum_le_sum fun i _ => h r i
  omega

end Categorification.Stendhal
