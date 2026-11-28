/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.SubwordBruhatOrder

/-!
# Rank numbers and the Bruhat order

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.19: the filtration of the window part of
`S_+(Z ⊠ N)` by the number of strands passing the window is indexed by a rank number of the
permutation of a diagram, and the filtration is preserved because rank numbers only decrease
along the Bruhat order (the straightening of (B2) produces only Bruhat-lower terms).

For `w ∈ S_m` the rank number `r_w(i, t)` (`rankNum`) is the number of positions `a < i` with
`w(a) ≥ t`. We prove:

* `rankNum_mul_of_forall_lt_iff`, `rankNum_mul_left_of_forall_le_iff`: `r_{x w y}(i, t) =
  r_w(i, t)` when `y` preserves `{a < i}` and `x` preserves `{b ≥ t}`; so a rank number at a cut
  of the top parabolic and a cut of the bottom parabolic is constant on double cosets
  (`rankNum_mul_mul`).
* `rankNum_le_of_mem_subProds`: if `v` is a subword product of a reduced word of `w`, then
  `r_v ≤ r_w` pointwise; equivalently (`BruhatLE.rankNum_le`) rank numbers are monotone in the
  Bruhat order. This is one half of the rank criterion for the Bruhat order of `S_m`.

## Main definitions

* `TypeA.rankNum`.

## Main results

* `TypeA.rankNum_mul_mul`, `TypeA.BruhatLE.rankNum_le`.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

/-- The rank number `r_w(i, t)`: the number of positions `a < i` with `w(a) ≥ t`. -/
def rankNum (m : ℕ) (w : Perm (Fin m)) (i t : ℕ) : ℕ :=
  (Finset.univ.filter fun a : Fin m => (a : ℕ) < i ∧ t ≤ (w a : ℕ)).card

/-- Right multiplication by a permutation preserving `{a < i}` does not change `r(i, ·)`. -/
theorem rankNum_mul_of_forall_lt_iff (w y : Perm (Fin m)) {i : ℕ}
    (hy : ∀ a : Fin m, (y a : ℕ) < i ↔ (a : ℕ) < i) (t : ℕ) :
    rankNum m (w * y) i t = rankNum m w i t := by
  unfold rankNum
  have hyb : ∀ b, y (y⁻¹ b) = b := fun b => by simp
  refine Finset.card_bij' (fun a _ => y a) (fun b _ => y⁻¹ b) (fun a ha => ?_) (fun b hb => ?_)
    (fun a _ => by simp) (fun b _ => hyb b)
  · rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, (hy a).2 ha.2.1, ha.2.2⟩
  · rw [Finset.mem_filter] at hb ⊢
    refine ⟨Finset.mem_univ _, (hy _).1 (by rw [hyb]; exact hb.2.1), ?_⟩
    change t ≤ (w (y (y⁻¹ b)) : ℕ)
    rw [hyb]
    exact hb.2.2

/-- Left multiplication by a permutation preserving `{b ≥ t}` does not change `r(·, t)`. -/
theorem rankNum_mul_left_of_forall_le_iff (x w : Perm (Fin m)) {t : ℕ}
    (hx : ∀ b : Fin m, t ≤ (x b : ℕ) ↔ t ≤ (b : ℕ)) (i : ℕ) :
    rankNum m (x * w) i t = rankNum m w i t := by
  unfold rankNum
  congr 1
  refine Finset.filter_congr fun a _ => ?_
  rw [Perm.mul_apply, hx]

/-- **Rank numbers are double-coset invariants**: `r_{x w y}(i, t) = r_w(i, t)` when `y`
preserves `{a < i}` and `x` preserves `{b ≥ t}`. -/
theorem rankNum_mul_mul (x w y : Perm (Fin m)) {i t : ℕ}
    (hx : ∀ b : Fin m, t ≤ (x b : ℕ) ↔ t ≤ (b : ℕ))
    (hy : ∀ a : Fin m, (y a : ℕ) < i ↔ (a : ℕ) < i) :
    rankNum m (x * w * y) i t = rankNum m w i t := by
  rw [rankNum_mul_of_forall_lt_iff _ _ hy, rankNum_mul_left_of_forall_le_iff _ _ hx]

/-- `r_w(i + 1, t) = r_w(i, t) + [w(i) ≥ t]`. -/
theorem rankNum_succ (w : Perm (Fin m)) {i : ℕ} (hi : i < m) (t : ℕ) :
    rankNum m w (i + 1) t = rankNum m w i t + if t ≤ (w ⟨i, hi⟩ : ℕ) then 1 else 0 := by
  unfold rankNum
  have h : (if t ≤ (w ⟨i, hi⟩ : ℕ) then 1 else 0) =
      ∑ a : Fin m, if a = ⟨i, hi⟩ then (if t ≤ (w a : ℕ) then 1 else 0) else 0 := by
    rw [Finset.sum_ite_eq']
    simp
  rw [Finset.card_filter, Finset.card_filter, h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a = ⟨i, hi⟩
  · subst ha
    simp
  · have ha' : (a : ℕ) ≠ i := fun h => ha (Fin.ext h)
    by_cases hlt : (a : ℕ) < i
    · simp [hlt, ha, show (a : ℕ) < i + 1 by omega]
    · simp [hlt, ha, show ¬ (a : ℕ) < i + 1 by omega]

/-- `s_p` preserves `{a < i}` for `i ≠ p + 1`. -/
theorem sadj_lt_iff {p : ℕ} (hp : p + 1 < m) {i : ℕ} (hi : i ≠ p + 1) (a : Fin m) :
    (sadj m p a : ℕ) < i ↔ (a : ℕ) < i := by
  rw [sadj_val_of_lt hp]
  have := swapNat_cases p a
  omega

/-- The induction step of the rank criterion: if `r_v ≤ r_w` and `w(p) < w(p + 1)`, then `r_v`
and `r_{v s_p}` are both at most `r_{w s_p}`. -/
theorem rankNum_le_mul_sadj {p : ℕ} (hp : p + 1 < m) {v w : Perm (Fin m)}
    (hw : w ⟨p, by omega⟩ < w ⟨p + 1, hp⟩) (hvw : ∀ i t, rankNum m v i t ≤ rankNum m w i t)
    (i t : ℕ) :
    rankNum m v i t ≤ rankNum m (w * sadj m p) i t ∧
      rankNum m (v * sadj m p) i t ≤ rankNum m (w * sadj m p) i t := by
  by_cases hi : i = p + 1
  · subst hi
    have hp0 : p < m := by omega
    have h1 := hvw p t
    have h2 := hvw (p + 1) t
    have h3 := hvw (p + 2) t
    rw [rankNum_succ _ hp0] at h2 ⊢
    rw [rankNum_succ _ hp0, rankNum_succ _ hp0, rankNum_mul_of_forall_lt_iff _ _
      (sadj_lt_iff hp (by omega)), rankNum_mul_of_forall_lt_iff _ _ (sadj_lt_iff hp (by omega)),
      Perm.mul_apply, Perm.mul_apply, sadj_apply_left hp]
    rw [show p + 2 = p + 1 + 1 by omega, rankNum_succ _ hp, rankNum_succ _ hp0,
      rankNum_succ _ hp, rankNum_succ _ hp0] at h3
    have hA : t ≤ (w ⟨p, hp0⟩ : ℕ) → t ≤ (w ⟨p + 1, hp⟩ : ℕ) := fun h =>
      h.trans (Fin.lt_def.1 hw).le
    split_ifs at h2 h3 ⊢ <;> omega
  · rw [rankNum_mul_of_forall_lt_iff _ _ (sadj_lt_iff hp hi),
      rankNum_mul_of_forall_lt_iff _ _ (sadj_lt_iff hp hi)]
    exact ⟨hvw i t, hvw i t⟩

/-- **Rank numbers decrease along subwords**: if `γ` is a reduced word and `v` is the product of a
subword of `γ`, then `r_v ≤ r_w` pointwise, `w = wordProd m γ`. -/
theorem rankNum_le_of_mem_subProds {γ : List ℕ} (hγ : IsReduced m γ) {v : Perm (Fin m)}
    (hv : v ∈ subProds m γ) (i t : ℕ) : rankNum m v i t ≤ rankNum m (wordProd m γ) i t := by
  induction γ using List.reverseRecOn generalizing v i t with
  | nil =>
    rw [mem_subProds_nil.1 hv]
    exact le_rfl
  | append_singleton γ p ih =>
    have hp : p + 1 < m := hγ.1 p (by simp)
    have hval : ValidWord m γ := hγ.1.sublist (List.sublist_append_left γ [p])
    have hlen := hγ.2
    rw [wordProd_append, List.length_append] at hlen
    have hw : wordProd m γ ⟨p, by omega⟩ < wordProd m γ ⟨p + 1, hp⟩ := by
      have hne : wordProd m γ ⟨p, by omega⟩ ≠ wordProd m γ ⟨p + 1, hp⟩ := fun h => by
        have := (wordProd m γ).injective h
        simp [Fin.ext_iff] at this
      refine lt_of_le_of_ne (not_lt.1 fun hgt => ?_) hne
      have h1 := length_mul_sadj_of_gt hp hgt
      have h2 := length_wordProd_le (m := m) hval
      have h3 : wordProd m [p] = sadj m p := by simp [wordProd]
      rw [h3] at hlen
      simp only [List.length_singleton] at hlen
      omega
    have hred : IsReduced m γ := by
      rw [isReduced_iff_length_le hval]
      have h3 : wordProd m [p] = sadj m p := by simp [wordProd]
      rw [h3, length_mul_sadj_of_lt hp hw] at hlen
      simp only [List.length_singleton] at hlen
      omega
    have h3 : wordProd m [p] = sadj m p := by simp [wordProd]
    obtain ⟨u, hu, x, hx, rfl⟩ := mem_subProds_append.1 hv
    rw [wordProd_append, h3]
    have key := rankNum_le_mul_sadj hp hw (fun i t => ih hred hu i t) i t
    rcases mem_subProds_cons.1 hx with hx | ⟨y, hy, rfl⟩
    · rw [mem_subProds_nil.1 hx, mul_one]
      exact key.1
    · rw [mem_subProds_nil.1 hy, mul_one]
      exact key.2

/-- **Rank numbers are monotone in the Bruhat order.** -/
theorem BruhatLE.rankNum_le {v w : Perm (Fin m)} (h : BruhatLE m v w) (i t : ℕ) :
    rankNum m v i t ≤ rankNum m w i t := by
  have := rankNum_le_of_mem_subProds (isReduced_canWord m w) h i t
  rwa [wordProd_canWord] at this

end Categorification.TypeA
