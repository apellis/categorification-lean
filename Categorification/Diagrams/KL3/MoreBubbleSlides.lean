/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.BubbleSlidesProp

/-!
# KL III Proposition 3.4 (more bubble slides)

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Proposition 3.4 (TeX label `prop_bubble_slide2`): "These equations follow from the previous
Proposition." They are the inverse forms of Proposition 3.3, and are proved here from it by
the second-difference identity `second_difference` (case `i = j`, coefficients `α + 1 - ℓ`) and
by induction (case `i · j = -1`), in the range where all bubbles involved are real:

* `prop34_cw_same`, `prop34_ccw_same` (`i = j`);
* `prop34_cw_adj` (`i · j = -1`, `⟨i,λ⟩ ≥ 2`), `prop34_ccw_adj` (`⟨i,λ⟩ ≤ -1`).

The versions for all `α` (fake bubbles included) are in
`Categorification.Diagrams.KL3.BubbleSlidesAll`.
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

theorem sum_coeff_succ {M : Type*} [AddCommGroup M] (F : ℕ → M) (n : ℕ) :
    ∑ ℓ ∈ Finset.range (n + 2), (n + 2 - ℓ) • F ℓ =
      ∑ ℓ ∈ Finset.range (n + 1), (n + 1 - ℓ) • F ℓ + ∑ ℓ ∈ Finset.range (n + 2), F ℓ := by
  rw [Finset.sum_range_succ (fun ℓ => (n + 2 - ℓ) • F ℓ), Finset.sum_range_succ (fun ℓ => F ℓ),
    show n + 2 - (n + 1) = 1 by omega, one_smul, ← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [show n + 2 - ℓ = (n + 1 - ℓ) + 1 by omega, add_smul, one_smul]

/-- The second difference of the coefficient sequences `α + 1 - ℓ`:
`∑_{ℓ<α-1} (α-1-ℓ) F_ℓ - 2 ∑_{ℓ<α} (α-ℓ) F_ℓ + ∑_{ℓ≤α} (α+1-ℓ) F_ℓ = F_α`. -/
theorem second_difference {M : Type*} [AddCommGroup M] (F : ℕ → M) (α : ℕ) :
    ∑ ℓ ∈ Finset.range (α - 1), (α - 1 - ℓ) • F ℓ - 2 • ∑ ℓ ∈ Finset.range α, (α - ℓ) • F ℓ +
      ∑ ℓ ∈ Finset.range (α + 1), (α + 1 - ℓ) • F ℓ = F α := by
  rcases α with _ | _ | β
  · simp
  · simp [Finset.sum_range_succ, two_smul]; abel
  · rw [show β + 1 + 1 - 1 = β + 1 by omega, show β + 1 + 1 + 1 = (β + 1) + 2 by omega,
      show β + 1 + 1 = β + 2 by omega, sum_coeff_succ F (β + 1), show β + 1 + 1 = β + 2 by omega,
      sum_coeff_succ F β, Finset.sum_range_succ (fun ℓ => F ℓ) (β + 2)]
    abel

/-- A clockwise real bubble to the left of `E_i`, slid to the right with `dg_cw_slide_eq`, in
terms of `F_ℓ = cw_{n-1+ℓ} x^{α-ℓ}`: for `c ≤ 2` with `n + 1 + α - c ≥ 0`. -/
theorem cw_left_expand (lam : X) (i : I) (α c : ℕ) (hc : 0 ≤ ip RD i lam + 1 + ((α : ℤ) - c)) :
    (pres RD k).lin (bubL RD k lam [up i]
        (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - c)))) ≫
        dotsU RD k lam (up i) c =
      ∑ ℓ ∈ Finset.range (α + 1 - c), (α + 1 - c - ℓ) •
        (bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + ℓ)) ≫
          dotsU RD k lam (up i) (α - ℓ)) := by
  rw [cwL_of_nonneg RD k _ i hc, lin_bubL_cwReal, dg_cw_slide_eq, Preadditive.sum_comp]
  have e : (((ip RD i lam + 1 + ((α : ℤ) - c)).toNat : ℕ) : ℤ) + -ip RD i lam = α + 1 - c := by
    rw [Int.toNat_of_nonneg hc]; ring
  rw [e, show ((α : ℤ) + 1 - c).toNat = α + 1 - c by omega]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [Linear.smul_comp, Category.assoc, dotsU_add, show ((α : ℤ) + 1 - c - ℓ).toNat = α + 1 - c - ℓ by
    omega]
  congr 3
  omega

/-- **KL III Proposition 3.4, first display, `i = j`** (real bubbles): for `⟨i,λ⟩ - 1 + α ≥ 0`,
`cw_{⟨i,λ⟩-1+α} ⊗ E_i = (E_i ⊗ cw_{⟨i,λ⟩+1+(α-2)}) x² - 2 (E_i ⊗ cw_{⟨i,λ⟩+1+(α-1)}) x +
E_i ⊗ cw_{⟨i,λ⟩+1+α}` (the bubbles on the left in the region `λ + i_X`). -/
theorem prop34_cw_same (lam : X) (i : I) (α : ℕ) (hα : 0 ≤ ip RD i lam - 1 + α) :
    (pres RD k).lin (bubR RD k lam [up i] (cwL RD k lam i (ip RD i lam - 1 + α))) =
      (pres RD k).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - 2)))) ≫
          dotsU RD k lam (up i) 2 -
        2 • ((pres RD k).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - 1)))) ≫
          dotsU RD k lam (up i) 1) +
        (pres RD k).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + α))) := by
  have h₀ := cw_left_expand RD k lam i α 0 (by push_cast; omega)
  simp only [Nat.cast_zero, sub_zero, dotsU_zero, Category.comp_id, Nat.sub_zero] at h₀
  have h₂ := cw_left_expand RD k lam i α 2 (by push_cast; omega)
  have h₁ := cw_left_expand RD k lam i α 1 (by push_cast; omega)
  simp only [Nat.cast_ofNat, Nat.cast_one] at h₂ h₁
  rw [h₂, h₁, h₀, show α + 1 - 2 = α - 1 by omega, show α + 1 - 1 = α by omega]
  have h := second_difference (fun ℓ => bubRU RD k lam (up i) (cwU RD k lam i (ip RD i lam - 1 + ℓ)) ≫
    dotsU RD k lam (up i) (α - ℓ)) α
  simp only [Nat.sub_self, dotsU_zero, Category.comp_id] at h
  rw [lin_bubR_eq, h.symm]

/-- A counterclockwise real bubble to the right of `E_i`, slid to the left with
`dg_ccw_slide_eq`, in terms of `F_j = ccw'_{-N-1+j} x^{α-j}` (`N = ⟨i, λ+i_X⟩`). -/
theorem ccw_right_expand (lam : X) (i : I) (α c : ℕ) (hc : 0 ≤ -ip RD i lam - 1 + ((α : ℤ) - c)) :
    (pres RD k).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - c)))) ≫
        dotsU RD k lam (up i) c =
      ∑ j ∈ Finset.range (α + 1 - c), (α + 1 - c - j) •
        (bubLU RD k lam (up i) (ccwU RD k (wt RD lam [up i]) i
            (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫ dotsU RD k lam (up i) (α - j)) := by
  have hN : ip RD i (wt RD lam [up i]) = 2 + ip RD i lam := by rw [ip_wt_up, A_self]
  rw [ccwL_of_nonneg RD k _ i hc, lin_bubR_ccwReal, dg_ccw_slide_eq, Preadditive.sum_comp]
  have e : (((-ip RD i lam - 1 + ((α : ℤ) - c)).toNat : ℕ) : ℤ) + ip RD i (wt RD lam [up i]) =
      α + 1 - c := by
    rw [Int.toNat_of_nonneg hc, hN]; ring
  rw [e, show ((α : ℤ) + 1 - c).toNat = α + 1 - c by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.1 hj
  rw [Linear.smul_comp, Category.assoc, dotsU_add, show ((α : ℤ) + 1 - c - j).toNat = α + 1 - c - j by
    omega]
  congr 3
  omega

/-- **KL III Proposition 3.4, second display, `i = j`** (real bubbles): for
`-⟨i,λ⟩ - 3 + α ≥ 0`, `E_i ⊗ ccw_{-⟨i,λ+i_X⟩-1+α} = (ccw_{-⟨i,λ⟩-1+(α-2)} ⊗ E_i) x² -
2 (ccw_{-⟨i,λ⟩-1+(α-1)} ⊗ E_i) x + ccw_{-⟨i,λ⟩-1+α} ⊗ E_i`. -/
theorem prop34_ccw_same (lam : X) (i : I) (α : ℕ) (hα : 0 ≤ -ip RD i lam - 3 + α) :
    (pres RD k).lin (bubL RD k lam [up i]
        (ccwL RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + α))) =
      (pres RD k).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - 2)))) ≫
          dotsU RD k lam (up i) 2 -
        2 • ((pres RD k).lin (bubR RD k lam [up i]
          (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - 1)))) ≫ dotsU RD k lam (up i) 1) +
        (pres RD k).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + α))) := by
  have h₀ := ccw_right_expand RD k lam i α 0 (by push_cast; omega)
  simp only [Nat.cast_zero, sub_zero, dotsU_zero, Category.comp_id, Nat.sub_zero] at h₀
  have h₂ := ccw_right_expand RD k lam i α 2 (by push_cast; omega)
  have h₁ := ccw_right_expand RD k lam i α 1 (by push_cast; omega)
  simp only [Nat.cast_ofNat, Nat.cast_one] at h₂ h₁
  rw [h₂, h₁, h₀, show α + 1 - 2 = α - 1 by omega, show α + 1 - 1 = α by omega]
  have h := second_difference (fun j => bubLU RD k lam (up i) (ccwU RD k (wt RD lam [up i]) i
    (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫ dotsU RD k lam (up i) (α - j)) α
  simp only [Nat.sub_self, dotsU_zero, Category.comp_id] at h
  rw [lin_bubL_eq, h.symm]

/-- **KL III Proposition 3.4, first display, `i · j = -1`** (real bubbles): for `⟨i,λ⟩ ≥ 2`,
`cw_{⟨i,λ⟩-1+α} ⊗ E_j = ∑_{f=0}^{α} (-1)^f (E_j ⊗ cw_{⟨i,λ+j_X⟩-1+(α-f)}) x_j^f`. -/
theorem prop34_cw_adj (lam : X) (i j : I) (hij : C.dot i j = -1) (hn : 2 ≤ ip RD i lam) (α : ℕ) :
    (pres RD k).lin (bubR RD k lam [up j] (cwL RD k lam i (ip RD i lam - 1 + α))) =
      ∑ f ∈ Finset.range (α + 1), ((-1 : ℤ) ^ f) •
        ((pres RD k).lin (bubL RD k lam [up j]
            (cwL RD k (wt RD lam [up j]) i (ip RD i (wt RD lam [up j]) - 1 + ((α - f : ℕ) : ℤ)))) ≫
          dotsU RD k lam (up j) f) := by
  have hn' : ip RD i (wt RD lam [up j]) = -1 + ip RD i lam := by
    rw [ip_wt_up, A_of_dot_neg_one hij]
  induction α with
  | zero =>
    have h := prop33_cw_adj RD k lam i j hij 0 (by omega)
    have h0 : (pres RD k).lin (bubR RD k lam [up j] (cwL RD k lam i (ip RD i lam - 1 + (0 : ℕ) - 1))) = 0 := by
      rw [lin_bubR_eq, cwL_of_nonneg RD k lam i (by omega), lin_cwReal,
        dg_cwNeg RD k lam i _ (by omega)]
      exact map_zero _
    rw [h0, Limits.zero_comp, zero_add] at h
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, dotsU_zero,
      Category.comp_id, Nat.sub_zero]
    exact h.symm
  | succ α ih =>
    have h := prop33_cw_adj RD k lam i j hij (α + 1) (by omega)
    have e : ip RD i lam - 1 + ((α + 1 : ℕ) : ℤ) - 1 = ip RD i lam - 1 + (α : ℤ) := by push_cast; ring
    rw [e, ih] at h
    rw [eq_sub_of_add_eq' h.symm, Preadditive.sum_comp, Finset.sum_range_succ' _ (α + 1),
      pow_zero, one_smul, Nat.sub_zero, dotsU_zero, Category.comp_id, sub_eq_add_neg,
      ← Finset.sum_neg_distrib, add_comm (∑ _ ∈ _, _)]
    congr 1
    refine Finset.sum_congr rfl fun f hf => ?_
    have := Finset.mem_range.1 hf
    rw [Linear.smul_comp, Category.assoc, dotsU_add, pow_succ, mul_neg_one, neg_smul]
    rw [show α + 1 - (f + 1) = α - f by omega]

/-- **KL III Proposition 3.4, second display, `i · j = -1`** (real bubbles): for `⟨i,λ⟩ ≤ -1`,
`E_j ⊗ ccw_{-⟨i,λ+j_X⟩-1+α} = ∑_{f=0}^{α} (-1)^f (ccw_{-⟨i,λ⟩-1+(α-f)} ⊗ E_j) x_j^f`. -/
theorem prop34_ccw_adj (lam : X) (i j : I) (hij : C.dot i j = -1) (hn : ip RD i lam ≤ -1) (α : ℕ) :
    (pres RD k).lin (bubL RD k lam [up j]
        (ccwL RD k (wt RD lam [up j]) i (-ip RD i (wt RD lam [up j]) - 1 + α))) =
      ∑ f ∈ Finset.range (α + 1), ((-1 : ℤ) ^ f) •
        ((pres RD k).lin (bubR RD k lam [up j]
            (ccwL RD k lam i (-ip RD i lam - 1 + ((α - f : ℕ) : ℤ)))) ≫
          dotsU RD k lam (up j) f) := by
  have hn' : ip RD i (wt RD lam [up j]) = -1 + ip RD i lam := by
    rw [ip_wt_up, A_of_dot_neg_one hij]
  induction α with
  | zero =>
    have h := prop33_ccw_adj RD k lam i j hij 0 (by omega)
    have h0 : (pres RD k).lin (bubL RD k lam [up j] (ccwL RD k (wt RD lam [up j]) i
        (-ip RD i (wt RD lam [up j]) - 2 + (0 : ℕ)))) = 0 := by
      rw [lin_bubL_eq, ccwL_of_nonneg RD k _ i (by omega), lin_ccwReal,
        dg_ccwNeg RD k _ i _ (by omega)]
      exact map_zero _
    rw [h0, Limits.zero_comp, add_zero] at h
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, dotsU_zero,
      Category.comp_id, Nat.sub_zero]
    exact h.symm
  | succ α ih =>
    have h := prop33_ccw_adj RD k lam i j hij (α + 1) (by omega)
    have e : -ip RD i (wt RD lam [up j]) - 2 + ((α + 1 : ℕ) : ℤ) =
        -ip RD i (wt RD lam [up j]) - 1 + (α : ℤ) := by push_cast; ring
    rw [e, ih] at h
    rw [eq_sub_of_add_eq h.symm, Preadditive.sum_comp, Finset.sum_range_succ' _ (α + 1),
      pow_zero, one_smul, Nat.sub_zero, dotsU_zero, Category.comp_id, sub_eq_add_neg,
      ← Finset.sum_neg_distrib, add_comm (∑ _ ∈ _, _)]
    congr 1
    refine Finset.sum_congr rfl fun f hf => ?_
    have := Finset.mem_range.1 hf
    rw [Linear.smul_comp, Category.assoc, dotsU_add, pow_succ, mul_neg_one, neg_smul]
    rw [show α + 1 - (f + 1) = α - f by omega]

end Categorification.KL3.Diagram
