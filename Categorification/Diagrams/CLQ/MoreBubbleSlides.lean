/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.BubbleSlidesProp
import Categorification.Diagrams.KL3.MoreBubbleSlides

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

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)



/-- A clockwise real bubble to the left of `E_i`, slid to the right with `dg_cw_slide_eq`, in
terms of `F_ℓ = cw_{n-1+ℓ} x^{α-ℓ}`: for `c ≤ 2` with `n + 1 + α - c ≥ 0`. -/
theorem cw_left_expand (lam : X) (i : I) (α c : ℕ) (hc : 0 ≤ ip RD i lam + 1 + ((α : ℤ) - c)) :
    (pres RD k sc).lin (bubL RD k lam [up i]
        (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - c)))) ≫
        NF.dotsU (pres RD k sc) lam (up i) c =
      ∑ ℓ ∈ Finset.range (α + 1 - c), (α + 1 - c - ℓ) •
        (NF.bubRU (pres RD k sc) lam (up i) (NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + ℓ)) ≫
          NF.dotsU (pres RD k sc) lam (up i) (α - ℓ)) := by
  rw [cwL_of_nonneg RD k _ i hc, NF.lin_bubL_cwReal, dg_cw_slide_eq, Preadditive.sum_comp]
  have e : (((ip RD i lam + 1 + ((α : ℤ) - c)).toNat : ℕ) : ℤ) + -ip RD i lam = α + 1 - c := by
    rw [Int.toNat_of_nonneg hc]; ring
  rw [e, show ((α : ℤ) + 1 - c).toNat = α + 1 - c by omega]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [Linear.smul_comp, Category.assoc, NF.dotsU_add, show ((α : ℤ) + 1 - c - ℓ).toNat = α + 1 - c - ℓ by
    omega]
  congr 3
  omega

/-- **KL III Proposition 3.4, first display, `i = j`** (real bubbles): for `⟨i,λ⟩ - 1 + α ≥ 0`,
`cw_{⟨i,λ⟩-1+α} ⊗ E_i = (E_i ⊗ cw_{⟨i,λ⟩+1+(α-2)}) x² - 2 (E_i ⊗ cw_{⟨i,λ⟩+1+(α-1)}) x +
E_i ⊗ cw_{⟨i,λ⟩+1+α}` (the bubbles on the left in the region `λ + i_X`). -/
theorem prop34_cw_same (lam : X) (i : I) (α : ℕ) (hα : 0 ≤ ip RD i lam - 1 + α) :
    (pres RD k sc).lin (bubR RD k lam [up i] (cwL RD k lam i (ip RD i lam - 1 + α))) =
      (pres RD k sc).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - 2)))) ≫
          NF.dotsU (pres RD k sc) lam (up i) 2 -
        2 • ((pres RD k sc).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + ((α : ℤ) - 1)))) ≫
          NF.dotsU (pres RD k sc) lam (up i) 1) +
        (pres RD k sc).lin (bubL RD k lam [up i]
          (cwL RD k (wt RD lam [up i]) i (ip RD i lam + 1 + α))) := by
  have h₀ := cw_left_expand RD k sc lam i α 0 (by push_cast; omega)
  simp only [Nat.cast_zero, sub_zero, NF.dotsU_zero, Category.comp_id, Nat.sub_zero] at h₀
  have h₂ := cw_left_expand RD k sc lam i α 2 (by push_cast; omega)
  have h₁ := cw_left_expand RD k sc lam i α 1 (by push_cast; omega)
  simp only [Nat.cast_ofNat, Nat.cast_one] at h₂ h₁
  rw [h₂, h₁, h₀, show α + 1 - 2 = α - 1 by omega, show α + 1 - 1 = α by omega]
  have h := second_difference (fun ℓ => NF.bubRU (pres RD k sc) lam (up i) (NF.cwU (pres RD k sc) lam i (ip RD i lam - 1 + ℓ)) ≫
    NF.dotsU (pres RD k sc) lam (up i) (α - ℓ)) α
  simp only [Nat.sub_self, NF.dotsU_zero, Category.comp_id] at h
  rw [lin_bubR_eq, h.symm]

/-- A counterclockwise real bubble to the right of `E_i`, slid to the left with
`dg_ccw_slide_eq`, in terms of `F_j = ccw'_{-N-1+j} x^{α-j}` (`N = ⟨i, λ+i_X⟩`). -/
theorem ccw_right_expand (lam : X) (i : I) (α c : ℕ) (hc : 0 ≤ -ip RD i lam - 1 + ((α : ℤ) - c)) :
    (pres RD k sc).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - c)))) ≫
        NF.dotsU (pres RD k sc) lam (up i) c =
      ∑ j ∈ Finset.range (α + 1 - c), (α + 1 - c - j) •
        (NF.bubLU (pres RD k sc) lam (up i) (NF.ccwU (pres RD k sc) (wt RD lam [up i]) i
            (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫ NF.dotsU (pres RD k sc) lam (up i) (α - j)) := by
  have hN : ip RD i (wt RD lam [up i]) = 2 + ip RD i lam := by rw [ip_wt_up, A_self]
  rw [ccwL_of_nonneg RD k _ i hc, NF.lin_bubR_ccwReal, dg_ccw_slide_eq, Preadditive.sum_comp]
  have e : (((-ip RD i lam - 1 + ((α : ℤ) - c)).toNat : ℕ) : ℤ) + ip RD i (wt RD lam [up i]) =
      α + 1 - c := by
    rw [Int.toNat_of_nonneg hc, hN]; ring
  rw [e, show ((α : ℤ) + 1 - c).toNat = α + 1 - c by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.1 hj
  rw [Linear.smul_comp, Category.assoc, NF.dotsU_add, show ((α : ℤ) + 1 - c - j).toNat = α + 1 - c - j by
    omega]
  congr 3
  omega

/-- **KL III Proposition 3.4, second display, `i = j`** (real bubbles): for
`-⟨i,λ⟩ - 3 + α ≥ 0`, `E_i ⊗ ccw_{-⟨i,λ+i_X⟩-1+α} = (ccw_{-⟨i,λ⟩-1+(α-2)} ⊗ E_i) x² -
2 (ccw_{-⟨i,λ⟩-1+(α-1)} ⊗ E_i) x + ccw_{-⟨i,λ⟩-1+α} ⊗ E_i`. -/
theorem prop34_ccw_same (lam : X) (i : I) (α : ℕ) (hα : 0 ≤ -ip RD i lam - 3 + α) :
    (pres RD k sc).lin (bubL RD k lam [up i]
        (ccwL RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + α))) =
      (pres RD k sc).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - 2)))) ≫
          NF.dotsU (pres RD k sc) lam (up i) 2 -
        2 • ((pres RD k sc).lin (bubR RD k lam [up i]
          (ccwL RD k lam i (-ip RD i lam - 1 + ((α : ℤ) - 1)))) ≫ NF.dotsU (pres RD k sc) lam (up i) 1) +
        (pres RD k sc).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + α))) := by
  have h₀ := ccw_right_expand RD k sc lam i α 0 (by push_cast; omega)
  simp only [Nat.cast_zero, sub_zero, NF.dotsU_zero, Category.comp_id, Nat.sub_zero] at h₀
  have h₂ := ccw_right_expand RD k sc lam i α 2 (by push_cast; omega)
  have h₁ := ccw_right_expand RD k sc lam i α 1 (by push_cast; omega)
  simp only [Nat.cast_ofNat, Nat.cast_one] at h₂ h₁
  rw [h₂, h₁, h₀, show α + 1 - 2 = α - 1 by omega, show α + 1 - 1 = α by omega]
  have h := second_difference (fun j => NF.bubLU (pres RD k sc) lam (up i) (NF.ccwU (pres RD k sc) (wt RD lam [up i]) i
    (-ip RD i (wt RD lam [up i]) - 1 + j)) ≫ NF.dotsU (pres RD k sc) lam (up i) (α - j)) α
  simp only [Nat.sub_self, NF.dotsU_zero, Category.comp_id] at h
  rw [lin_bubL_eq, h.symm]



end Categorification.KL3.Diagram.CLQ
