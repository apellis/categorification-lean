/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.BubbleSlidesEq

/-!
# KL III Proposition 3.3 (bubble slides), printed form

M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.1.2,
Proposition 3.3 (TeX label `prop_bubble_slide1`).

The statements of Proposition 3.3 are stated here with the printed labels `α`, in the range in
which the bubble on the left-hand side is a real (dotted) bubble; the bubbles on the right-hand
side may be fake bubbles (`ccwL`, `cwL`). Throughout, `n = ⟨i, λ⟩` and `λ` is the region on the
right of the upward `j`-strand.

* `prop33_ccw_same`, `prop33_cw_same`: the case `i = j` (first and second display);
* `prop33_ccw_adj`, `prop33_cw_adj`: the case `i · j = -1`;
* `prop33_ccw_orth`, `prop33_cw_orth`: the case `i · j = 0`.

For an arbitrary Cartan datum and `i ≠ j` see `bubble_slide_ccw_ne` and `bubble_slide_cw_ne`
(with the KL II polynomial `Q_ij = u^{d_ij} + v^{d_ji}`).

## Interpretation of the printed statement

* The printed first display for `i = j` has, on the right-hand side, the region label `λ + j_X`
  and the bubble label `-⟨i, λ + i_X⟩ - 1 + f` (in the TeX source); the summation index `f`
  runs from `0` to `α` with coefficient `α + 1 - f` and `α - f` dots on the strand.
* KL III do not say for which `α` the identities are claimed. Here they are proved when the
  bubble on the left-hand side is real (label `≥ 0`); the extension to all `α ≥ 0` (fake bubble
  on the left-hand side) uses the infinite Grassmannian relation in all degrees and is in
  `Categorification.Diagrams.KL3.BubbleSlidesAll` (`prop33_ccw_same_all`, …).
-/

noncomputable section

namespace Categorification.KL3.Diagram

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : RootDatum C X Y) (k : Type w) [CommRing k]

/-- `⟨i, λ + j_X⟩ = ⟨i, λ⟩ + ⟨i, j_X⟩`. -/
theorem ip_wt_up (i j : I) (lam : X) : ip RD i (wt RD lam [up j]) = A C i j + ip RD i lam := by
  simp [ip, wt, sh, RD.pair_iY_iX_eq_A]

theorem A_eq_neg_dij {i j : I} (h : i ≠ j) : A C i j = -(C.dij i j : ℤ) := by
  have h₁ := C.dij_mul h
  have hpos := C.dot_self_pos i
  rw [A, show 2 * C.dot i j = -(C.dij i j : ℤ) * C.dot i i by linarith,
    Int.mul_ediv_cancel _ hpos.ne']

theorem lin_bubL_eq (lam : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD lam [l]) [])) :
    (pres RD k).lin (bubL RD k lam [l] b) = bubLU RD k lam l ((pres RD k).lin b) :=
  lin_bubL RD k lam l b

theorem lin_bubR_eq (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    (pres RD k).lin (bubR RD k lam [l] b) = bubRU RD k lam l ((pres RD k).lin b) :=
  lin_bubR RD k lam l b

theorem ccwL_of_nonneg (ν : X) (i : I) {m : ℤ} (hm : 0 ≤ m) :
    ccwL RD k ν i m = LinDiagram.of (ccwReal RD ν i m.toNat) := by
  rw [ccwL, if_pos hm]

theorem cwL_of_nonneg (ν : X) (i : I) {m : ℤ} (hm : 0 ≤ m) :
    cwL RD k ν i m = LinDiagram.of (cwReal RD ν i m.toNat) := by
  rw [cwL, if_pos hm]

/-- **KL III Proposition 3.3, first display, `i = j`** (real bubble on the left-hand side): for
`α` with `-⟨i,λ⟩ - 1 + α ≥ 0`,
`ccw_{-⟨i,λ⟩-1+α} ⊗ E_i = ∑_{ℓ=0}^{α} (α + 1 - ℓ) (E_i ⊗ ccw_{-⟨i,λ+i_X⟩-1+ℓ}) x^{α-ℓ}`. -/
theorem prop33_ccw_same (lam : X) (i : I) (α : ℕ) (hα : 0 ≤ -ip RD i lam - 1 + α) :
    (pres RD k).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + α))) =
      ∑ ℓ ∈ Finset.range (α + 1), (α + 1 - ℓ) •
        ((pres RD k).lin (bubL RD k lam [up i]
            (ccwL RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + ℓ))) ≫
          dotsU RD k lam (up i) (α - ℓ)) := by
  rw [ccwL_of_nonneg RD k lam i hα, lin_bubR_ccwReal, dg_ccw_slide_eq]
  have hN : ip RD i (wt RD lam [up i]) = 2 + ip RD i lam := by
    rw [ip_wt_up, A_self]
  have e : (((-ip RD i lam - 1 + α).toNat : ℕ) : ℤ) + ip RD i (wt RD lam [up i]) = α + 1 := by
    rw [Int.toNat_of_nonneg hα, hN]; ring
  rw [e, show ((α : ℤ) + 1).toNat = α + 1 by omega]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubL_eq, show ((α : ℤ) + 1 - ℓ).toNat = α + 1 - ℓ by omega]
  congr 2
  show dotsU RD k lam (up i) _ = dotsU RD k lam (up i) _
  congr 1; omega

/-- **KL III Proposition 3.3, second display, `i = j`** (real bubble on the left-hand side): for
`α` with `⟨i,λ+i_X⟩ - 1 + α ≥ 0`,
`E_i ⊗ cw_{⟨i,λ+i_X⟩-1+α} = ∑_{ℓ=0}^{α} (α + 1 - ℓ) (cw_{⟨i,λ⟩-1+ℓ} ⊗ E_i) x^{α-ℓ}`. -/
theorem prop33_cw_same (lam : X) (i : I) (α : ℕ)
    (hα : 0 ≤ ip RD i (wt RD lam [up i]) - 1 + α) :
    (pres RD k).lin (bubL RD k lam [up i]
        (cwL RD k (wt RD lam [up i]) i (ip RD i (wt RD lam [up i]) - 1 + α))) =
      ∑ ℓ ∈ Finset.range (α + 1), (α + 1 - ℓ) •
        ((pres RD k).lin (bubR RD k lam [up i] (cwL RD k lam i (ip RD i lam - 1 + ℓ))) ≫
          dotsU RD k lam (up i) (α - ℓ)) := by
  rw [cwL_of_nonneg RD k _ i hα, lin_bubL_cwReal, dg_cw_slide_eq]
  have hN : ip RD i (wt RD lam [up i]) = 2 + ip RD i lam := by
    rw [ip_wt_up, A_self]
  have e : (((ip RD i (wt RD lam [up i]) - 1 + α).toNat : ℕ) : ℤ) + -ip RD i lam = α + 1 := by
    rw [Int.toNat_of_nonneg hα, hN]; ring
  rw [e, show ((α : ℤ) + 1).toNat = α + 1 by omega]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have := Finset.mem_range.1 hℓ
  rw [lin_bubR_eq, show ((α : ℤ) + 1 - ℓ).toNat = α + 1 - ℓ by omega]
  congr 2
  show dotsU RD k lam (up i) _ = dotsU RD k lam (up i) _
  congr 1; omega

section Adjacent

variable {RD}

theorem ne_of_dot_neg_one {i j : I} (h : C.dot i j = -1) : i ≠ j := by
  rintro rfl; have := C.dot_self_pos i; omega

theorem ne_of_dot_zero {i j : I} (h : C.dot i j = 0) : i ≠ j := by
  rintro rfl; have := C.dot_self_pos i; omega

theorem dot_self_eq_two_of_dot_neg_one {i j : I} (h : C.dot i j = -1) : C.dot i i = 2 := by
  have hd := C.dvd_two_mul i j
  rw [h] at hd
  have hpos := C.dot_self_pos i
  obtain ⟨e, he⟩ := C.dot_self_even i
  have hle : C.dot i i ≤ 2 := Int.le_of_dvd (by norm_num) (by simpa using hd)
  omega

theorem dij_of_dot_neg_one {i j : I} (h : C.dot i j = -1) : C.dij i j = 1 := by
  rw [CartanDatum.dij, h, dot_self_eq_two_of_dot_neg_one h]; rfl

theorem A_of_dot_neg_one {i j : I} (h : C.dot i j = -1) : A C i j = -1 := by
  rw [A, h, dot_self_eq_two_of_dot_neg_one h]; rfl

theorem A_of_dot_zero {i j : I} (h : C.dot i j = 0) : A C i j = 0 := by
  rw [A, h]; simp

end Adjacent

/-- **KL III Proposition 3.3, first display, `i · j = -1`** (real bubble on the left-hand side):
for `α` with `-⟨i,λ⟩ - 1 + α ≥ 0`,
`ccw_{-⟨i,λ⟩-1+α} ⊗ E_j = E_j ⊗ ccw_{-⟨i,λ+j_X⟩-1+α} + (E_j ⊗ ccw_{-⟨i,λ+j_X⟩-2+α}) x_j`. -/
theorem prop33_ccw_adj (lam : X) (i j : I) (hij : C.dot i j = -1) (α : ℕ)
    (hα : 0 ≤ -ip RD i lam - 1 + α) :
    (pres RD k).lin (bubR RD k lam [up j] (ccwL RD k lam i (-ip RD i lam - 1 + α))) =
      (pres RD k).lin (bubL RD k lam [up j]
          (ccwL RD k (wt RD lam [up j]) i (-ip RD i (wt RD lam [up j]) - 1 + α))) +
        (pres RD k).lin (bubL RD k lam [up j]
            (ccwL RD k (wt RD lam [up j]) i (-ip RD i (wt RD lam [up j]) - 2 + α))) ≫
          dotsU RD k lam (up j) 1 := by
  have hn : ip RD i (wt RD lam [up j]) = -1 + ip RD i lam := by
    rw [ip_wt_up, A_of_dot_neg_one hij]
  have hji : C.dot j i = -1 := by rw [C.symm]; exact hij
  rw [ccwL_of_nonneg RD k lam i hα, bubble_slide_ccw_ne RD k lam i j (ne_of_dot_neg_one hij),
    if_neg (by omega), dij_of_dot_neg_one hij, dij_of_dot_neg_one hji,
    ccwL_of_nonneg RD k _ i (by omega), ccwL_of_nonneg RD k _ i (by omega)]
  congr 5
  · omega
  · congr 1; omega

/-- **KL III Proposition 3.3, second display, `i · j = -1`** (real bubble on the left-hand side):
for `α` with `⟨i,λ+j_X⟩ - 1 + α ≥ 0`,
`E_j ⊗ cw_{⟨i,λ+j_X⟩-1+α} = (cw_{⟨i,λ⟩-1+α-1} ⊗ E_j) x_j + cw_{⟨i,λ⟩-1+α} ⊗ E_j`. -/
theorem prop33_cw_adj (lam : X) (i j : I) (hij : C.dot i j = -1) (α : ℕ)
    (hα : 0 ≤ ip RD i (wt RD lam [up j]) - 1 + α) :
    (pres RD k).lin (bubL RD k lam [up j]
        (cwL RD k (wt RD lam [up j]) i (ip RD i (wt RD lam [up j]) - 1 + α))) =
      (pres RD k).lin (bubR RD k lam [up j] (cwL RD k lam i (ip RD i lam - 1 + α - 1))) ≫
          dotsU RD k lam (up j) 1 +
        (pres RD k).lin (bubR RD k lam [up j] (cwL RD k lam i (ip RD i lam - 1 + α))) := by
  have hn : ip RD i (wt RD lam [up j]) = -1 + ip RD i lam := by
    rw [ip_wt_up, A_of_dot_neg_one hij]
  have hji : C.dot j i = -1 := by rw [C.symm]; exact hij
  rw [cwL_of_nonneg RD k _ i hα, bubble_slide_cw_ne RD k lam i j (ne_of_dot_neg_one hij),
    if_neg (by omega), dij_of_dot_neg_one hij, dij_of_dot_neg_one hji,
    cwL_of_nonneg RD k _ i (by omega), cwL_of_nonneg RD k _ i (by omega), add_comm]
  congr 5
  all_goals first | omega | (congr 1; omega)

/-- **KL III Proposition 3.3, first display, `i · j = 0`** (real bubble): for
`-⟨i,λ⟩ - 1 + α ≥ 0`, `ccw_{-⟨i,λ⟩-1+α} ⊗ E_j = E_j ⊗ ccw_{-⟨i,λ⟩-1+α}`. -/
theorem prop33_ccw_orth (lam : X) (i j : I) (hij : C.dot i j = 0) (α : ℕ)
    (hα : 0 ≤ -ip RD i lam - 1 + α) :
    (pres RD k).lin (bubR RD k lam [up j] (ccwL RD k lam i (-ip RD i lam - 1 + α))) =
      (pres RD k).lin (bubL RD k lam [up j] (ccwL RD k (wt RD lam [up j]) i (-ip RD i lam - 1 + α))) := by
  rw [ccwL_of_nonneg RD k lam i hα, bubble_slide_ccw_ne RD k lam i j (ne_of_dot_zero hij),
    if_pos hij, ccwL_of_nonneg RD k _ i hα]

/-- **KL III Proposition 3.3, second display, `i · j = 0`** (real bubble): for
`⟨i,λ⟩ - 1 + α ≥ 0`, `E_j ⊗ cw_{⟨i,λ⟩-1+α} = cw_{⟨i,λ⟩-1+α} ⊗ E_j`. -/
theorem prop33_cw_orth (lam : X) (i j : I) (hij : C.dot i j = 0) (α : ℕ)
    (hα : 0 ≤ ip RD i lam - 1 + α) :
    (pres RD k).lin (bubL RD k lam [up j] (cwL RD k (wt RD lam [up j]) i (ip RD i lam - 1 + α))) =
      (pres RD k).lin (bubR RD k lam [up j] (cwL RD k lam i (ip RD i lam - 1 + α))) := by
  rw [cwL_of_nonneg RD k _ i hα, bubble_slide_cw_ne RD k lam i j (ne_of_dot_zero hij),
    if_pos hij, cwL_of_nonneg RD k _ i hα]

end Categorification.KL3.Diagram
