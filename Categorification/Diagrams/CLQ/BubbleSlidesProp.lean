/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.CLQ.BubbleSlidesEq
import Categorification.Diagrams.KL3.BubbleSlidesProp

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

namespace Categorification.KL3.Diagram.CLQ

open CategoryTheory StringDiagrams QuantumGroup UDot Presentation

universe w u v

variable {I : Type u} {C : CartanDatum I} {X Y : Type v} [AddCommGroup X] [AddCommGroup Y]
  (RD : WeightDatum C X Y) (k : Type w) [CommRing k] (sc : CL.CLScalars C k)



theorem lin_bubL_eq (lam : X) (l : Letter I) (b : LEnd RD k (ob RD (wt RD lam [l]) [])) :
    (pres RD k sc).lin (bubL RD k lam [l] b) = bubLU RD k sc lam l ((pres RD k sc).lin b) :=
  lin_bubL RD k sc lam l b

theorem lin_bubR_eq (lam : X) (l : Letter I) (b : LEnd RD k (ob RD lam [])) :
    (pres RD k sc).lin (bubR RD k lam [l] b) = bubRU RD k sc lam l ((pres RD k sc).lin b) :=
  lin_bubR RD k sc lam l b



/-- **KL III Proposition 3.3, first display, `i = j`** (real bubble on the left-hand side): for
`α` with `-⟨i,λ⟩ - 1 + α ≥ 0`,
`ccw_{-⟨i,λ⟩-1+α} ⊗ E_i = ∑_{ℓ=0}^{α} (α + 1 - ℓ) (E_i ⊗ ccw_{-⟨i,λ+i_X⟩-1+ℓ}) x^{α-ℓ}`. -/
theorem prop33_ccw_same (lam : X) (i : I) (α : ℕ) (hα : 0 ≤ -ip RD i lam - 1 + α) :
    (pres RD k sc).lin (bubR RD k lam [up i] (ccwL RD k lam i (-ip RD i lam - 1 + α))) =
      ∑ ℓ ∈ Finset.range (α + 1), (α + 1 - ℓ) •
        ((pres RD k sc).lin (bubL RD k lam [up i]
            (ccwL RD k (wt RD lam [up i]) i (-ip RD i (wt RD lam [up i]) - 1 + ℓ))) ≫
          dotsU RD k sc lam (up i) (α - ℓ)) := by
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
  show dotsU RD k sc lam (up i) _ = dotsU RD k sc lam (up i) _
  congr 1; omega

/-- **KL III Proposition 3.3, second display, `i = j`** (real bubble on the left-hand side): for
`α` with `⟨i,λ+i_X⟩ - 1 + α ≥ 0`,
`E_i ⊗ cw_{⟨i,λ+i_X⟩-1+α} = ∑_{ℓ=0}^{α} (α + 1 - ℓ) (cw_{⟨i,λ⟩-1+ℓ} ⊗ E_i) x^{α-ℓ}`. -/
theorem prop33_cw_same (lam : X) (i : I) (α : ℕ)
    (hα : 0 ≤ ip RD i (wt RD lam [up i]) - 1 + α) :
    (pres RD k sc).lin (bubL RD k lam [up i]
        (cwL RD k (wt RD lam [up i]) i (ip RD i (wt RD lam [up i]) - 1 + α))) =
      ∑ ℓ ∈ Finset.range (α + 1), (α + 1 - ℓ) •
        ((pres RD k sc).lin (bubR RD k lam [up i] (cwL RD k lam i (ip RD i lam - 1 + ℓ))) ≫
          dotsU RD k sc lam (up i) (α - ℓ)) := by
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
  show dotsU RD k sc lam (up i) _ = dotsU RD k sc lam (up i) _
  congr 1; omega

section Adjacent

variable {RD}







end Adjacent





end Categorification.KL3.Diagram.CLQ
