/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicAction.VacuumTrace
import Categorification.Diagrams.KL3.GammaFlagBubble

/-!
# The Grassmannian inverse of the vacuum traces

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, proof of
Proposition 3.25. At the vacuum the counterclockwise bubbles act by the traces `vacTrace`, and
the fake clockwise bubbles are their Grassmannian inverses. These inverses are, up to sign, the
coefficients of the universal cyclotomic polynomial: `(-1)^n e_n(p_j)` in degree `n ≤ λ^j`, and
`0` above.

* `vacFakeVal j n`: `1` for `n = 0`, `(-1)^n e_n(p_j)` for `1 ≤ n ≤ λ^j`, `0` for `n > λ^j`;
* `grassInv_vacTrace`: the Grassmannian inverse of `a ↦ vacTrace j (λ^j - 1 + a)` is
  `vacFakeVal j`.
-/

namespace Categorification.KLR.CyclotomicAction

universe u v

noncomputable section

variable {I : Type u} (k : Type v) [CommRing k] [Nontrivial k] (lam : I → ℕ)

/-- The coefficients of the universal cyclotomic polynomial, signed: `1` in degree `0`,
`(-1)^n e_n(p_j)` in degree `1 ≤ n ≤ λ^j`, `0` above. -/
def vacFakeVal (j : I) (n : ℕ) : UnivCycRing k lam :=
  if h0 : n = 0 then 1
  else if h : n ≤ lam j then (-1) ^ n * elemSym k lam j ⟨n - 1, by omega⟩ else 0

omit [Nontrivial k] in
theorem vacTrace_eq_zero_of_lam_eq_zero (j : I) (h : lam j = 0) (m : ℕ) :
    vacTrace k lam j m = 0 := by
  have := vacTrace_recurrence k lam j m
  have hE : IsEmpty (Fin (lam j)) := by rw [h]; infer_instance
  rw [Finset.univ_eq_empty, Finset.sum_empty, h, add_zero] at this
  exact this

/-- The convolution of the vacuum traces with `vacFakeVal` in positive degree. -/
private theorem vacConv_pos (j : I) (N : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Finset.range (N + 1),
      (if N - q = 0 then 1 else vacTrace k lam j (lam j - 1 + (N - q))) * vacFakeVal k lam j q =
      0 := by
  rcases Nat.eq_zero_or_pos (lam j) with h0 | hl
  · refine Finset.sum_eq_zero fun q hq => ?_
    have hq' := Finset.mem_range.1 hq
    by_cases hqN : N - q = 0
    · have : q ≠ 0 := by omega
      simp [vacFakeVal, this, h0, show ¬ q ≤ 0 by omega]
    · simp only [hqN, ↓reduceIte, vacTrace_eq_zero_of_lam_eq_zero k lam j h0, zero_mul]
  have hterm : ∀ q ∈ Finset.range (N + 1),
      (if N - q = 0 then 1 else vacTrace k lam j (lam j - 1 + (N - q))) * vacFakeVal k lam j q =
        vacTrace k lam j (lam j - 1 + N - q) * vacFakeVal k lam j q := by
    intro q hq
    have hq' := Finset.mem_range.1 hq
    by_cases hqN : N - q = 0
    · simp only [hqN, ↓reduceIte]
      have hqe : q = N := by omega
      subst hqe
      by_cases hle : q ≤ lam j
      · rw [show lam j - 1 + q - q = lam j - 1 by omega, vacTrace_of_lt k lam j (by omega)]
        simp
      · simp [vacFakeVal, show q ≠ 0 by omega, hle]
    · simp only [hqN, ↓reduceIte]
      rw [show lam j - 1 + (N - q) = lam j - 1 + N - q by omega]
  rw [Finset.sum_congr rfl hterm]
  -- extend or restrict the range to `λ + 1`
  have hext : ∀ M, N + 1 ≤ M →
      ∑ q ∈ Finset.range M, vacTrace k lam j (lam j - 1 + N - q) * vacFakeVal k lam j q =
        ∑ q ∈ Finset.range (N + 1),
          vacTrace k lam j (lam j - 1 + N - q) * vacFakeVal k lam j q := by
    intro M hM
    refine (Finset.sum_subset (Finset.range_mono hM) fun q hq hq' => ?_).symm
    have h1 := Finset.mem_range.1 hq
    have h2 : N + 1 ≤ q := by simpa using hq'
    by_cases hle : q ≤ lam j
    · rw [vacTrace_of_lt k lam j (by omega)]
      simp [show lam j - 1 + N - q ≠ lam j - 1 by omega]
    · simp [vacFakeVal, show q ≠ 0 by omega, hle]
  have htrunc : ∀ M, lam j + 1 ≤ M →
      ∑ q ∈ Finset.range M, vacTrace k lam j (lam j - 1 + N - q) * vacFakeVal k lam j q =
        ∑ q ∈ Finset.range (lam j + 1),
          vacTrace k lam j (lam j - 1 + N - q) * vacFakeVal k lam j q := by
    intro M hM
    refine (Finset.sum_subset (Finset.range_mono hM) fun q hq hq' => ?_).symm
    have h2 : lam j + 1 ≤ q := by simpa using hq'
    simp [vacFakeVal, show q ≠ 0 by omega, show ¬ q ≤ lam j by omega]
  rw [← hext (N + lam j + 1) (by omega), htrunc _ (by omega), Finset.sum_range_succ']
  have hrec := vacTrace_recurrence k lam j (N - 1)
  rw [show N - 1 + lam j = lam j - 1 + N - 0 by omega] at hrec
  rw [Finset.sum_range (fun q =>
      vacTrace k lam j (lam j - 1 + N - (q + 1)) * vacFakeVal k lam j (q + 1)),
    show vacFakeVal k lam j 0 = 1 by simp [vacFakeVal], mul_one, hrec, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun n _ => ?_
  have hn := n.2
  rw [vacFakeVal]
  simp only [show n.val + 1 ≠ 0 by omega, show n.val + 1 ≤ lam j by omega, ↓reduceDIte]
  rw [show lam j - 1 + N - (n.val + 1) = N - 1 + (lam j - (n.val + 1)) by omega]
  simp only [Nat.add_sub_cancel, Fin.eta, pow_succ]
  ring

/-- **The Grassmannian inverse of the vacuum traces**: the inverse of the series with
coefficients `vacTrace j (λ^j - 1 + a)` (`a ≥ 1`) is the signed universal cyclotomic polynomial
`vacFakeVal j`. The zeroth coefficient of the series plays no role in `grassInv`. -/
theorem grassInv_vacTrace (j : I) (n : ℕ) :
    KL3.Diagram.grassInv (fun a => vacTrace k lam j (lam j - 1 + a)) n = vacFakeVal k lam j n := by
  rw [KL3.Diagram.Signed.grassInv_congr _
    (fun a => if a = 0 then 1 else vacTrace k lam j (lam j - 1 + a)) (fun a => by simp)]
  refine KL3.Diagram.Signed.grassInv_eq _ _ (by simp) (fun N => ?_) n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [vacFakeVal]
  simp only [hN.ne', ↓reduceIte]
  rw [← vacConv_pos k lam j N hN, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun q hq => ?_
  have := Finset.mem_range.1 hq
  simp only [show N + 1 - 1 - q = N - q by omega, show N - (N - q) = q by omega]

end

end Categorification.KLR.CyclotomicAction
