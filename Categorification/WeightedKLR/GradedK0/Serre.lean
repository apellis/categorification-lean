/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.GradedK0.SpacedZigzag
import Categorification.WeightedKLR.GradedK0.DividedPowers
import Categorification.WeightedKLR.RouquierQ
import Categorification.KLR.Rouquier.K0Relations

/-!
# Serre relations among weighted loading projectives

The graded projective relation needed for the natural map in Webster,
*Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, §2.4,
Theorem 2.19, roadmap C. Rouquier's homogeneous contracting zigzag
(arXiv:0812.5023v1, §4.1.1, Proposition 4.2) transports along the evenly spaced
loading comparison of Webster Proposition 2.14. Its alternating relation is
the graded projective calculation of KL II, arXiv:0804.2080v1, §3, Proposition 6
and Corollary 7. The coefficient ring is any commutative ring, and different
sequence words may have the same weighted loading chamber.
-/

noncomputable section

namespace Categorification.WeightedKLR.GradingDatum

open Categorification.Graded Categorification.KLR Categorification.KLR.KL2
  Categorification.KLR.Rouquier LaurentPolynomial _root_.Finset

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}
  {ν : Multiset I} {t : Seq ν} {p N : ℕ} {i j : I}

/-- The divided-power Serre window for the weighted evenly spaced loadings, over any
commutative coefficient ring and with Webster's standing crossing polynomials. -/
theorem K0_serre_window (hS : Γ.Standing) (hD : Γ.Dagger)
    (hne : ∀ e, Γ.head e ≠ Γ.tail e) (hl : ∀ i, Γ.loop i = none)
    (hpN : p + N < ν.card)
    (ht₀ : ∀ r : Fin ν.card, (r : ℕ) = p → t.lbl r = j)
    (ht : ∀ r : Fin ν.card, p < r → (r : ℕ) ≤ p + N → t.lbl r = i)
    (hij : i ≠ j) (hN : N = hS.cartanDatum.dij i j + 1)
    (sh : ℕ → ℤ)
    (hsh : ∀ a, a < N → sh (a + 1) = sh a +
      (-((N - a - 1 : ℕ) : ℤ) * hS.cartanDatum.dot i i - hS.cartanDatum.dot i j))
    (P : ℕ → K0 (hS.gradingDatum.klrGrade ν.toFinsupp))
    (hP : ∀ a (ha : a ≤ N), P a = K0.of
      (hS.gradingDatum.spacedProjFlip hS hD hne hl (serreSeq t p a)
        [(p, a), (p + a + 1, N - a)] (isBlocks_etop hpN ht₀ ht ha))) :
    ∑ a ∈ range (N + 1), ((-1 : LaurentPolynomial ℤ) ^ a * T (-sh a)) • P a = 0 := by
  let G := hS.gradingDatum
  let H := G.toKLRGrading hne hl
  have hX (c : I) : H.degX c = hS.cartanDatum.dot c c := by
    rw [hS.cartanDatum_dot_self]
    rfl
  have hΨ (c d : I) : H.degΨ c d = -hS.cartanDatum.dot c d :=
    hS.pairDeg_eq_neg_cartanDatum_dot hne hl c d
  let data := serre_zigzag_data hpN ht₀ ht H hX hΨ hS.isRouquierQ hij hN
  apply G.sum_neg_one_pow_smul_of_spaced_zigzag hS hD hne hl (serreSeq t p)
    data.hE data.hE0 data.hER data.hpR data.hmR data.hsum data.hpm data.hmp
    data.hpE data.hmE data.hxy data.hGm data.hGp hsh P
  intro a ha
  rw [hP a ha]
  apply K0.of_ofIdempotent_congr
  exact congrArg (spacedEntryMap hS hD hne hl (serreSeq t p a) (serreSeq t p a) ∘ KLRAlgebra.hflip)
    (etop_eq_divIdem (k := k) (Q := Γ.klrQ) (t := t) (p := p) (N := N) a).symm

end Categorification.WeightedKLR.GradingDatum
