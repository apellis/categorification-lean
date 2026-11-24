/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Filtration
import Categorification.KLR.Grading

/-!
# Affine words for exits across two black strands

A local word calculation for Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8
after (6.21). On the interval `b i j a`, the reds can meet to the left, between
the blacks, or to the right. Completing each cut to `a i j b` gives the same
affine element. Only the distinctness of the two endpoint labels enters the
braid comparisons, so the black labels may coincide.
-/

noncomputable section

namespace Categorification.KLR.KLRAlgebra

open KLR TypeA

variable {I : Type*} {k : Type*} [DecidableEq I] [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν
local notation "A" => KLRAlgebra k Q ν

private theorem braid_between (p : ℕ) (hp : p + 2 < m) (s : Seq ν)
    (hne : s.lbl ⟨p, by omega⟩ ≠ s.lbl ⟨p + 2, hp⟩) :
    (ψ p * (ψ (p + 1) * (ψ p * e s)) : A) =
      ψ (p + 1) * (ψ p * (ψ (p + 1) * e s)) := by
  have h := braid (Q := Q) p hp s
  rw [ite_eq_right (fun h => hne h.1), sub_mul, sub_eq_zero] at h
  simpa only [mul_assoc] using h

private theorem with_crossing (s : Seq ν) (r : ℕ) (x y : A)
    (h : x * e (sadj m r • s) = y * e (sadj m r • s)) :
    x * (ψ r * e s) = y * (ψ r * e s) := by
  rw [ψ_mul_e, ← mul_assoc x, ← mul_assoc y, h]

/-- On an interval `b i j a` with distinct endpoints, the two outside exits and
the middle exit agree after completion to `a i j b`. The words act from the
right. Webster v2, §6.1, proof of Lemma 6.8 after (6.21). -/
theorem twoBlackExitWords (p : ℕ) (hp : p + 3 < m) (s : Seq ν)
    (hne : s.lbl ⟨p, by omega⟩ ≠ s.lbl ⟨p + 3, hp⟩) :
    (ψw [p, p + 1, p + 2, p + 1, p] * e s : A) =
      ψw [p + 2, p, p + 1, p + 2, p] * e s ∧
    (ψw [p + 2, p + 1, p, p + 1, p + 2] * e s : A) =
      ψw [p + 2, p, p + 1, p + 2, p] * e s := by
  have hp₀ : p + 1 < m := by omega
  have far : Commute (ψ p : A) (ψ (p + 2)) := ψ_mul_ψ _ _ (by omega)
  have hl : (sadj m p • s).lbl ⟨p + 1, by omega⟩ ≠
      (sadj m p • s).lbl ⟨p + 1 + 2, by omega⟩ := by
    simpa only [GradingDatum.lbl_sadj_smul, sadj_apply_right hp₀,
      sadj_apply_of_ne (k := p) (⟨p + 3, hp⟩ : Fin m) (by simp) (by simp),
      show p + 1 + 2 = p + 3 by omega] using hne
  have hr : (sadj m (p + 2) • s).lbl ⟨p, by omega⟩ ≠
      (sadj m (p + 2) • s).lbl ⟨p + 2, by omega⟩ := by
    simpa only [GradingDatum.lbl_sadj_smul, sadj_apply_left hp,
      sadj_apply_of_ne (k := p + 2) (⟨p, by omega⟩ : Fin m) (by simp) (by simp; omega),
      show p + 2 + 1 = p + 3 by omega] using hne
  have left := with_crossing s p _ _ (by
    simpa only [← mul_assoc] using braid_between (Q := Q) (p + 1) (by omega) _ hl)
  have right := with_crossing s (p + 2) _ _ (by
    simpa only [← mul_assoc] using (braid_between (Q := Q) p (by omega) _ hr).symm)
  constructor
  · simp only [ψw_cons, ψw_nil, mul_one, mul_assoc] at left ⊢
    rw [left, far.left_comm]
  · simp only [ψw_cons, ψw_nil, mul_one, mul_assoc] at right ⊢
    rw [right, far.left_comm]

end Categorification.KLR.KLRAlgebra
