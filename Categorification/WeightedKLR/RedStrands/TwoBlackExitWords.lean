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


/-- Adjacent pairs of the two-black exits admit a joint with a single black strand
between the exchanged reds. In each pair the right arm is one crossing with the
right red. The words act from the right. -/
theorem twoBlackNearbyExitWords (p : ℕ) (hp : p + 3 < m) (s : Seq ν)
    (hne : s.lbl ⟨p, by omega⟩ ≠ s.lbl ⟨p + 3, hp⟩) :
    (ψw [p + 1, p + 2, p + 1, p] * e s : A) =
      ψw [p + 2, p + 1, p + 2, p] * e s ∧
    (ψw [p, p + 1, p + 2, p] * e s : A) =
      ψw [p + 1, p, p + 1, p + 2] * e s := by
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
    simpa only [← mul_assoc] using braid_between (Q := Q) p (by omega) _ hr)
  constructor
  · simpa only [ψw_cons, ψw_nil, mul_one, mul_assoc] using left
  · simp only [ψw_cons, ψw_nil, mul_one, mul_assoc] at right ⊢
    rw [far.symm.left_comm, right]

/-- The reversed-middle exit has a comparison with each extreme exit.
Neither comparison requires distinct colours on the two black strands. -/
theorem twoBlackReversedMiddleExitWords {I₀ : Type*} [DecidableEq I₀] {red : Type*}
    [DecidableEq red] {Q₀ : I₀ ⊕ red → I₀ ⊕ red → MvPolynomial (Fin 2) k}
    {ν₀ : Multiset (I₀ ⊕ red)} (p : ℕ) (hp : p + 3 < ν₀.card) (s : Seq ν₀)
    {a b : red} {i j : I₀}
    (hb : s.lbl ⟨p, by omega⟩ = .inr b)
    (hi : s.lbl ⟨p+1, by omega⟩ = .inl i)
    (hj : s.lbl ⟨p+2, by omega⟩ = .inl j)
    (ha : s.lbl ⟨p+3, hp⟩ = .inr a) (hab : a ≠ b) :
    (ψw [p+1,p,p+2,p+1,p] * e s : KLRAlgebra k Q₀ ν₀) =
      ψw [p+2,p+1,p+2,p,p+1] * e s ∧
    (ψw [p+1,p+2,p,p+1,p+2] * e s : KLRAlgebra k Q₀ ν₀) =
      ψw [p,p+1,p+2,p,p+1] * e s := by
  let n := ν₀.card
  let left := sadj n p • (sadj n (p+1) • s)
  let right := sadj n (p+2) • (sadj n (p+1) • s)
  have hp₀ : p+1 < n := by omega
  have hp₁ : p+2 < n := by omega
  have far : Commute (ψ p : KLRAlgebra k Q₀ ν₀) (ψ (p+2)) := ψ_mul_ψ _ _ (by omega)
  have hs₀ : s.lbl ⟨p, by omega⟩ ≠ s.lbl ⟨p+2, by omega⟩ := by rw [hb,hj]; exact Sum.inr_ne_inl
  have hs₁ : s.lbl ⟨p+1, by omega⟩ ≠ s.lbl ⟨p+1+2, by omega⟩ := by
    rw [hi, ha]
    exact Sum.inl_ne_inr
  have fromB : s.lbl ⟨p, by omega⟩ ≠ s.lbl ⟨p+3, hp⟩ := by
    rw [hb, ha]
    exact fun h => hab (Sum.inr.inj h).symm
  have hl : left.lbl ⟨p+1, by omega⟩ ≠ left.lbl ⟨p+1+2, by omega⟩ := by
    dsimp only [left,n]
    rw [GradingDatum.lbl_sadj_smul, sadj_apply_right hp₀,
      GradingDatum.lbl_sadj_smul,
      sadj_apply_of_ne (k := p+1) (⟨p, by omega⟩ : Fin ν₀.card)
        (by dsimp; omega) (by dsimp; omega)]
    rw [GradingDatum.lbl_sadj_smul,
      sadj_apply_of_ne (k := p) (⟨p+3, by omega⟩ : Fin ν₀.card)
        (by dsimp; omega) (by dsimp; omega), GradingDatum.lbl_sadj_smul,
      sadj_apply_of_ne (k := p+1) (⟨p+3, by omega⟩ : Fin ν₀.card)
        (by dsimp; omega) (by dsimp; omega)]
    exact fromB
  have hr : right.lbl ⟨p, by omega⟩ ≠ right.lbl ⟨p+2, by omega⟩ := by
    dsimp only [right,n]
    rw [GradingDatum.lbl_sadj_smul,
      sadj_apply_of_ne (k := p+2) (⟨p, by omega⟩ : Fin ν₀.card)
        (by dsimp; omega) (by dsimp; omega), GradingDatum.lbl_sadj_smul,
      sadj_apply_of_ne (k := p+1) (⟨p, by omega⟩ : Fin ν₀.card)
        (by dsimp; omega) (by dsimp; omega)]
    rw [GradingDatum.lbl_sadj_smul, sadj_apply_left hp, GradingDatum.lbl_sadj_smul,
      sadj_apply_of_ne (k := p+1) (⟨p+3, by omega⟩ : Fin ν₀.card)
        (by dsimp; omega) (by dsimp; omega)]
    exact fromB
  have leftBraid := with_crossing s (p+1) _ _ (by
    simpa only [← mul_assoc] using with_crossing (sadj n (p+1) • s) p _ _ (by
      simpa only [← mul_assoc] using braid_between (Q := Q₀) (p+1) (by omega) left hl))
  have rightBraid := with_crossing s (p+1) _ _ (by
    simpa only [← mul_assoc] using with_crossing (sadj n (p+1) • s) (p+2) _ _ (by
      simpa only [← mul_assoc] using (braid_between (Q := Q₀) p (by omega) right hr).symm))
  constructor
  · simp only [ψw_cons, ψw_nil, mul_one, mul_assoc] at leftBraid ⊢
    rw [far.left_comm, braid_between p hp₁ s hs₀, leftBraid]
  · simp only [ψw_cons, ψw_nil, mul_one, mul_assoc] at rightBraid ⊢
    rw [far.symm.left_comm, ← braid_between (p+1) (by omega) s hs₁, rightBraid, far.left_comm]

private theorem offset_sadj {n p : ℕ} (hp : p + 3 < n) (r : Fin 3) (z : Fin 4) :
    sadj n (p + r.val) ⟨p + z.val, by omega⟩ =
      ⟨p + (sadj 4 r.val z).val, by omega⟩ := by
  have hn : p + r.val + 1 < n := by omega
  have h4 : r.val + 1 < 4 := by omega
  by_cases hleft : z.val = r.val
  · have he : z = ⟨r.val, Nat.lt_succ_of_lt r.isLt⟩ := Fin.ext hleft
    cases he
    simp only [Fin.val_mk, sadj_apply_left hn, sadj_apply_left h4, Nat.add_assoc]
  by_cases hright : z.val = r.val + 1
  · have he : z = ⟨r.val+1, h4⟩ := Fin.ext hright
    cases he
    simp only [Fin.val_mk, ← Nat.add_assoc, sadj_apply_right hn, sadj_apply_right h4]
  · have H₁ : p + z.val ≠ p + r.val := by omega
    have H₂ : p + z.val ≠ p + r.val + 1 := by omega
    simp only [sadj_apply_of_ne (⟨p + z.val, by omega⟩ : Fin n) H₁ H₂,
      sadj_apply_of_ne z hleft hright]

private theorem offset_wordProd {n p : ℕ} (hp : p + 3 < n)
    (w : List (Fin 3)) (z : Fin 4) :
    wordProd n (w.map fun i => p + i.val) ⟨p + z.val, by omega⟩ =
      ⟨p + (wordProd 4 (w.map Fin.val) z).val, by omega⟩ := by
  induction w with
  | nil => simp [wordProd_nil]
  | cons r w ih =>
    simp only [List.map_cons, wordProd_cons, Equiv.Perm.mul_apply, ih]
    exact offset_sadj hp r _

private theorem lbl_smul {I : Type*} {ν : Multiset I} (w : Equiv.Perm (Fin ν.card))
    (s : Seq ν) (z : Fin ν.card) : (w • s).lbl z = s.lbl (w⁻¹ z) := rfl

/-- The three right-red legs at the neighboring joints have a black immediately
before the right red at their upper cuts. The equalities identify those labels
using the original bottom loading. -/
theorem twoBlackRightPivotLabels {I : Type*} [DecidableEq I] {ν : Multiset I}
    (s : Seq ν) (p : ℕ) (hp : p+3 < ν.card) :
    let u₁ := wordProd ν.card [p+2,p+1,p+2,p] • s
    let u₂ := wordProd ν.card [p+1,p,p+1,p+2] • s
    let u₃ := wordProd ν.card [p+2,p+1,p+2,p,p+1] • s
    u₁.lbl ⟨p+2,by omega⟩ = s.lbl ⟨p+2,by omega⟩ ∧
    u₁.lbl ⟨p+3,hp⟩ = s.lbl ⟨p,by omega⟩ ∧
    u₂.lbl ⟨p+1,by omega⟩ = s.lbl ⟨p+1,by omega⟩ ∧
    u₂.lbl ⟨p+2,by omega⟩ = s.lbl ⟨p,by omega⟩ ∧
    u₃.lbl ⟨p+2,by omega⟩ = s.lbl ⟨p+1,by omega⟩ ∧
    u₃.lbl ⟨p+3,hp⟩ = s.lbl ⟨p,by omega⟩ := by
  let w₁ : List (Fin 3) := [0,2,1,2]
  let w₂ : List (Fin 3) := [2,1,0,1]
  let w₃ : List (Fin 3) := [1,0,2,1,2]
  dsimp only
  simp only [lbl_smul, ← wordProd_reverse, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append]
  exact ⟨congrArg s.lbl (offset_wordProd hp w₁ 2), congrArg s.lbl (offset_wordProd hp w₁ 3),
    congrArg s.lbl (offset_wordProd hp w₂ 1), congrArg s.lbl (offset_wordProd hp w₂ 2),
    congrArg s.lbl (offset_wordProd hp w₃ 2), congrArg s.lbl (offset_wordProd hp w₃ 3)⟩

end Categorification.KLR.KLRAlgebra
