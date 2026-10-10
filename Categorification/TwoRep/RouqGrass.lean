/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqDual

/-!
# The infinite Grassmannian relation from Rouquier's data

J. Brundan, *On the definition of Kac–Moody 2-category*, arXiv:1501.00350v1, §3, Theorem 3.2: for
Rouquier's data at one weight `h` (`RouqLoc`), with the dotted bubbles of all integer degrees
defined by (3.8), (3.9) (`RouqLoc.ccw`, `RouqLoc.cw`), for every `t > 0`

`∑_{r + s = t - 2} (counter-clockwise bubble with r dots) (clockwise bubble with s dots) = 0`.

No grading and no condition on `End(1_λ)` is used. The sum is finite: only the terms with
`min h 0 - 1 ≤ r ≤ t - 1 + max h 0` can be nonzero, and we state the relation for every window
`r ∈ [lo, lo + K)` containing this range (`RouqLoc.infGrass`).

The proof for `h ≥ 0` is Brundan's: substituting (3.9), the sum becomes the bubble
`η' ∘ x^{t-1} ∘ σ ∘ σ' ∘ (cap with h dots)` rewritten with (3.5), (1.17) and the iterated dot
slide (2.3) (`powComp_sig`, `key_nonneg`), which vanishes by (3.6) if `h > 0` and by (1.18), (3.5)
if `h = 0`. The case `h ≤ 0` follows by applying the case `-h ≥ 0` to the dual data in the bidual
(`RouqLoc.dual`, Brundan's appeal to Theorem 2.3 and (3.10)).

## Main statements

* `RouqLoc.powComp_sig`: `x^m` on the bottom of `σ` (Brundan (2.3) iterated);
* `RouqLoc.key_nonneg`: Brundan's computation for `h ≥ 0`;
* `RouqLoc.infGrass`: **Brundan, Theorem 3.2**.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory Opposite

universe w v u

/-- A sum over a window of integers whose terms vanish outside a subwindow is the sum over the
subwindow. -/
theorem sum_range_window {M : Type*} [AddCommMonoid M] (f : ℤ → M) {lo lo' : ℤ} {K K' : ℕ}
    (hf : ∀ a, (a < lo' ∨ lo' + K' ≤ a) → f a = 0) (hlo : lo ≤ lo') (hK : lo' + K' ≤ lo + K) :
    ∑ i ∈ Finset.range K, f (lo + i) = ∑ i ∈ Finset.range K', f (lo' + i) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, lo' = lo + d := ⟨(lo' - lo).toNat, by omega⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ, K = d + K' + e := ⟨K - d - K', by omega⟩
  subst he
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range d, f (lo + i) = 0 :=
    Finset.sum_eq_zero fun i hi => hf _ (Or.inl (by simp at hi; omega))
  have h2 : ∑ i ∈ Finset.range e, f (lo + ↑(d + K' + i)) = 0 :=
    Finset.sum_eq_zero fun i _ => hf _ (Or.inr (by push_cast; omega))
  rw [h1, zero_add, h2, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  push_cast
  omega

namespace RouqLoc

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

open AdditiveWhiskering

theorem whiskerLeft_powComp_capD (m n : ℕ) :
    R₁ ◁ powComp x₁ m ≫ L.capD n = L.capD (m + n) := by
  rw [capD, capD, ← Category.assoc, ← Bicategory.whiskerLeft_comp, powComp_comp_powComp]

theorem cupD_powComp_whiskerRight (m n : ℕ) :
    L.cupD m ≫ powComp x₂ n ▷ R₂ = L.cupD (m + n) := by
  rw [cupD, cupD, Category.assoc, ← Bicategory.comp_whiskerRight, powComp_comp_powComp]

/-- Brundan (2.3) iterated: `x^m` on the upward strand at the bottom of `σ` equals `x^m` at the top
minus `∑_{j < m}` (cap with `j` dots)(cup with `m - 1 - j` dots). -/
theorem powComp_sig (m : ℕ) :
    R₁ ◁ powComp x₁ m ≫ L.sig =
      L.sig ≫ powComp x₂ m ▷ R₂ - ∑ j ∈ Finset.range m, L.capD j ≫ L.cupD (m - 1 - j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : R₁ ◁ x₁ ≫ L.sig = L.sig ≫ x₂ ▷ R₂ - L.capD 0 ≫ L.cupD 0 := by
      rw [← L.sig_dot_sub]
      simp [capD, cupD]
    rw [powComp_succ, Bicategory.whiskerLeft_comp, Category.assoc, h1, Preadditive.comp_sub,
      ← Category.assoc, ih, Preadditive.sub_comp, Category.assoc, ← Bicategory.comp_whiskerRight,
      ← powComp_succ, Finset.sum_range_succ, Preadditive.sum_comp, ← Category.assoc,
      whiskerLeft_powComp_capD, add_zero, Nat.add_sub_cancel]
    have h2 : ∀ j ∈ Finset.range m, (L.capD j ≫ L.cupD (m - 1 - j)) ≫ x₂ ▷ R₂ =
        L.capD j ≫ L.cupD (m + 1 - 1 - j) := by
      intro j hj
      have hj' : j < m := Finset.mem_range.mp hj
      rw [Category.assoc, ← powComp_one x₂, cupD_powComp_whiskerRight]
      congr 2
      omega
    rw [Finset.sum_congr rfl h2, Nat.sub_self, Nat.add_sub_cancel]
    abel

/-- **Brundan's computation in the proof of Theorem 3.2** (`h ≥ 0`): with `P j` the
counter-clockwise bubble with `j ≥ 0` dots, `Q j` the clockwise one and `N = h`,
`∑_{j < m} P j Q (m-1-j) - η' σ x^m ε' = ∑_{n < N} P (m+n) (η'_n ∘ cap_N) - P (m+N)`. -/
theorem key_nonneg (hh : 0 ≤ h) (m : ℕ) :
    ∑ j ∈ Finset.range m, (L.cupL ≫ L.capD j) ≫ (L.cupD (m - 1 - j) ≫ L.capL) -
        L.cupL ≫ L.sig ≫ powComp x₂ m ▷ R₂ ≫ L.capL =
      ∑ n ∈ Finset.range h.toNat, (L.cupL ≫ L.capD (m + n)) ≫ (L.cupN n ≫ L.capD h.toNat) -
        L.cupL ≫ L.capD (m + h.toNat) := by
  have hc : ∀ (n : ℕ) {Z : b ⟶ b} (g : 𝟙 b ⟶ Z),
      R₁ ◁ powComp x₁ m ≫ L.capD n ≫ g = L.capD (m + n) ≫ g := by
    intro n Z g
    rw [← Category.assoc, whiskerLeft_powComp_capD]
  have A : L.cupL ≫ R₁ ◁ powComp x₁ m ≫ L.sig ≫ L.capL =
      L.cupL ≫ L.sig ≫ powComp x₂ m ▷ R₂ ≫ L.capL -
        ∑ j ∈ Finset.range m, (L.cupL ≫ L.capD j) ≫ (L.cupD (m - 1 - j) ≫ L.capL) := by
    rw [← Category.assoc (R₁ ◁ _), powComp_sig, Preadditive.sub_comp, Preadditive.comp_sub,
      Preadditive.sum_comp, Preadditive.comp_sum]
    simp only [Category.assoc]
  have B : L.cupL ≫ R₁ ◁ powComp x₁ m ≫ L.sig ≫ L.capL =
      -(∑ n ∈ Finset.range h.toNat, (L.cupL ≫ L.capD (m + n)) ≫ (L.cupN n ≫ L.capD h.toNat) -
        L.cupL ≫ L.capD (m + h.toNat)) := by
    calc L.cupL ≫ R₁ ◁ powComp x₁ m ≫ L.sig ≫ L.capL =
        -(L.cupL ≫ R₁ ◁ powComp x₁ m ≫ (L.sig ≫ L.sigL) ≫ L.capD h.toNat) := by
          rw [capL_of_nonneg hh]
          simp only [Preadditive.comp_neg, Category.assoc]
      _ = -(L.cupL ≫ R₁ ◁ powComp x₁ m ≫
          (∑ n ∈ Finset.range h.toNat, L.capD n ≫ L.cupN n - 𝟙 _) ≫ L.capD h.toNat) := by
          rw [sig_sigL_of_nonneg hh]
      _ = _ := by
          simp only [Preadditive.sub_comp, Preadditive.sum_comp, Preadditive.comp_sub,
            Preadditive.comp_sum, Category.assoc, Category.id_comp, hc, whiskerLeft_powComp_capD]
  rw [show ∀ (X Y Z : 𝟙 b ⟶ 𝟙 b), X - Y = Z ↔ -(Y - X) = Z from fun X Y Z => by
    rw [neg_sub], ← A, B, neg_neg]

theorem infGrass_nonneg (hh : 0 ≤ h) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1 + (h.toNat + 1)),
      L.ccw (-1 + i) ≫ L.cw ((m : ℤ) - 1 - (-1 + i)) = 0 := by
  have hN : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh
  rw [Finset.sum_range_add, Finset.sum_range_succ' (n := m), Finset.sum_range_succ (n := h.toNat)]
  have e1 : ∀ i ∈ Finset.range m, L.ccw (-1 + ↑(i + 1)) ≫ L.cw ((m : ℤ) - 1 - (-1 + ↑(i + 1))) =
      (L.cupL ≫ L.capD i) ≫ (L.cupD (m - 1 - i) ≫ L.capL) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show (-1 : ℤ) + ↑(i + 1) = ↑i by push_cast; ring,
      show (m : ℤ) - 1 - ↑i = ↑(m - 1 - i) by omega, ccw_of_nonneg (by positivity),
      cw_of_nonneg (by positivity), Int.toNat_natCast, Int.toNat_natCast]
  have e2 : ∀ n ∈ Finset.range h.toNat,
      L.ccw (-1 + ↑(m + 1 + n)) ≫ L.cw ((m : ℤ) - 1 - (-1 + ↑(m + 1 + n))) =
        -((L.cupL ≫ L.capD (m + n)) ≫ (L.cupN n ≫ L.capD h.toNat)) := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [show (-1 : ℤ) + ↑(m + 1 + n) = ↑(m + n) by push_cast; ring,
      show (m : ℤ) - 1 - ↑(m + n) = -↑n - 1 by push_cast; ring, ccw_of_nonneg (by positivity),
      Int.toNat_natCast, cw_of_neg_of_gt (by omega) (by omega),
      show -(-(n : ℤ) - 1) - 1 = n by ring, Int.toNat_natCast, Preadditive.comp_neg]
  have e3 : L.ccw (-1 + ↑(m + 1 + h.toNat)) ≫ L.cw ((m : ℤ) - 1 - (-1 + ↑(m + 1 + h.toNat))) =
      L.cupL ≫ L.capD (m + h.toNat) := by
    rw [show (-1 : ℤ) + ↑(m + 1 + h.toNat) = ↑(m + h.toNat) by push_cast; ring,
      show (m : ℤ) - 1 - ↑(m + h.toNat) = -h - 1 by omega, ccw_of_nonneg (by positivity),
      cw_of_neg_of_eq (by omega) rfl, Category.comp_id, Int.toNat_natCast]
  have e4 : L.ccw (-1 + ↑(0 : ℕ)) ≫ L.cw ((m : ℤ) - 1 - (-1 + ↑(0 : ℕ))) =
      L.ccw (-1) ≫ (L.cupD m ≫ L.capL) := by
    rw [show (-1 : ℤ) + ↑(0 : ℕ) = -1 by simp, show (m : ℤ) - 1 - -1 = ↑m by ring,
      cw_of_nonneg (by positivity), Int.toNat_natCast]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, e3, e4, Finset.sum_neg_distrib]
  have K' := L.key_nonneg hh m
  rw [sub_eq_iff_eq_add] at K'
  rw [K']
  have hZ : L.cupL ≫ L.sig ≫ powComp x₂ m ▷ R₂ ≫ L.capL + L.ccw (-1) ≫ (L.cupD m ≫ L.capL) =
      0 := by
    rcases lt_or_eq_of_le hh with hh' | hh'
    · rw [← Category.assoc, cupL_sig hh', Limits.zero_comp,
        ccw_of_neg_of_lt (by omega) (by omega), Limits.zero_comp, add_zero]
    · subst hh'
      rw [ccw_of_neg_of_eq (by omega) (by omega), Category.id_comp, cupL_of_nonpos le_rfl,
        Category.assoc, ← Category.assoc L.sigL, sigL_sig_of_nonneg le_rfl,
        Preadditive.neg_comp, Category.id_comp, Preadditive.comp_neg, ← Category.assoc,
        cupD_powComp_whiskerRight]
      simp
  rw [← hZ]
  abel

/-- **Brundan, Theorem 3.2 (the infinite Grassmannian relation).** For every `m ≥ 0` (Brundan's
`t = m + 1 > 0`), `∑_{r + s = m - 1} ccw r ∘ cw s = 0`, the sum taken over any window
`r ∈ [lo, lo + K)` containing `[min h 0 - 1, m + max h 0]` (outside it all terms vanish). -/
theorem infGrass (m : ℕ) (lo : ℤ) (K : ℕ) (hlo : lo ≤ min h 0 - 1)
    (hK : (m : ℤ) + max h 0 ≤ lo + K - 1) :
    ∑ i ∈ Finset.range K, L.ccw (lo + i) ≫ L.cw ((m : ℤ) - 1 - (lo + i)) = 0 := by
  rcases le_or_gt 0 h with hh | hh
  · have hN : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh
    rw [sum_range_window (fun r => L.ccw r ≫ L.cw ((m : ℤ) - 1 - r)) (lo' := -1)
      (K' := m + 1 + (h.toNat + 1)) ?_ (by omega) (by push_cast; omega)]
    · exact L.infGrass_nonneg hh m
    · intro r hr
      rcases hr with hr | hr
      · rw [ccw_of_neg_of_lt (by omega) (by omega), Limits.zero_comp]
      · push_cast at hr
        rw [cw_of_neg_of_lt (by omega) (by omega), Limits.comp_zero]
  · have hN : ((-h).toNat : ℤ) = -h := Int.toNat_of_nonneg (by omega)
    have hD := L.dual.infGrass_nonneg (by omega) m
    rw [← sum_range_window (fun r => L.dual.ccw r ≫ L.dual.cw ((m : ℤ) - 1 - r))
      (lo := (m : ℤ) - lo - K) (K := K) (lo' := -1) (K' := m + 1 + ((-h).toNat + 1)) ?_
      (by omega) (by push_cast; omega)] at hD
    · simp only [dual_ccw, dual_cw] at hD
      have hD' : (∑ i ∈ Finset.range K,
          L.ccw ((m : ℤ) - 1 - ((m : ℤ) - lo - K + i)) ≫ L.cw ((m : ℤ) - lo - K + i)).op = 0 := by
        rw [← hD, op_sum]
        rfl
      have hD'' := congrArg Quiver.Hom.unop hD'
      simp only [Quiver.Hom.unop_op] at hD''
      rw [← Finset.sum_range_reflect] at hD''
      rw [← hD'']
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      congr 2 <;> push_cast [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_sub (by omega : i ≤ K - 1)]
        <;> ring
    · intro r hr
      rcases hr with hr | hr
      · rw [ccw_of_neg_of_lt (L := L.dual) (by omega) (by omega), Limits.zero_comp]
      · push_cast at hr
        rw [cw_of_neg_of_lt (L := L.dual) (by omega) (by omega), Limits.comp_zero]

end RouqLoc

end Categorification.TwoRep
