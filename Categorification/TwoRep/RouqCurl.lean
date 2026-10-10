/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TwoRep.RouqGrass
import Categorification.TwoRep.FakeBubbles

/-!
# Inverse components and curls from Rouquier's data

The inverse-component expansions of Brundan, *On the definition of Kac–Moody 2-category*,
arXiv:1501.00350v1, Corollaries 3.3–3.5, in a preadditive bicategory with additive whiskering.
These formulas express the components of the inverse of Rouquier's map using left cups,
left caps and bubbles. They supply the decomposition relations without a grading or a
restriction on endomorphisms of identity 1-morphisms.
-/

noncomputable section

namespace Categorification.TwoRep

open CategoryTheory CategoryTheory.Bicategory Opposite

universe w v u

namespace RouqLoc

variable {C : Type u} [Bicategory.{w, v} C] [∀ a b : C, Preadditive (a ⟶ b)] [AdditiveWhiskering C]
  {a b c : C} {E₁ : a ⟶ b} {R₁ : b ⟶ a} {E₂ : b ⟶ c} {R₂ : c ⟶ b}
  {adj₁ : E₁ ⊣ R₁} {adj₂ : E₂ ⊣ R₂} {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}
  {τ : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {h : ℤ} (L : RouqLoc adj₁ adj₂ x₁ x₂ τ h)

/-- A left cup with fewer than `h` dots is killed by the rightward crossing (Brundan (3.14)). -/
theorem cupL_powComp_sig (hh : 0 < h) {r : ℕ} (hr : r < h.toNat) :
    L.cupL ≫ R₁ ◁ powComp x₁ r ≫ L.sig = 0 := by
  rw [L.powComp_sig, Preadditive.comp_sub, ← Category.assoc, L.cupL_sig hh,
    Limits.zero_comp, Preadditive.comp_sum]
  have hz : ∑ j ∈ Finset.range r, L.cupL ≫ L.capD j ≫ L.cupD (r - 1 - j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [← Category.assoc, L.cupL_capD hh (by omega), ite_eq_right (by omega), Limits.zero_comp]
  rw [hz, sub_zero]

/-- The bubble convolution pairing an inverse cup with a dotted cap (Brundan (3.15)). -/
theorem cupN_bubble_pairing (hh : 0 < h) {m n : ℕ} (hm : m < h.toNat) (hn : n < h.toNat) :
    ∑ r ∈ Finset.range (h.toNat - n), L.cw (-(n : ℤ) - r - 2) ≫ L.ccw (r + m) =
      if n = m then 𝟙 _ else 0 := by
  have hN : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh.le
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · rw [ite_eq_right (by omega)]
    apply Finset.sum_eq_zero
    intro r hr
    have hr' := Finset.mem_range.mp hr
    rw [L.ccw_of_lt hh (by omega), Limits.comp_zero]
  · subst m
    rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (h.toNat - n - 1)]
    · rw [show -(n : ℤ) - ↑(h.toNat - n - 1) - 2 = -h - 1 by omega,
        show (↑(h.toNat - n - 1) : ℤ) + ↑n = h - 1 by omega,
        L.cw_of_neg_of_eq (by omega) rfl, L.ccw_self hh, Category.id_comp]
    · intro r hr hrn
      have hr' := Finset.mem_range.mp hr
      rw [L.ccw_of_lt hh (by omega), Limits.comp_zero]
    · intro hnmem
      exact False.elim (hnmem (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right (by omega)]
    have hg := L.infGrass (m - n - 1) (-1) (m - n - 1 + h.toNat + 2)
      (by omega) (by omega)
    have hw := sum_range_window
      (fun s : ℤ => L.ccw s ≫ L.cw ((m - n - 1 : ℕ) - 1 - s))
      (lo := -1) (K := m - n - 1 + h.toNat + 2) (lo' := m) (K' := h.toNat - n)
      (by
        intro s hs
        rcases hs with hs | hs
        · rw [L.ccw_of_lt hh (by omega), Limits.zero_comp]
        · rw [L.cw_of_neg_of_lt (by omega) (by omega), Limits.comp_zero])
      (by omega) (by omega)
    rw [hw] at hg
    rw [← hg]
    apply Finset.sum_congr rfl
    intro r _
    rw [Bicategory.endId_comm]
    congr 2 <;> omega

/-- **Brundan, Corollary 3.3, (3.12)**: the inverse cup components expressed by bubbles and
left cups. The omitted terms vanish below the minimal bubble degree. -/
theorem cupN_expansion (hh : 0 < h) {n : ℕ} (hn : n < h.toNat) :
    L.cupN n = ∑ r ∈ Finset.range (h.toNat - n),
      L.cw (-(n : ℤ) - r - 2) ≫ L.cupL ≫ R₁ ◁ powComp x₁ r := by
  rw [L.cupN_of_nonneg hh.le]
  symm
  apply (L.ip hh.le).eq_g' hn
  · rw [Preadditive.sum_comp]
    apply Finset.sum_eq_zero
    intro r hr
    have hr' := Finset.mem_range.mp hr
    rw [Category.assoc, Category.assoc, L.cupL_powComp_sig hh (by omega), Limits.comp_zero]
  · intro m hm
    rw [Preadditive.sum_comp]
    calc (∑ r ∈ Finset.range (h.toNat - n),
        (L.cw (-(n : ℤ) - r - 2) ≫ L.cupL ≫ R₁ ◁ powComp x₁ r) ≫ L.capD m) =
        ∑ r ∈ Finset.range (h.toNat - n), L.cw (-(n : ℤ) - r - 2) ≫ L.ccw (r + m) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Category.assoc, Category.assoc, L.whiskerLeft_powComp_capD,
            L.ccw_of_nonneg (by positivity), Int.toNat_add (by positivity) (by positivity),
            Int.toNat_natCast, Int.toNat_natCast]
      _ = _ := L.cupN_bubble_pairing hh hm hn

/-- **Brundan, Corollary 3.3, (3.13)**: the dual expansion of the inverse cap components. -/
theorem capN_expansion (hh : h < 0) {n : ℕ} (hn : n < (-h).toNat) :
    L.capN n = ∑ r ∈ Finset.range ((-h).toNat - n),
      powComp x₂ r ▷ R₂ ≫ L.capL ≫ L.ccw (-(n : ℤ) - r - 2) := by
  have hd := L.dual.cupN_expansion (by omega) hn
  simp only [dual_cupN, dual_cw, dual_cupL] at hd
  have hu := congrArg Quiver.Hom.unop hd
  change L.capN n = (∑ r ∈ Finset.range ((-h).toNat - n),
    ((Quiver.Hom.unop (powComp x₂.op r) ▷ R₂ ≫ L.capL) ≫
      L.ccw (-(n : ℤ) - r - 2)).op).unop at hu
  rw [unop_sum] at hu
  change L.capN n = ∑ r ∈ Finset.range ((-h).toNat - n),
    ((powComp x₂.op r).unop ▷ R₂ ≫ L.capL) ≫ L.ccw (-(n : ℤ) - r - 2) at hu
  rw [hu]
  apply Finset.sum_congr rfl
  intro r _
  rw [unop_powComp, Category.assoc]
  rfl

/-- **Brundan, Corollary 3.4, (3.16)**: the decomposition of `E F` into `F E` and identity
summands, written using bubbles and left cups. -/
theorem decompEF :
    L.sig ≫ L.sigL = (∑ n ∈ Finset.range h.toNat, ∑ r ∈ Finset.range (h.toNat - n),
      L.capD n ≫ L.cw (-(n : ℤ) - r - 2) ≫ L.cupL ≫ R₁ ◁ powComp x₁ r) - 𝟙 _ := by
  rcases lt_or_ge 0 h with hh | hh
  · rw [L.sig_sigL_of_nonneg hh.le]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [L.cupN_expansion hh (Finset.mem_range.mp hn), Preadditive.comp_sum]
  · rw [L.sig_sigL_of_nonpos hh, Int.toNat_of_nonpos hh]
    simp

/-- **Brundan, Corollary 3.4, (3.17)**: the dual decomposition of `F E`. -/
theorem decompFE :
    L.sigL ≫ L.sig = (∑ n ∈ Finset.range (-h).toNat, ∑ r ∈ Finset.range ((-h).toNat - n),
      powComp x₂ r ▷ R₂ ≫ L.capL ≫ L.ccw (-(n : ℤ) - r - 2) ≫ L.cupD n) - 𝟙 _ := by
  rcases lt_or_ge h 0 with hh | hh
  · rw [L.sigL_sig_of_nonpos hh.le]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [L.capN_expansion hh (Finset.mem_range.mp hn), Preadditive.sum_comp]
    simp only [Category.assoc]
  · rw [L.sigL_sig_of_nonneg hh, Int.toNat_of_nonpos (by omega : -h ≤ 0)]
    simp

omit [AdditiveWhiskering C] in
/-- **Brundan, Corollary 3.5, (3.18), first identity**: the capped rightward crossing is a
finite sum of dotted caps and clockwise bubbles. -/
theorem sig_capL_expansion :
    L.sig ≫ L.capL = ∑ n ∈ Finset.range (h + 1).toNat,
      L.capD n ≫ L.cw (-(n : ℤ) - 1) := by
  rcases lt_or_ge h 0 with hh | hh
  · rw [L.sig_capL hh, Int.toNat_of_nonpos (by omega : h + 1 ≤ 0)]
    simp
  · have hN : (h.toNat : ℤ) = h := Int.toNat_of_nonneg hh
    rw [L.capL_of_nonneg hh, Preadditive.comp_neg, ← Category.assoc,
      L.sig_sigL_of_nonneg hh, Preadditive.sub_comp, Preadditive.sum_comp, Category.id_comp,
      show (h + 1).toNat = h.toNat + 1 by omega, Finset.sum_range_succ,
      show -(h.toNat : ℤ) - 1 = -h - 1 by omega,
      L.cw_of_neg_of_eq (by omega) rfl, Category.comp_id]
    have hs : ∑ n ∈ Finset.range h.toNat, L.capD n ≫ L.cw (-(n : ℤ) - 1) =
        -(∑ n ∈ Finset.range h.toNat, (L.capD n ≫ L.cupN n) ≫ L.capD h.toNat) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      have hn' := Finset.mem_range.mp hn
      rw [L.cw_of_neg_of_gt (by omega) (by omega),
        show -(-(n : ℤ) - 1) - 1 = n by ring, Int.toNat_natCast,
        Preadditive.comp_neg, Category.assoc]
    rw [hs]
    abel

/-- **Brundan, Corollary 3.5, (3.18), second identity**: the rightward crossing on a left
cup is a finite sum of counter-clockwise bubbles and dotted cups. -/
theorem cupL_sig_expansion :
    L.cupL ≫ L.sig = -(∑ n ∈ Finset.range (-h + 1).toNat,
      L.ccw (-(n : ℤ) - 1) ≫ L.cupD n) := by
  have hd := L.dual.sig_capL_expansion
  simp only [dual_sig, dual_capL, dual_capD, dual_cw] at hd
  have hu := congrArg Quiver.Hom.unop hd
  rw [Coop.unop_sum₂] at hu
  change L.cupL ≫ (-L.sig) = ∑ n ∈ Finset.range (-h + 1).toNat,
    L.ccw (-(n : ℤ) - 1) ≫ L.cupD n at hu
  rw [Preadditive.comp_neg] at hu
  simpa only [neg_neg] using congrArg Neg.neg hu

end RouqLoc

end Categorification.TwoRep
