/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BlockKernelDerivedSequence
import Categorification.WeightedKLR.RedStrands.BlockKernelSingleLayer
import Categorification.WeightedKLR.RedStrands.BraidedFactorizationExits

/-!
# The first paired red block with a terminal spectator

Webster, arXiv:1309.3796v2, Lemma 6.8 at (6.21).
When all black strands precede the third red, the retained cut is maximal
after global violation.
-/

noncomputable section

namespace Categorification.Stendhal.BraidedStendhalAlgebra

open KLR
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

universe u v w

variable {I : Type u} {k : Type v} [DecidableEq I] [CommRing k] {ν : Multiset I}
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin 3 → I →₀ ℕ)

local notation "μ" => stendhalWeight 3 ν
local notation "N" => Multiset.card μ

private theorem firstPair_root_eq_zero (s : Seq μ) (order : redWord s = List.finRange 3)
    (hs : ¬ IsViolated s) (r : Fin 3) (hr : r = 0 ∨ r = 1) (i : I) :
    adjacentBlockRoot 0 1 s r i = 0 := by
  have nonempty : 0 < N := by
    obtain ⟨j, _⟩ := exists_lbl_eq_inr s 0
    exact Nat.zero_lt_of_lt j.isLt
  let p : Fin N := ⟨0, nonempty⟩
  have first : s.lbl p = Sum.inr (0 : Fin 3) := by
    rcases h : s.lbl p with c | c
    · exact (hs ⟨nonempty, by rw [show (s.lbl ⟨0,nonempty⟩) = s.lbl p from rfl, h]; rfl⟩).elim
    · have hpos : p = redPos s c := eq_redPos h
      have h01 : redPos s 0 < redPos s 1 :=
        lt_of_redWord_eq_append
          (show redWord s = ([] : List (Fin 3)) ++ 0 :: 1 :: [2] from order)
          (lbl_redPos s 0) (lbl_redPos s 1)
      have h12 : redPos s 1 < redPos s 2 :=
        lt_of_redWord_eq_append
          (show redWord s = ([0] : List (Fin 3)) ++ 1 :: 2 :: [] from order)
          (lbl_redPos s 1) (lbl_redPos s 2)
      have earlier (r : Fin 3) (hr : r ≠ 0) : redPos s 0 < redPos s r := by
        fin_cases r
        · exact (hr rfl).elim
        · exact h01
        · exact h01.trans h12
      have hc : c = 0 := by
        by_contra hn
        have lt := earlier c hn
        rw [← hpos] at lt
        exact (Nat.not_lt_zero (redPos s 0).val) lt
      exact congrArg Sum.inr hc
  rw [adjacentBlockRoot, ite_eq_left hr, blockBlackCount]
  have hempty : (Finset.univ.filter fun x : Fin N =>
      s.lbl x = .inl i ∧ ∀ y c, c ∈ ({0,1} : Finset (Fin 3)) →
        s.lbl y = .inr c → x < y) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro x _ hx
    exact (Nat.not_lt_zero x.val) (hx.2 p 0 (by decide) first)
  rw [hempty, Finset.card_empty]

private theorem countBefore_mono_at (s : Seq μ) (i : I) {a b : ℕ} (hab : a ≤ b) :
    countBefore s (.inl i) a ≤ countBefore s (.inl i) b := by
  apply Finset.sum_le_sum
  intro p _
  by_cases h : p.val < a ∧ s.lbl p = Sum.inl i
  · have hb : p.val < b ∧ s.lbl p = Sum.inl i := ⟨lt_of_lt_of_le h.1 hab, h.2⟩
    simp [h, hb]
  · simpa only [ite_eq_right h] using
      (Nat.zero_le (if p.val < b ∧ s.lbl p = Sum.inl i then 1 else 0))

private theorem countBefore_terminal_red (t : Seq μ)
    (terminal : ∀ (p : Fin N) (i : I), t.lbl p = Sum.inl i → p < redPos t 2)
    (i : I) : countBefore t (.inl i) N = countBefore t (.inl i) (redPos t 2) := by
  apply Finset.sum_congr rfl
  intro p _
  by_cases hl : t.lbl p = Sum.inl i
  · have hbefore : p.val < (redPos t 2).val := terminal p i hl
    simp only [p.isLt, hl, and_true, hbefore, ite_true]
  · simp only [hl, and_false, ite_false]

/-- With the first two reds paired, a final spectator beyond all black
strands is a maximal retained cut. The higher kernel then vanishes for
arbitrary black content. -/
theorem firstPair_terminal_blockLoadingKernel_eq_bot (t : Seq μ)
    (order : redWord t = List.finRange 3)
    (terminal : ∀ (p : Fin N) (i : I), t.lbl p = Sum.inl i → p < redPos t 2) :
    blockLoadingKernel Q Λ t 0 1 = ⊥ := by
  apply blockLoadingKernel_eq_bot_of_maximal
  intro s hs hlt
  by_contra h
  apply hlt.not_ge
  intro r i
  have same : redWord s = List.finRange 3 := hs.trans order
  fin_cases r
  · change adjacentBlockRoot 0 1 s 0 i ≤ adjacentBlockRoot 0 1 t 0 i
    rw [firstPair_root_eq_zero s same h 0 (Or.inl rfl)]
    exact Nat.zero_le _
  · change adjacentBlockRoot 0 1 s 1 i ≤ adjacentBlockRoot 0 1 t 1 i
    rw [firstPair_root_eq_zero s same h 1 (Or.inr rfl)]
    exact Nat.zero_le _
  · change blockBlackCount s ({2} : Finset (Fin 3)) i ≤ blockBlackCount t {2} i
    simp only [blockBlackCount_singleton, blackCount_eq_countBefore]
    calc
      _ ≤ countBefore s (.inl i) N := countBefore_mono_at s i (redPos s 2).isLt.le
      _ = countBefore t (.inl i) N := by rw [countBefore_card, countBefore_card]
      _ = _ := countBefore_terminal_red t terminal i

open CategoryTheory CategoryTheory.Limits DG DG.DerivedCategory
open scoped DG.DegreeZero
attribute [local instance 1200] Ring.toIntAlgebra

local notation "T" t:arg =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν (redWord t))
local notation "U" target:arg =>
  IsIdempotentElem.Corner (isIdempotentElem_violMk_redProj k Q Λ ν target)

set_option backward.isDefEq.respectTransparency false in
/-- The braid of the terminal-spectator partial standard is concentrated
in degree zero for any target red order and arbitrary black content. -/
theorem firstPair_terminal_partialStandard_braid_homology_vanish (t : Seq μ)
    (order : redWord t = List.finRange 3)
    (terminal : ∀ (p : Fin N) (i : I), t.lbl p = Sum.inl i → p < redPos t 2)
    (target : List (Fin 3))
    [HasDerivedCategory.{w, max u v} (T t)ᵐᵒᵖ] [HasDerivedCategory.{w, max u v} (U target)ᵐᵒᵖ]
    (j : ℤ) (hj : j ≠ 0) :
    IsZero ((homologyFunctor (A := (U target)ᵐᵒᵖ) ℤ j).obj
      ((braidingFunctor k Q Λ ν (redWord t) target).obj
        (DG.DerivedCategory.Q.obj ((degreeZeroModuleFunctor (T t)ᵐᵒᵖ).obj
          (blockLoadingShortComplex Q Λ t 0 1).X₃)))) :=
  blockPartialStandard_braid_homology_vanish_of_bot Q Λ t 0 1 target
    (firstPair_terminal_blockLoadingKernel_eq_bot Q Λ t order terminal) j hj

end Categorification.Stendhal.BraidedStendhalAlgebra
