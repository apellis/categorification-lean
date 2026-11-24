/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LabelTwoMiddleFixedComplex

/-!
# Loading support of the label-two middle complex

Webster, arXiv:1309.3796v2, §8.2, preceding Proposition 8.4. The middle
standard is supported at the middle and terminal loadings. The other
ordered loadings vanish by the violated and higher-cut relations.
-/

noncomputable section

namespace Categorification.Stendhal.LabelTwo

open KLR KLRAlgebra TypeA

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

local notation "blackWeight" => (({()} : Multiset Unit) + {()})
local notation "μ" => stendhalWeight 2 blackWeight

private abbrev higherLoading : Seq μ := sadj (Multiset.card μ) 2 • loading

private abbrev position (j : Fin 4) : Fin (Multiset.card μ) := j

private theorem unique_red_position (s : Seq μ) (hs : IsRedOrdered s)
    {x y : Fin (Multiset.card μ)} {r : Fin 2}
    (hx : s.lbl x = .inr r) (hy : s.lbl y = .inr r) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exact (lt_irrefl _ (hs _ _ _ _ h hx hy)).elim
  · exact h
  · exact (lt_irrefl _ (hs _ _ _ _ h hy hx)).elim

private theorem ordered_nonviolated_cases (s : Seq μ) (hs : IsRedOrdered s)
    (hv : ¬ IsViolated s) : s = loading ∨ s = terminalLoading ∨ s = higherLoading := by
  obtain ⟨j,hj⟩ := exists_lbl_eq_inr s 0
  obtain ⟨l,hl⟩ := exists_lbl_eq_inr s 1
  have hz : s.lbl (position 0) = .inr 0 := by
    cases h : s.lbl (position 0) with
    | inl c => exact (hv ⟨by decide, by exact congrArg Sum.isLeft h⟩).elim
    | inr r =>
      fin_cases r
      · rfl
      · have hh : position 0 < j := by
          apply lt_of_le_of_ne (Fin.zero_le _)
          intro he
          have he' := congrArg s.lbl he
          rw [h,hj] at he'
          exact (by decide : (Sum.inr (1 : Fin 2) : Unit ⊕ Fin 2) ≠ .inr 0) he'
        exact (by decide : ¬ (1 : Fin 2) < 0) (hs _ _ _ _ hh h hj) |>.elim
  have hne : l ≠ position 0 := by
    intro he
    rw [he,hz] at hl
    contradiction
  have hsfun (p : Fin (Multiset.card μ)) :
      s.lbl p = if p = position 0 then .inr 0 else if p = l then .inr 1 else .inl () := by
    by_cases h0 : p = position 0
    · simpa only [h0, ite_true] using hz
    by_cases h1 : p = l
    · simpa only [h1, ite_eq_right (show l ≠ position 0 from hne), ite_true] using hl
    rw [ite_eq_right h0, ite_eq_right h1]
    cases hh : s.lbl p with
    | inl a => cases a; rfl
    | inr r =>
      fin_cases r
      · exact (h0 (unique_red_position s hs hh hz)).elim
      · exact (h1 (unique_red_position s hs hh hl)).elim
  have hcases : l = position 1 ∨ l = position 2 ∨ l = position 3 := by
    fin_cases l <;> first | exact (hne rfl).elim | decide
  rcases hcases with h | h | h
  · refine Or.inr (Or.inl (Subtype.ext (funext fun p => (hsfun p).trans ?_)))
    rw [h]
    fin_cases p <;> decide
  · refine Or.inl (Subtype.ext (funext fun p => (hsfun p).trans ?_))
    rw [h]
    fin_cases p <;> decide
  · refine Or.inr (Or.inr (Subtype.ext (funext fun p => (hsfun p).trans ?_)))
    rw [h]
    fin_cases p <;> decide

private theorem higherLoading_lt : StendhalLT loading higherLoading := by
  unfold StendhalLT StendhalLE
  decide +kernel

variable (k : Type) [Field k]

/-- At any other loading, the action of the loading idempotent on the
actual middle standard is zero. -/
theorem middleStandard_smul_eq_zero_of_other_loading
    (s : Seq μ) (hs : IsRedOrdered s) (hm : s ≠ loading) (ht : s ≠ terminalLoading)
    (z : Standard k) : seqIdem (parameter k) weights s hs • z = 0 := by
  by_cases hv : IsViolated s
  · have hz : seqIdem (parameter k) weights s hs = 0 := by
      change (StendhalAlgebra.violatedIdeal k (parameter k) weights blackWeight).ringCon.mk' _ = 0
      rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
      exact TwoSidedIdeal.subset_span ⟨s, hs, hv, rfl⟩
    rw [hz, zero_smul]
  · rcases ordered_nonviolated_cases s hs hv with h | h | h
    · exact (hm h).elim
    · exact (ht h).elim
    · exact seqIdem_smul_leftStandard_eq_zero (parameter k) weights loading_ordered hs
        (h ▸ higherLoading_lt) z

/-- Away from the middle and terminal loadings, the alternating complex
has zero terms after applying the loading idempotent. -/
theorem middleFixed_subsingleton_of_other_loading
    (s : Seq μ) (hs : IsRedOrdered s) (hm : s ≠ loading) (ht : s ≠ terminalLoading) :
    Subsingleton (fixSub k (Standard k) (seqIdem (parameter k) weights s hs)) := by
  constructor
  intro x y
  apply Subtype.ext
  exact (x.property.symm.trans
    (middleStandard_smul_eq_zero_of_other_loading k s hs hm ht x.val)).trans
      (y.property.symm.trans
        (middleStandard_smul_eq_zero_of_other_loading k s hs hm ht y.val)).symm

end Categorification.Stendhal.LabelTwo
