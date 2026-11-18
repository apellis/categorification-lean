/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.TensorCornerBlackFormula
import Categorification.WeightedKLR.RedStrands.TensorHomInduction

/-!
# Computing the graded dimension of an ordinary Stendhal corner

For the canonical grading, the boundary recursion in Webster, arXiv:1309.3796v2,
§4.7, Lemma 4.36, determines each graded dimension of `e_s T e_t`. The calculation
uses only the Cartan datum and the two weighted boundary words. We compare its
black deletion, common last red and vacuum cases by induction on the number of strands.
-/

noncomputable section
namespace Categorification.Stendhal

open KLR KLRAlgebra CycKLR QuantumGroup Categorification.Graded FirstWeight
open LieLean.QuantumGroup
attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

variable {I : Type} [DecidableEq I] {k : Type*} [Field k]
    {Q : I → I → MvPolynomial (Fin 2) k} (C : CartanDatum I) (hQ : IsRouquierQ C Q)

local notation "grade" L => stendhalGradingDatum L hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ)
local notation:max "word(" L "," s ")" => List.map (Sum.map id L) (List.ofFn (KLR.Seq.lbl s))

private def cornerAgreement {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) (ν : Multiset I) : Prop :=
  ∀ (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)
    (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t),
    sequenceCornerPoly (grade Λ) s hs t ht = cornerPolynomial C word(Λ, s) word(Λ, t)

private theorem agrees_at_length (n : ℕ) :
    ∀ (ℓ : ℕ) (ν : Multiset I), ℓ + ν.card = n → ∀ Λ : Fin ℓ → I →₀ ℕ, cornerAgreement C hQ Λ ν := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ℓ ν hn Λ s hs t ht
    by_cases hp : 0 < ℓ + ν.card
    · have black_case (a b : Seq (stendhalWeight ℓ ν)) (ha : IsRedOrdered a) (hb : IsRedOrdered b)
          (i : I) (he : a.lbl (terminalPos hp) = .inl i) :
          (∃ u, word(Λ, a) = u ++ [.inl i]) ∧
          sequenceCornerPoly (grade Λ) a ha b hb = cornerPolynomial C word(Λ, a) word(Λ, b) := by
        have hm := a.mem (terminalPos hp)
        change a.lbl (terminalPos hp) ∈ stendhalWeight ℓ ν at hm
        rw [he] at hm
        have hi : i ∈ ν := by simpa [stendhalWeight] using hm
        obtain ⟨β, hβ⟩ := Multiset.exists_cons_of_mem hi
        rw [← Multiset.singleton_add] at hβ
        subst ν
        obtain ⟨u, hu, heq⟩ := exists_appendBlack_terminal a he ha
        subst a
        have hsmall : ℓ + β.card < n := by
          simp only [Multiset.card_add, Multiset.card_singleton] at hn
          omega
        exact ⟨⟨_, weightedWord_appendBlackLoading Λ i β u⟩,
          sequenceCornerPoly_eq_wordCornerPoly_appendBlack C hQ Λ β (ih _ hsmall ℓ β rfl Λ) i u hu b hb⟩
      cases hse : s.lbl (terminalPos hp) with
      | inl i => exact (black_case s t hs ht i hse).2
      | inr r =>
        cases ℓ with
        | zero => exact r.elim0
        | succ ℓ =>
          have hpos : terminalPos hp = lastRedPosition ℓ ν := by
            apply Fin.ext
            change (stendhalWeight (ℓ + 1) ν).card - 1 = ν.card + ℓ
            rw [cardinal_weight]
            omega
          have hsr := terminal_red_last s hs r (by simpa only [hpos] using hse)
          obtain ⟨⟨u, hu⟩, hsu⟩ := (appendRedOrderedEquiv (ℓ := ℓ) (ν := ν)).surjective ⟨s, hs, hsr⟩
          have hes : appendRedLoading u = s := congrArg Subtype.val hsu
          subst s
          cases hte : t.lbl (terminalPos hp) with
          | inl i =>
            obtain ⟨⟨w, hw⟩, he⟩ := black_case t (appendRedLoading u) ht hs i hte
            rw [sequenceCornerPoly_comm C hQ Λ, he, weightedWord_appendRedLoading, hw,
              cornerPolynomial_terminalBlack_right, cornerPolynomial_terminalBlack]
          | inr r' =>
            have htr := terminal_red_last t ht r' (by simpa only [hpos] using hte)
            obtain ⟨⟨v, hv⟩, htv⟩ := (appendRedOrderedEquiv (ℓ := ℓ) (ν := ν)).surjective ⟨t, ht, htr⟩
            have het : appendRedLoading v = t := congrArg Subtype.val htv
            subst t
            rw [sequenceCornerPoly_appendRed, weightedWord_appendRedLoading, weightedWord_appendRedLoading,
              cornerPolynomial_terminalRed]
            exact ih _ (by omega) ℓ ν rfl (Λ ∘ Fin.castSucc) u hu v hv
    · have hℓ : ℓ = 0 := by omega
      have hν : ν = 0 := Multiset.card_eq_zero.mp (by omega)
      subst ℓ
      subst ν
      obtain rfl := zero_boundary_eq s vacuumSeq
      obtain rfl := zero_boundary_eq t vacuumSeq
      rw [sequenceCornerPoly_vacuum, word_vacuumSeq]
      exact (cornerPolynomial_empty C).symm

/-- The graded corner of arbitrary ordered Stendhal loadings has the Laurent polynomial
computed by deleting strands from the two weighted words (Webster v2, §4.7, Lemma 4.36). -/
theorem sequenceCornerPoly_eq_wordCornerPoly {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) {ν : Multiset I}
    (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)
    (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) :
    sequenceCornerPoly (grade Λ) s hs t ht = cornerPolynomial C word(Λ, s) word(Λ, t) :=
  agrees_at_length C hQ (ℓ + ν.card) ℓ ν rfl Λ s hs t ht

/-- For fixed red multiplicities and ordered boundary words, the homogeneous
corner dimensions in Webster, arXiv:1309.3796v2, §4.7, Lemma 4.36 agree over
any two fields with homogeneous Rouquier parameters for the same Cartan datum. -/
theorem finrank_sequenceCornerGrade_eq_of_parameters
    {K : Type*} [Field K] {P : I → I → MvPolynomial (Fin 2) K} (hP : IsRouquierQ C P)
    {ℓ : ℕ} (Λ : Fin ℓ → I →₀ ℕ) {ν : Multiset I}
    (s : Seq (stendhalWeight ℓ ν)) (hs : IsRedOrdered s)
    (t : Seq (stendhalWeight ℓ ν)) (ht : IsRedOrdered t) (d : ℤ) :
    Module.finrank k (sequenceCornerGrade
      (stendhalGradingDatum Λ hQ.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hQ))
      s hs t ht d) =
    Module.finrank K (sequenceCornerGrade
      (stendhalGradingDatum Λ hP.gradingDatum (fun i => C.dot i i / 2) (dotDegree C hP))
      s hs t ht d) := by
  apply Int.ofNat_inj.mp
  rw [← sequenceCornerPoly_coeff C hQ Λ s hs t ht d,
      ← sequenceCornerPoly_coeff C hP Λ s hs t ht d,
      sequenceCornerPoly_eq_wordCornerPoly C hQ Λ s hs t ht,
      sequenceCornerPoly_eq_wordCornerPoly C hP Λ s hs t ht]

end Categorification.Stendhal
