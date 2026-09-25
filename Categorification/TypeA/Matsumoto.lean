/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.NormalForm

/-!
# Matsumoto's theorem for the symmetric group

Consequences of the normal form theorem `TypeA.braidEquiv_canWord_or_hasRepeat`: the word
problem for `Equiv.Perm (Fin m)` in terms of braid moves.

## Main results

* `TypeA.braidEquiv_of_isReduced` (**Matsumoto's theorem**): two reduced words representing
  the same permutation are related by braid moves.
* `TypeA.exists_braidEquiv_hasRepeat_of_not_isReduced`: a valid word that is not reduced is
  related by braid moves to a word with two equal adjacent letters.
* `TypeA.IsReduced.not_braidEquiv_hasRepeat`: a reduced word is not related by braid moves to
  any word with two equal adjacent letters.
* `TypeA.isReduced_iff_forall_braidEquiv_not_hasRepeat`: the two previous statements combined.

These are exactly the inputs used in the spanning half of the basis theorem of
Khovanov–Lauda, *A diagrammatic approach to categorification of quantum groups I*
(arXiv:0803.4121v2), Theorem 2.5.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

/-- Braid moves preserve reducedness. -/
theorem BraidEquiv.isReduced_iff {ρ σ : List ℕ} (h : BraidEquiv ρ σ) :
    IsReduced m ρ ↔ IsReduced m σ := by
  refine ⟨fun hr => ⟨h.validWord_iff.1 hr.1, ?_⟩, fun hr => ⟨h.validWord_iff.2 hr.1, ?_⟩⟩
  · rw [← h.length_eq, ← h.wordProd_eq hr.1, hr.2]
  · rw [h.length_eq, h.wordProd_eq (h.validWord_iff.2 hr.1), hr.2]

/-! ## Headline results -/

/-- A reduced word is not braid equivalent to any word with two equal adjacent letters. -/
theorem IsReduced.not_braidEquiv_hasRepeat {ρ σ : List ℕ} (hr : IsReduced m ρ)
    (h : BraidEquiv ρ σ) : ¬ HasRepeat σ :=
  fun hσ => hσ.not_isReduced (h.isReduced_iff.1 hr)

/-- A reduced word is braid equivalent to the canonical word of its permutation. -/
theorem IsReduced.braidEquiv_canWord {ρ : List ℕ} (hr : IsReduced m ρ) :
    BraidEquiv ρ (canWord m (wordProd m ρ)) := by
  rcases braidEquiv_canWord_or_hasRepeat hr.1 with h | ⟨σ, h, hσ⟩
  · exact h
  · exact absurd hσ (hr.not_braidEquiv_hasRepeat h)

/-- **Matsumoto's theorem** (type A). Two reduced words representing the same permutation are
related by braid moves (commutations of distant letters and braid relations). -/
theorem braidEquiv_of_isReduced {ρ σ : List ℕ} (hρ : IsReduced m ρ) (hσ : IsReduced m σ)
    (h : wordProd m ρ = wordProd m σ) : BraidEquiv ρ σ :=
  hρ.braidEquiv_canWord.trans (h ▸ hσ.braidEquiv_canWord.symm)

/-- A valid word which is not reduced is braid equivalent to a word with two equal adjacent
letters. -/
theorem exists_braidEquiv_hasRepeat_of_not_isReduced {ρ : List ℕ} (hv : ValidWord m ρ)
    (hr : ¬ IsReduced m ρ) : ∃ σ, BraidEquiv ρ σ ∧ HasRepeat σ := by
  rcases braidEquiv_canWord_or_hasRepeat hv with h | h
  · exact absurd ((h.isReduced_iff).2 (isReduced_canWord m _)) hr
  · exact h

/-- A valid word is reduced iff it is not braid equivalent to a word with two equal adjacent
letters. -/
theorem isReduced_iff_forall_braidEquiv_not_hasRepeat {ρ : List ℕ} (hv : ValidWord m ρ) :
    IsReduced m ρ ↔ ∀ σ, BraidEquiv ρ σ → ¬ HasRepeat σ := by
  refine ⟨fun hr _ h => hr.not_braidEquiv_hasRepeat h, fun h => ?_⟩
  by_contra hr
  obtain ⟨σ, hσ, hrep⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hv hr
  exact h σ hσ hrep

end Categorification.TypeA
