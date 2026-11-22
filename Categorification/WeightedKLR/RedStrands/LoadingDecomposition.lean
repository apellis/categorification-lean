/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.ParabolicStandardProjectiveFiltration
import Categorification.WeightedKLR.RedStrands.TensorHomInduction

/-!
# Decomposition of red-ordered loadings at the last red strand

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2, the
induction in the proof of Proposition 5.20. Every red-ordered loading of
`T^λ_ν` with `ℓ + 1` red strands has the form `(s, λ_{ℓ+1}, w)`: a red-ordered loading `s` of
the first `ℓ` red strands, the last red strand, and a word `w` of black strands to its right.

## Main results

* `exists_blackWordLoading_appendRed`: the decomposition `s = (s₀, λ_{ℓ+1}, w)`, up to the
  transport of loadings along `wordWt w (θ + 0) = ν`.
-/

noncomputable section

namespace Categorification.Stendhal

open KLR

variable {I : Type} {ℓ : ℕ}

private theorem cast_appendRedLoading {a b : Multiset I} (h : a = b)
    (u : Seq (stendhalWeight ℓ b)) :
    Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h)
      (appendRedLoading (Seq.cast (congrArg (stendhalWeight ℓ) h.symm) u)) =
        appendRedLoading u := by
  subst h
  rfl

/-- **Decomposition of red-ordered loadings at the last red strand** (Webster,
arXiv:1309.3796v2, the induction in the proof of Proposition 5.20): every
red-ordered loading of `T^λ_ν` with `ℓ + 1` red strands is `(s₀, λ_{ℓ+1}, w)`, the last red
strand appended to a red-ordered loading `s₀` of the first `ℓ` red strands, followed by a word
`w` of black strands. -/
theorem exists_blackWordLoading_appendRed (n : ℕ) :
    ∀ (ν : Multiset I), ν.card = n → ∀ (s : Seq (stendhalWeight (ℓ + 1) ν)),
      IsRedOrdered s →
      ∃ (θ : Multiset I) (w : List I) (s₀ : Seq (stendhalWeight ℓ (θ + 0)))
        (_ : IsRedOrdered s₀) (h : wordWt w (θ + 0) = ν),
        Seq.cast (congrArg (stendhalWeight (ℓ + 1)) h)
          (blackWordLoading w (appendRedLoading s₀)) = s := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro ν hn s hs
    have hpos : 0 < (ℓ + 1) + ν.card := by omega
    cases hsEnd : s.lbl (FirstWeight.terminalPos hpos) with
    | inl i =>
      have hmem := s.mem (FirstWeight.terminalPos hpos)
      change s.lbl (FirstWeight.terminalPos hpos) ∈ stendhalWeight (ℓ + 1) ν at hmem
      rw [hsEnd] at hmem
      have hi : i ∈ ν := by simpa [stendhalWeight] using hmem
      obtain ⟨β, hβ⟩ := Multiset.exists_cons_of_mem hi
      rw [← Multiset.singleton_add] at hβ
      subst ν
      obtain ⟨u, hu, he⟩ := FirstWeight.exists_appendBlack_terminal s hsEnd hs
      subst s
      have hsmall : β.card < n := by
        simp only [Multiset.card_add, Multiset.card_singleton] at hn
        omega
      obtain ⟨θ, w, s₀, hs₀, h, hc⟩ := ih β.card hsmall β rfl u hu
      subst h
      subst hc
      exact ⟨θ, i :: w, s₀, hs₀, rfl, rfl⟩
    | inr r =>
      have hp : FirstWeight.terminalPos hpos = lastRedPosition ℓ ν := by
        apply Fin.ext
        change (stendhalWeight (ℓ + 1) ν).card - 1 = ν.card + ℓ
        rw [FirstWeight.cardinal_weight]
        omega
      have hsr := FirstWeight.terminal_red_last s hs r (by simpa only [hp] using hsEnd)
      obtain ⟨⟨u, hu⟩, he⟩ := (appendRedOrderedEquiv (ℓ := ℓ) (ν := ν)).surjective ⟨s, hs, hsr⟩
      have hes : appendRedLoading u = s := congrArg Subtype.val he
      subst s
      exact ⟨ν, [], Seq.cast (congrArg (stendhalWeight ℓ) (add_zero ν).symm) u,
        (isRedOrdered_cast _ u).2 hu, add_zero ν, cast_appendRedLoading (add_zero ν) u⟩

end Categorification.Stendhal
