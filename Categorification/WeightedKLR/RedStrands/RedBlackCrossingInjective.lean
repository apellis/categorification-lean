/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.IndLastStrandFirstFactor
import Categorification.KLR.CyclotomicB

set_option backward.isDefEq.respectTransparency false

/-!
# Pulling a red strand across a black strand is injective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v2,
Lemma 5.23 (base step). This file starts with the combinatorial input: when the second block
of the first-factor Mackey datum has a single strand, the crossing `ψ_d` is the single crossing
`ψ_{|ν₀|}`.

## Main results

* `TypeA.canWord_sadj`: the canonical word of an adjacent transposition `s_a` is `[a]`.
* `KLR.KLRAlgebra.firstψ_eq_ψ`: `ψ_d = ψ_{|ν₀|}` when `|ν'| = 1`.
-/

namespace Categorification.TypeA

open Equiv

/-- The code of the adjacent transposition `s_a` among codes of length `n`. -/
def singleCode : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, a => (if n = a then n else n + 1) :: singleCode n a

@[simp] theorem length_singleCode (n a : ℕ) : (singleCode n a).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [singleCode, ih]

theorem isCode_singleCode (n a : ℕ) : IsCode (singleCode n a) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine isCode_cons.2 ⟨?_, ih⟩
    simp only [length_singleCode]
    split_ifs <;> omega

theorem codeWord_singleCode (n a : ℕ) :
    codeWord (singleCode n a) = if a < n then [a] else [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [singleCode, codeWord_cons, ih, length_singleCode]
    by_cases h : n = a
    · subst h
      rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _), ite_eq_left (Nat.lt_succ_self _),
        show n + 1 - n = 1 by omega, descRun_one, List.nil_append]
    · rw [ite_eq_right h, Nat.sub_self, descRun_zero, List.append_nil]
      by_cases h' : a < n
      · rw [ite_eq_left h', ite_eq_left (by omega)]
      · rw [ite_eq_right h', ite_eq_right (by omega)]

/-- The canonical word of the adjacent transposition `s_a` of `Fin m`, `a + 1 < m`, is `[a]`. -/
theorem canWord_sadj {m a : ℕ} (ha : a + 1 < m) : canWord m (sadj m a) = [a] := by
  have hc := codeWord_singleCode (m - 1) a
  rw [ite_eq_left (by omega)] at hc
  rw [← wordProd_singleton, ← hc,
    canWord_wordProd_codeWord (isCode_singleCode _ a) (by simp)]

end Categorification.TypeA

namespace Categorification.KLR.KLRAlgebra

open TypeA Equiv

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

local notation "Si" i:max => (Singleton.singleton i : Multiset I)

omit [DecidableEq I] in
/-- When `ν'` has a single strand, the minimal double coset representative of the first-factor
Mackey datum is the adjacent transposition `s_{|ν₀|}`. -/
theorem quadPerm_firstQuad_eq_sadj (ν₀ ν' : Multiset I) (i : I) (h1 : Multiset.card ν' = 1) :
    quadPerm (firstQuad_h ν₀ ν' i) (firstQuad ν₀ ν' i) =
      sadj (Multiset.card (ν₀ + ν' + Si i)) (Multiset.card ν₀) := by
  ext p
  rw [quadPerm_val, sadj_val]
  have hp := p.isLt
  simp only [Multiset.card_add, Multiset.card_singleton, h1, swapNat] at hp ⊢
  split_ifs <;> omega

variable (Q) in
/-- **The first-factor crossing is a single crossing.** When `|ν'| = 1`, `ψ_d = ψ_{|ν₀|}`. -/
theorem firstψ_eq_ψ (ν₀ ν' : Multiset I) (i : I) (h1 : Multiset.card ν' = 1) :
    firstψ Q ν₀ ν' i = ψ (Multiset.card ν₀) := by
  rw [firstψ, quadPerm_firstQuad_eq_sadj ν₀ ν' i h1,
    canWord_sadj (by simp only [Multiset.card_add, Multiset.card_singleton, h1]; omega)]
  simp

end Categorification.KLR.KLRAlgebra
