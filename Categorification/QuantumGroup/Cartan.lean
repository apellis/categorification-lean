/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Cartan data

A *Cartan datum* (Lusztig, *Introduction to quantum groups*, §1.1.1) is a set `I` with a
symmetric bilinear form `ν, ν' ↦ ν · ν'` on `ℤ[I]` such that

* `i · i ∈ {2, 4, 6, …}` for `i ∈ I`, and
* `2 (i · j) / (i · i) ∈ {0, -1, -2, …}` for `i ≠ j` in `I`.

This is the setting of Khovanov–Lauda II (arXiv:0804.2080v1, §1.1 / §3). The simply-laced
case of Khovanov–Lauda I (arXiv:0803.4121v2, §1) is the Cartan datum of a graph `Γ`
without loops or multiple edges: `i · i = 2`, `i · j = -1` if `i` and `j` are joined by an
edge, and `i · j = 0` otherwise (`CartanDatum.ofGraph`).

The quantum-group constructions in `Categorification.QuantumGroup` take the pairing as a
bare function `dot : I → I → ℤ` together with exactly the hypotheses they use (usually only
symmetry), so they apply to any `CartanDatum` via `CartanDatum.dot`.
-/

namespace Categorification.QuantumGroup

/-- A Cartan datum `(I, ·)` in the sense of Lusztig 1.1.1, recorded by the values `i · j`. -/
structure CartanDatum (I : Type*) where
  /-- The values `i · j` of the symmetric bilinear form on the basis `I` of `ℤ[I]`. -/
  dot : I → I → ℤ
  symm : ∀ i j, dot i j = dot j i
  dot_self_pos : ∀ i, 0 < dot i i
  dot_self_even : ∀ i, Even (dot i i)
  dot_nonpos : ∀ i j, i ≠ j → dot i j ≤ 0
  /-- `2 (i · j) / (i · i)` is an integer. -/
  dvd_two_mul : ∀ i j, dot i i ∣ 2 * dot i j

namespace CartanDatum

variable {I : Type*}

/-- The simply-laced Cartan datum of a simple graph `Γ` (KL I §1):
`i · i = 2`, `i · j = -1` for an edge `i — j`, and `i · j = 0` otherwise. -/
def ofGraph [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj] : CartanDatum I where
  dot i j := if i = j then 2 else if Γ.Adj i j then -1 else 0
  symm i j := by
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
      by_cases hij : Γ.Adj i j
      · rw [if_pos hij, if_pos hij.symm]
      · rw [if_neg hij, if_neg (fun h' => hij h'.symm)]
  dot_self_pos i := by simp
  dot_self_even i := by simp
  dot_nonpos i j h := by
    rw [if_neg h]
    split_ifs <;> norm_num
  dvd_two_mul i j := by
    rw [if_pos rfl]
    exact dvd_mul_right 2 _

variable [DecidableEq I] (Γ : SimpleGraph I) [DecidableRel Γ.Adj]

@[simp] theorem ofGraph_dot_self (i : I) : (ofGraph Γ).dot i i = 2 := by simp [ofGraph]

theorem ofGraph_dot_of_adj {i j : I} (h : Γ.Adj i j) : (ofGraph Γ).dot i j = -1 := by
  simp [ofGraph, h.ne, h]

theorem ofGraph_dot_of_not_adj {i j : I} (hij : i ≠ j) (h : ¬ Γ.Adj i j) :
    (ofGraph Γ).dot i j = 0 := by
  simp [ofGraph, hij, h]

end CartanDatum

end Categorification.QuantumGroup
