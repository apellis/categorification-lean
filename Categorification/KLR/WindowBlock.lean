/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Concat

/-!
# Blocks of consecutive positions cut out by a set of sequences

Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, puts diagrams next to each other. The block
embeddings `KLRAlgebra.BlockEmb` of `Categorification.KLR.Concat` express this for a block of
consecutive positions of `ν`. This file gives the block embedding attached to a window
`o, …, o + card μ - 1` of positions and a set `T` of sequences of weight `ν` whose labels on the
window always form a sequence of weight `μ` and which is stable under the adjacent
transpositions inside the window.

## Main definitions

* `KLRAlgebra.BlockEmb.window`: the block embedding of the window.
-/

namespace Categorification.KLR

open Equiv TypeA

variable {I : Type*}

namespace KLRAlgebra

variable {μ ν : Multiset I}

local notation "n₀" => Multiset.card μ
local notation "M" => Multiset.card ν

/-- The position `o + a` of `ν`. -/
def windowPos (o : ℕ) (ho : o + n₀ ≤ M) (a : Fin n₀) : Fin M := ⟨o + a, by omega⟩

/-- The labels of `s` on the window, as a sequence of weight `μ`. -/
def windowSeq (o : ℕ) (ho : o + n₀ ≤ M) (s : Seq ν)
    (hs : Finset.univ.val.map (fun a => s.1 (windowPos o ho a)) = μ) : Seq μ :=
  ⟨fun a => s.1 (windowPos o ho a), hs⟩

theorem sadj_windowPos (o : ℕ) (ho : o + n₀ ≤ M) {j : ℕ} (hj : j + 1 < n₀) (a : Fin n₀) :
    sadj M (o + j) (windowPos o ho a) = windowPos o ho (sadj n₀ j a) := by
  ext
  rw [sadj_val_of_lt (by omega), windowPos, windowPos]
  simp only
  rw [sadj_val_of_lt hj]
  unfold swapNat
  split_ifs <;> omega

/-- **The block embedding of a window** of positions `o, …, o + card μ - 1` of `ν`, for a set
`T` of sequences whose labels on the window have weight `μ` and which is stable under the
adjacent transpositions inside the window. The fibre over `i ∈ Seq μ` consists of the elements
of `T` with labels `i` on the window. -/
noncomputable def BlockEmb.window [DecidableEq I] (T : Finset (Seq ν)) (o : ℕ)
    (ho : o + n₀ ≤ M)
    (hT : ∀ s ∈ T, Finset.univ.val.map (fun a => s.1 (windowPos o ho a)) = μ)
    (hstab : ∀ j, j + 1 < n₀ → ∀ s, s ∈ T ↔ sadj M (o + j) • s ∈ T) :
    BlockEmb μ ν T where
  o := o
  pos := windowPos o ho
  pos_val _ := rfl
  F i := T.filter fun s => ∀ a, s.1 (windowPos o ho a) = i.1 a
  disj i i' h := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [Finset.mem_filter] at hs hs'
    exact h (Subtype.ext (funext fun a => (hs.2 a).symm.trans (hs'.2 a)))
  mem_T s := by
    constructor
    · intro hs
      exact ⟨windowSeq o ho s (hT s hs), Finset.mem_filter.2 ⟨hs, fun _ => rfl⟩⟩
    · rintro ⟨i, hi⟩
      exact (Finset.mem_filter.1 hi).1
  lbl i s hs a := (Finset.mem_filter.1 hs).2 a
  sadj_mem j hj i s := by
    simp only [Finset.mem_filter]
    rw [← hstab j hj s]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h a
      rw [sadj_smul_apply, sadj_windowPos o ho hj, h, sadj_smul_apply, TypeA.sadj_sadj_apply]
    · intro h a
      rw [sadj_smul_apply, ← h, sadj_smul_apply, sadj_windowPos o ho hj, TypeA.sadj_sadj_apply]

end KLRAlgebra

end Categorification.KLR
