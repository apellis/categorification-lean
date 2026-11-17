/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.RedStrands.Stendhal

/-! # Red order under an adjacent black crossing -/

namespace Categorification.Stendhal

open Equiv

variable {I : Type*} {ℓ : ℕ} {ν : Multiset I}
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

set_option linter.unusedSimpArgs false in
/-- Exchanging two neighbouring strands, one of them black, keeps the red strands in order. -/
theorem isRedOrdered_sadj {i : KLR.Seq (stendhalWeight ℓ ν)} (hi : IsRedOrdered i) {n : ℕ}
    (h : n + 1 < m) (hb : (i.1 ⟨n, by omega⟩).isLeft ∨ (i.1 ⟨n + 1, h⟩).isLeft) :
    IsRedOrdered (TypeA.sadj m n • i) := by
  have hs : TypeA.sadj m n = swap ⟨n, by omega⟩ ⟨n + 1, h⟩ := by
    simp only [TypeA.sadj, h, ↓reduceDIte]
  have hs' : (TypeA.sadj m n).symm = TypeA.sadj m n := by
    rw [← Perm.inv_def]
    exact inv_eq_of_mul_eq_one_left (TypeA.sadj_mul_self m n)
  intro a b r r' hab ha hb'
  simp only [KLR.Seq.lbl, KLR.Seq.smul_apply] at ha hb'
  rw [hs', hs] at ha hb'
  have key : swap (⟨n, by omega⟩ : Fin m) ⟨n + 1, h⟩ a < swap ⟨n, by omega⟩ ⟨n + 1, h⟩ b ∨
      (a = ⟨n, by omega⟩ ∧ b = ⟨n + 1, h⟩) := by
    rw [Fin.lt_def] at hab
    simp only [swap_apply_def, Fin.lt_def, Fin.ext_iff]
    split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> omega
  rcases key with key | ⟨h1, h2⟩
  · exact hi _ _ r r' key ha hb'
  · rw [h1, swap_apply_left] at ha
    rw [h2, swap_apply_right] at hb'
    rcases hb with hb | hb
    · rw [hb'] at hb; simp at hb
    · rw [ha] at hb; simp at hb

end Categorification.Stendhal
