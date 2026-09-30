/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Chord.Realisation

/-!
# Lettered states of chord diagrams

Complements to `StringDiagrams.Chord.Lettered`: for an involution `d` on the letters, the letter
condition is symmetric in the two ends of an arc, is preserved by every generating move, and
therefore holds for the state `run d D` of every diagram `D` fitting on the empty state
(`lettered_run`).
-/

namespace StringDiagrams.Chord

variable {α : Type*} {d : α → α}

theorem Lettered.symm' {s : List (ℕ × α)} (h : Lettered d s) (hd : Function.Involutive d) {i j : ℕ}
    (hij : Same s i j) : (s[j]?).map Prod.snd = (s[i]?).map (d ∘ Prod.snd) := by
  rcases lt_or_gt_of_ne hij.ne with hlt | hlt
  · exact h i j hij hlt
  · have := h j i hij.symm hlt
    have hi := hij.lt_left
    have hj := hij.lt_right
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at this ⊢
    simp at this ⊢
    rw [this, hd]

theorem Lettered.swapAt' {s : List (ℕ × α)} (h : Lettered d s) (hd : Function.Involutive d)
    {p : ℕ} (hp : p + 1 < s.length) : Lettered d (Chord.swapAt s p) := by
  intro i j hij _
  rw [same_swapAt hp] at hij
  rw [getElem?_swapAt s hp, getElem?_swapAt s hp]
  exact h.symm' hd hij

theorem Lettered.insAt {s : List (ℕ × α)} (h : Lettered d s) (hd : Function.Involutive d)
    {g : ℕ} (hg : g ≤ s.length) {k : ℕ} (hk : ∀ x ∈ s, x.1 ≠ k) (a : α) :
    Lettered d (Chord.insAt s g (k, a) (k, d a)) := by
  intro i j hij hlt
  rw [same_insAt_iff hg hk] at hij
  rw [getElem?_insAt s hg, getElem?_insAt s hg]
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4, h5⟩
  · simp
  · omega
  · have := h.symm' hd h5
    simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    split_ifs at this ⊢ <;> exact this

theorem Inv.lettered_step {s : List (ℕ × α)} (hs : Inv s) (hl : Lettered d s)
    (hd : Function.Involutive d) {m : Move α} (hm : m.Ok s.length) :
    Lettered d (Chord.step d s m) := by
  cases m with
  | cup g a => exact hl.insAt hd hm (fun x hx => (hs.2 x hx).ne) a
  | cross p => exact hl.swapAt' hd hm

/-- The states reached by diagrams are lettered (for an involution `d`). -/
theorem lettered_run (hd : Function.Involutive d) : ∀ {D : List (Move α)}, Fits 0 D →
    Lettered d (run d D) := by
  intro D
  induction D using List.reverseRecOn with
  | nil => intro _ i j hij; have := hij.lt_left; simp [run] at this
  | append_singleton D m ih =>
    intro h
    rw [fits_snoc (d := d)] at h
    rw [run_append]
    exact (inv_run h.1).lettered_step (ih h.1) hd h.2

end StringDiagrams.Chord
