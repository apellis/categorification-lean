/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Inserting a black letter at the end of a block of a word

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §5.1 and
Proposition 5.5. In a word in black letters `I` and red letters `Fin n`, block `k` consists of
the black letters between the red letters `λ_{k-1}` and `λ_k`. `blockInsertList i k L` inserts
the black letter `i` at the right end of block `k`: just before the first red letter of index at
least `k`, or at the end (`insertBefore`).

## Main definitions

* `insertBefore`: insert an element before the first one satisfying a predicate.
* `redAtLeast`, `blockInsertList`.
-/

namespace Categorification.Stendhal

section Lists

variable {α β : Type*}

/-- Insert `x` immediately before the first element satisfying `p`, or at the end if there is
none. -/
def insertBefore (p : α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: L => if p y then x :: y :: L else y :: insertBefore p x L

theorem insertBefore_perm (p : α → Bool) (x : α) :
    ∀ L : List α, (insertBefore p x L).Perm (x :: L)
  | [] => List.Perm.refl _
  | y :: L => by
    rw [insertBefore]
    split_ifs
    · exact List.Perm.refl _
    · exact ((insertBefore_perm p x L).cons y).trans (List.Perm.swap x y L)

theorem insertBefore_of_forall (p : α → Bool) (x : α) :
    ∀ L : List α, (∀ y ∈ L, p y = false) → insertBefore p x L = L ++ [x]
  | [], _ => rfl
  | y :: L, h => by
    simp only [insertBefore, h y List.mem_cons_self, Bool.false_eq_true, ite_false]
    rw [insertBefore_of_forall p x L fun z hz => h z (List.mem_cons_of_mem _ hz)]
    rfl

theorem insertBefore_append_of_exists (p : α → Bool) (x : α) (B : List α) :
    ∀ A : List α, (∃ y ∈ A, p y = true) → insertBefore p x (A ++ B) = insertBefore p x A ++ B
  | [], h => by simp at h
  | y :: A, h => by
    simp only [List.cons_append, insertBefore]
    split_ifs with hy
    · rfl
    · have h' : ∃ z ∈ A, p z = true := by
        obtain ⟨z, hz, hpz⟩ := h
        rcases List.mem_cons.1 hz with rfl | hz
        · exact absurd hpz hy
        · exact ⟨z, hz, hpz⟩
      rw [insertBefore_append_of_exists p x B A h', List.cons_append]

theorem insertBefore_append_of_forall (p : α → Bool) (x : α) (B : List α) :
    ∀ A : List α, (∀ y ∈ A, p y = false) → insertBefore p x (A ++ B) = A ++ insertBefore p x B
  | [], _ => rfl
  | y :: A, h => by
    simp only [List.cons_append, insertBefore, h y List.mem_cons_self, Bool.false_eq_true,
      ite_false]
    rw [insertBefore_append_of_forall p x B A fun z hz => h z (List.mem_cons_of_mem _ hz)]

theorem insertBefore_map (f : α → β) (p : β → Bool) (x : α) :
    ∀ L : List α, insertBefore p (f x) (L.map f) = (insertBefore (p ∘ f) x L).map f
  | [] => rfl
  | y :: L => by
    simp only [List.map_cons, insertBefore, Function.comp_apply]
    split_ifs
    · rfl
    · rw [insertBefore_map f p x L, List.map_cons]

theorem filterMap_insertBefore (p : α → Bool) (x : α) (g : α → Option β) (hx : g x = none) :
    ∀ L : List α, (insertBefore p x L).filterMap g = L.filterMap g
  | [] => by simp [insertBefore, hx]
  | y :: L => by
    simp only [insertBefore]
    split_ifs
    · simp [List.filterMap_cons, hx]
    · rw [List.filterMap_cons, List.filterMap_cons, filterMap_insertBefore p x g hx L]

end Lists

variable {I : Type*} {n : ℕ}

/-- The strands of block index at least `k`: red strands `r` with `k ≤ r`. Inserting before the
first such strand puts the new strand at the right end of block `k`. -/
def redAtLeast (k : ℕ) : I ⊕ Fin n → Bool
  | .inl _ => false
  | .inr r => decide (k ≤ r.val)

/-- The word of `t^{(k)}`: the word of `t` with the black letter `i` at the end of block `k`. -/
def blockInsertList (i : I) (k : ℕ) (L : List (I ⊕ Fin n)) : List (I ⊕ Fin n) :=
  insertBefore (redAtLeast k) (.inl i) L

end Categorification.Stendhal
