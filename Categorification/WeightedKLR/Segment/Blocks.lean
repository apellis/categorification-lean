/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Segment

/-!
# Reversing the blocks of a weakly sorted list

Let `κ` be a function to a linear order, and let `la`, `lb` be lists with the same elements,
both sorted by `κ` (with respect to strict orders `Ra`, `Rb` refining the preorder of `κ`), such
that on each level set of `κ` the order of `lb` is the reverse of the order of `la`. Then `lb` is
obtained from `la` by reversing the level sets one at a time, from the smallest value of `κ` up
(`Segment.reflTransGen_reverse_blocks`). At the moment a level set `B` with value `c` is
reversed, the part of the list before it consists exactly of the elements with `κ < c`.

This is the combinatorial part of the local analysis of an event in a family of segments: the
hyperplanes crossed at the same time at the event form a block whose order is reversed.
-/

namespace List

lemma eq_filter_append_filter {α : Type*} (P : α → Bool) :
    ∀ {l : List α}, l.Pairwise (fun x y => P y = true → P x = true) →
      l = l.filter P ++ l.filter (fun x => !P x)
  | [], _ => rfl
  | a :: t, h => by
    rw [pairwise_cons] at h
    by_cases ha : P a = true
    · simp only [filter_cons, ha, ite_true, Bool.not_true, Bool.false_eq_true, ite_false,
        cons_append]
      exact congrArg (a :: ·) (eq_filter_append_filter P h.2)
    · have hall : ∀ y ∈ t, P y = false := fun y hy => by
        by_contra hy'
        exact ha (h.1 y hy (by simpa using hy'))
      have h1 : t.filter P = [] := filter_eq_nil_iff.2 fun y hy => by simp [hall y hy]
      have h2 : t.filter (fun x => !P x) = t := filter_eq_self.2 fun y hy => by simp [hall y hy]
      simp only [Bool.not_eq_true] at ha
      simp [ha, h1, h2]

end List

namespace Categorification.WeightedKLR.Segment

variable {α K : Type*} [LinearOrder K]

/-- **Reversal of level sets.** If `la` and `lb` list the same elements, are sorted by `κ`, and
have opposite orders on each level set of `κ`, then `A ++ lb` is obtained from `A ++ la` by
reversing blocks: each block is a level set `{κ = c}` of at least two elements, preceded by the
elements with `κ < c`. -/
theorem reflTransGen_reverse_blocks (κ : α → K) (S : α → Prop)
    (Ra Rb : α → α → Prop) (hRa : ∀ x y, Ra x y → ¬Ra y x) (hRb : ∀ x y, Rb x y → ¬Rb y x)
    (hκa : ∀ x y, Ra x y → κ x ≤ κ y) (hκb : ∀ x y, Rb x y → κ x ≤ κ y)
    (hrev : ∀ x y, κ x = κ y → (Ra x y ↔ Rb y x))
    (R : List α → List α → Prop)
    (hR : ∀ (A B C : List α) (c : K), B.Nodup → 2 ≤ B.length → (∀ x, x ∈ A ↔ S x ∧ κ x < c) →
      (∀ x, x ∈ B ↔ S x ∧ κ x = c) → R (A ++ B ++ C) (A ++ B.reverse ++ C)) :
    ∀ (n : ℕ) (la lb A : List α), la.length ≤ n → la.Pairwise Ra → lb.Pairwise Rb →
      (∀ x, x ∈ la ↔ x ∈ lb) → (∀ x, x ∈ A ∨ x ∈ la ↔ S x) →
      (∀ x ∈ A, ∀ y ∈ la, κ x < κ y) → Relation.ReflTransGen R (A ++ la) (A ++ lb) := by
  classical
  intro n
  induction n with
  | zero =>
    intro la lb A hn _ _ hm _ _
    have : la = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hn)
    subst this
    have : lb = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by simpa using (hm x).2 hx
    subst this
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro la lb A hn ha hb hm hS hA
    rcases la with _ | ⟨a, t⟩
    · have : lb = [] := List.eq_nil_iff_forall_not_mem.2 fun x hx => by simpa using (hm x).2 hx
      subst this
      exact Relation.ReflTransGen.refl
    set la := a :: t with hla
    set c := κ a with hc
    have hmin : ∀ y ∈ la, c ≤ κ y := by
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_rfl
      · exact hκa _ _ (List.rel_of_pairwise_cons ha hy)
    have hminb : ∀ y ∈ lb, c ≤ κ y := fun y hy => hmin y ((hm y).2 hy)
    let P : α → Bool := fun x => decide (κ x = c)
    have hsplit : ∀ l : List α, (∀ y ∈ l, c ≤ κ y) → l.Pairwise (fun x y => κ x ≤ κ y) →
        l = l.filter P ++ l.filter (fun x => !P x) := fun l hl hp =>
      List.eq_filter_append_filter P <| hp.imp_of_mem fun {x y} hx _ hxy hy => by
        simp only [P, decide_eq_true_eq] at hy ⊢
        exact le_antisymm (hy ▸ hxy) (hl x hx)
    have hka : la.Pairwise (fun x y => κ x ≤ κ y) := ha.imp fun h => hκa _ _ h
    have hkb : lb.Pairwise (fun x y => κ x ≤ κ y) := hb.imp fun h => hκb _ _ h
    set B := la.filter P with hB
    set B' := lb.filter P with hB'
    set la' := la.filter (fun x => !P x) with hla'
    set lb' := lb.filter (fun x => !P x) with hlb'
    have ea : la = B ++ la' := hsplit la hmin hka
    have eb : lb = B' ++ lb' := hsplit lb hminb hkb
    have hmemB : ∀ x, x ∈ B ↔ x ∈ la ∧ κ x = c := fun x => by simp [hB, P]
    have hmemB' : ∀ x, x ∈ B' ↔ x ∈ la ∧ κ x = c := fun x => by simp [hB', P, hm x]
    have hBa : B.Pairwise Ra := ha.filter P
    -- the level set is reversed
    have hBrev : B' = B.reverse := by
      refine List.eq_of_pairwise_asymm hRb (hb.filter P) ?_ fun x => by
        rw [List.mem_reverse, hmemB, hmemB']
      rw [List.pairwise_reverse]
      refine hBa.imp_of_mem fun {x y} hx hy hxy => ?_
      exact (hrev x y (((hmemB x).1 hx).2.trans ((hmemB y).1 hy).2.symm)).1 hxy
    have haB : a ∈ B := (hmemB a).2 ⟨List.mem_cons_self, rfl⟩
    have hlen : la'.length ≤ n := by
      have : la.length = B.length + la'.length := by rw [← List.length_append, ← ea]
      have hB0 : 0 < B.length := List.length_pos_of_mem haB
      simp only [hla, List.length_cons] at this hn
      omega
    -- the elements before and in the block
    have hAmem : ∀ x, x ∈ A ↔ S x ∧ κ x < c := fun x => by
      constructor
      · intro hx
        exact ⟨(hS x).1 (Or.inl hx), hA x hx a List.mem_cons_self⟩
      · rintro ⟨hx, hlt⟩
        rcases (hS x).2 hx with hx | hx
        · exact hx
        · exact absurd (hmin x hx) (not_le.2 hlt)
    have hBmem : ∀ x, x ∈ B ↔ S x ∧ κ x = c := fun x => by
      rw [hmemB]
      constructor
      · rintro ⟨hx, e⟩; exact ⟨(hS x).1 (Or.inr hx), e⟩
      · rintro ⟨hx, e⟩
        rcases (hS x).2 hx with hx | hx
        · exact absurd (hA x hx a List.mem_cons_self) (by rw [e]; exact lt_irrefl _)
        · exact ⟨hx, e⟩
    have hfirst : Relation.ReflTransGen R (A ++ B ++ la') (A ++ B.reverse ++ la') := by
      by_cases h2 : 2 ≤ B.length
      · exact Relation.ReflTransGen.single
          (hR A B la' c (List.nodup_of_pairwise_asymm hRa hBa) h2 hAmem hBmem)
      · have : B.reverse = B := by
          rcases B with _ | ⟨b, _ | ⟨b', l⟩⟩
          · rfl
          · rfl
          · simp at h2
        rw [this]
    have hrest := ih la' lb' (A ++ B.reverse) hlen (ha.filter _) (hb.filter _)
      (fun x => by simp [hla', hlb', hm x])
      (fun x => by
        rw [List.mem_append, List.mem_reverse, or_assoc, ← List.mem_append, ← ea]
        exact hS x)
      (fun x hx y hy => by
        have hy' : y ∈ la ∧ ¬κ y = c := by simpa [hla', P] using hy
        rcases List.mem_append.1 hx with hx | hx
        · exact hA x hx y hy'.1
        · rw [List.mem_reverse, hmemB] at hx
          rw [hx.2]
          exact lt_of_le_of_ne (hmin y hy'.1) (Ne.symm hy'.2))
    have e1 : A ++ la = A ++ B ++ la' := by rw [List.append_assoc, ← ea]
    have e2 : A ++ lb = A ++ B.reverse ++ lb' := by rw [List.append_assoc, ← hBrev, ← eb]
    rw [e1, e2]
    exact hfirst.trans hrest

end Categorification.WeightedKLR.Segment
