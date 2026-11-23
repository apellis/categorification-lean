/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidedStendhal

set_option backward.isDefEq.respectTransparency false

/-!
# The order of red strands under a permutation

Supporting combinatorics for Webster, arXiv:1309.3796v2, Lemma 6.5. The red labels of
`w • i`, read from left to right (`redWord`), only depend on the relative order in which `w`
places the red strands of `i` (`redWord_smul_eq_iff`). When the red labels of `i` read
`L ++ a :: b :: M`, those of `v • i` read `L ++ b :: a :: M` exactly when `v` inverts the
strands labelled `a` and `b` and no other pair of red strands (`redWord_smul_eq_swap_iff`), and
no red strand of `i` lies strictly between them (`not_lt_of_redWord_eq_append`).

## Main results

* `redWord_smul_eq_iff`: `redWord (w • i) = redWord (w' • i)` iff `w` and `w'` order the red
  strands of `i` in the same way.
* `redWord_smul_eq_swap_iff`: the red strands of `v • i` read `L ++ b :: a :: M` iff `v`
  inverts exactly the pair of red strands labelled `a` and `b`.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv

variable {I : Type*} {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card (stendhalWeight ℓ ν)

/-- Two members of a list that is pairwise for `R` and for `S` are related, in the same order,
by both. -/
theorem _root_.List.Pairwise.both {α : Type*} {R S : α → α → Prop} :
    ∀ {L : List α}, L.Pairwise R → L.Pairwise S → ∀ {a b : α}, a ∈ L → b ∈ L → a ≠ b →
      (R a b ∧ S a b) ∨ (R b a ∧ S b a)
  | [], _, _, _, _, ha, _, _ => by simp at ha
  | x :: L, hR, hS, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at hR hS
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hne
    · exact .inl ⟨hR.1 _ hb', hS.1 _ hb'⟩
    · exact .inr ⟨hR.1 _ ha', hS.1 _ ha'⟩
    · exact List.Pairwise.both hR.2 hS.2 ha' hb' hne

/-- Exchanging two adjacent entries of a list that is pairwise for an irreflexive relation. -/
theorem _root_.List.Pairwise.swap_adj {α : Type*} {R R' : α → α → Prop} {a b : α}
    (hirr : ∀ x, ¬ R x x) (hba : R' b a) (hR : ∀ x y, R x y → (x, y) ≠ (a, b) → R' x y) :
    ∀ {L M : List α}, (L ++ a :: b :: M).Pairwise R → (L ++ b :: a :: M).Pairwise R'
  | [], M, h => by
    simp only [List.nil_append, List.pairwise_cons, List.mem_cons] at h ⊢
    obtain ⟨hA, hB, hM⟩ := h
    refine ⟨fun y hy => ?_, fun y hy => ?_, hM.imp_of_mem fun {x y} hx _ h => hR x y h ?_⟩
    · rcases hy with rfl | hy
      · exact hba
      · exact hR _ _ (hB y hy) fun h' => by
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
          exact hirr _ (hA _ (.inr hy))
    · exact hR _ _ (hA y (.inr hy)) fun h' => by
        obtain ⟨-, rfl⟩ := Prod.mk.inj h'
        exact hirr _ (hB _ hy)
    · intro h'
      obtain ⟨rfl, -⟩ := Prod.mk.inj h'
      exact hirr _ (hA _ (.inr hx))
  | x :: L, M, h => by
    rw [List.cons_append, List.pairwise_cons] at h ⊢
    refine ⟨fun y hy => hR _ _ (h.1 y ?_) fun h' => ?_, List.Pairwise.swap_adj hirr hba hR h.2⟩
    · simp only [List.mem_append, List.mem_cons] at hy ⊢
      tauto
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
      exact hirr _ (h.1 _ (by simp))

/-- The relation "the strand labelled `r` lies left of the strand labelled `r'` after
applying `w`". -/
def RedBefore (i : Seq μ) (w : Perm (Fin m)) (r r' : Fin ℓ) : Prop :=
  ∀ s t, i.lbl s = .inr r → i.lbl t = .inr r' → w s < w t

theorem mem_redWord (j : Seq μ) (r : Fin ℓ) : r ∈ redWord j := by
  obtain ⟨a, ha⟩ := exists_lbl_eq_inr j r
  simp only [redWord, List.mem_filterMap, List.mem_finRange, true_and]
  exact ⟨a, by simp [ha]⟩

theorem redWord_nodup (j : Seq μ) : (redWord j).Nodup := by
  refine (List.nodup_finRange m).filterMap fun a a' r ha ha' => ?_
  rw [Option.mem_def, Sum.getRight?_eq_some_iff] at ha ha'
  exact lbl_inj_of_inr j r ha ha'

/-- The red labels of `w • i` are listed in the order in which `w` places them. -/
theorem redWord_pairwise (i : Seq μ) (w : Perm (Fin m)) :
    (redWord (w • i)).Pairwise (RedBefore i w) := by
  rw [redWord, List.pairwise_filterMap]
  refine (List.pairwise_lt_finRange m).imp fun {c c'} hcc' r hr r' hr' s t hs ht => ?_
  rw [Sum.getRight?_eq_some_iff, Seq.lbl, Seq.smul_apply] at hr hr'
  obtain rfl := lbl_inj_of_inr i r hs hr
  obtain rfl := lbl_inj_of_inr i r' ht hr'
  simpa using hcc'

theorem redWord_pairwise_one (i : Seq μ) :
    (redWord i).Pairwise (fun r r' => ∀ s t, i.lbl s = .inr r → i.lbl t = .inr r' → s < t) := by
  have h := redWord_pairwise i 1
  rw [one_smul] at h
  exact h.imp fun h' s t hs ht => by simpa using h' s t hs ht

/-- **The red labels of `w • i` only depend on how `w` orders the red strands of `i`.** -/
theorem redWord_smul_eq_iff (i : Seq μ) (w w' : Perm (Fin m)) :
    redWord (w • i) = redWord (w' • i) ↔ ∀ s t (r r' : Fin ℓ), i.lbl s = .inr r →
      i.lbl t = .inr r' → (w s < w t ↔ w' s < w' t) := by
  constructor
  · intro h s t r r' hs ht
    by_cases hst : s = t
    · subst hst; simp
    have hne : r ≠ r' := by
      rintro rfl
      exact hst (lbl_inj_of_inr i r hs ht)
    rcases (redWord_pairwise i w).both (h ▸ redWord_pairwise i w') (mem_redWord _ r)
      (mem_redWord _ r') hne with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact iff_of_true (h₁ s t hs ht) (h₂ s t hs ht)
    · exact iff_of_false (lt_asymm (h₁ t s ht hs)) (lt_asymm (h₂ t s ht hs))
  · intro h
    refine List.Perm.eq_of_pairwise (le := RedBefore i w) (fun r r' _ _ h₁ h₂ => ?_)
      (redWord_pairwise i w) ((redWord_pairwise i w').imp fun {r r'} h' s t hs ht =>
        (h s t r r' hs ht).2 (h' s t hs ht)) ?_
    · obtain ⟨s, hs⟩ := exists_lbl_eq_inr i r
      obtain ⟨t, ht⟩ := exists_lbl_eq_inr i r'
      exact absurd (h₂ t s ht hs) (lt_asymm (h₁ s t hs ht))
    · exact (List.perm_ext_iff_of_nodup (redWord_nodup _) (redWord_nodup _)).2 fun r => by
        simp [mem_redWord]

/-- No red strand lies strictly between two strands whose labels are adjacent in `redWord`. -/
theorem not_lt_of_redWord_eq_append {i : Seq μ} {L M : List (Fin ℓ)} {a b : Fin ℓ}
    (h : redWord i = L ++ a :: b :: M) {q p t : Fin m} (hq : i.lbl q = .inr a)
    (hp : i.lbl p = .inr b) (ht : (i.lbl t).isRight) (hqt : q < t) (htp : t < p) : False := by
  obtain ⟨r, hr⟩ : ∃ r, i.lbl t = .inr r := by
    rcases hl : i.lbl t with _ | r
    · simp [hl] at ht
    · exact ⟨r, rfl⟩
  have hP := redWord_pairwise_one i
  rw [h, List.pairwise_append, List.pairwise_cons, List.pairwise_cons] at hP
  have hmem := mem_redWord i r
  rw [h] at hmem
  simp only [List.mem_append, List.mem_cons] at hmem
  rcases hmem with hL | rfl | rfl | hM
  · exact absurd (hP.2.2 r hL a (by simp) t q hr hq) (not_lt.2 hqt.le)
  · exact absurd (lbl_inj_of_inr i _ hr hq) (ne_of_gt hqt)
  · exact absurd (lbl_inj_of_inr i _ hr hp) (ne_of_lt htp)
  · exact absurd (hP.2.1.2.1 r hM p t hp hr) (not_lt.2 htp.le)

/-- **The red labels of `v • i` are those of `i` with two adjacent labels exchanged** iff `v`
inverts the pair of red strands carrying them, and no other pair of red strands. -/
theorem redWord_smul_eq_swap_iff {i : Seq μ} {L M : List (Fin ℓ)} {a b : Fin ℓ}
    (h : redWord i = L ++ a :: b :: M) {q p : Fin m} (hq : i.lbl q = .inr a)
    (hp : i.lbl p = .inr b) (v : Perm (Fin m)) :
    redWord (v • i) = L ++ b :: a :: M ↔ ∀ s t, (i.lbl s).isRight → (i.lbl t).isRight →
      s < t → (v t < v s ↔ s = q ∧ t = p) := by
  have hP := redWord_pairwise_one i
  rw [h] at hP
  have hqp : q < p := by
    have := hP
    rw [List.pairwise_append, List.pairwise_cons] at this
    exact this.2.1.1 b (by simp) q p hq hp
  have hab : a ≠ b := by
    rintro rfl
    exact ne_of_lt hqp (lbl_inj_of_inr i a hq hp)
  have hperm : (L ++ b :: a :: M).Perm (L ++ a :: b :: M) := (List.Perm.swap a b M).append_left L
  have hred : ∀ s, (i.lbl s).isRight → ∃ r, i.lbl s = .inr r := fun s hs => by
    rcases hl : i.lbl s with _ | r
    · simp [hl] at hs
    · exact ⟨r, rfl⟩
  constructor
  · intro hv s t hs ht hst
    obtain ⟨r, hr⟩ := hred s hs
    obtain ⟨r', hr'⟩ := hred t ht
    have hne : r ≠ r' := by
      rintro rfl
      exact (ne_of_lt hst) (lbl_inj_of_inr i r hr hr')
    have hQ := redWord_pairwise i v
    rw [hv] at hQ
    have hQ' : (L ++ a :: b :: M).Pairwise
        (fun x y => RedBefore i v x y ∨ (x = a ∧ y = b)) :=
      hQ.swap_adj (a := b) (b := a) (R' := fun x y => RedBefore i v x y ∨ (x = a ∧ y = b))
        (fun x hx => by
          obtain ⟨s', hs'⟩ := exists_lbl_eq_inr i x
          exact lt_irrefl _ (hx s' s' hs' hs')) (.inr ⟨rfl, rfl⟩)
        (fun x y h _ => .inl h)
    constructor
    · intro hvts
      rcases hP.both hQ' (by rw [← h]; exact mem_redWord i r)
        (by rw [← h]; exact mem_redWord i r') hne with ⟨_, h₂ | ⟨rfl, rfl⟩⟩ | ⟨h₁, -⟩
      · exact absurd (h₂ s t hr hr') (lt_asymm hvts)
      · exact ⟨lbl_inj_of_inr i _ hr hq, lbl_inj_of_inr i _ hr' hp⟩
      · exact absurd (h₁ t s hr' hr) (not_lt.2 hst.le)
    · rintro ⟨rfl, rfl⟩
      have hQ'' := redWord_pairwise i v
      rw [hv, List.pairwise_append, List.pairwise_cons] at hQ''
      exact hQ''.2.1.1 a (by simp) t s hp hq
  · intro hv
    refine List.Perm.eq_of_pairwise (le := RedBefore i v) (fun r r' _ _ h₁ h₂ => ?_)
      (redWord_pairwise i v) (hP.swap_adj ?_ ?_ ?_) ?_
    · obtain ⟨s, hs⟩ := exists_lbl_eq_inr i r
      obtain ⟨t, ht⟩ := exists_lbl_eq_inr i r'
      exact absurd (h₂ t s ht hs) (lt_asymm (h₁ s t hs ht))
    · intro x hx
      obtain ⟨s', hs'⟩ := exists_lbl_eq_inr i x
      exact lt_irrefl _ (hx s' s' hs' hs')
    · intro s t hs ht
      rw [lbl_inj_of_inr i _ hs hp, lbl_inj_of_inr i _ ht hq]
      exact (hv q p (by simp [hq]) (by simp [hp]) hqp).2 ⟨rfl, rfl⟩
    · intro x y hxy hne s t hs ht
      have hst := hxy s t hs ht
      have h' := hv s t (by simp [hs]) (by simp [ht]) hst
      refine lt_of_le_of_ne (not_lt.1 fun hlt => hne ?_) (v.injective.ne (ne_of_lt hst))
      obtain ⟨rfl, rfl⟩ := h'.1 hlt
      rw [hs] at hq; rw [ht] at hp
      cases hq; cases hp; rfl
    · have hnd := redWord_nodup i
      rw [h] at hnd
      exact (List.perm_ext_iff_of_nodup (redWord_nodup _) (hperm.nodup_iff.2 hnd)).2 fun r => by
        rw [hperm.mem_iff, ← h]
        simp [mem_redWord]

end Categorification.Stendhal
