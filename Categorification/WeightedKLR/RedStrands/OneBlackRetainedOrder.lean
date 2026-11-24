/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.AdjacentBlockRoot

/-!
# Retained dominance for a single black strand

Webster, arXiv:1309.3796v2, §6.1, proof of Lemma 6.8 at (6.21).
In one-black content, a retained cut records the position of the black strand.
The second red of the adjacent pair contributes no additional boundary test.
-/

namespace Categorification.Stendhal

open KLR BraidedStendhalAlgebra

variable {I : Type*} [DecidableEq I] {ℓ : ℕ} {i : I}
local notation "μ" => stendhalWeight ℓ (Singleton.singleton i : Multiset I)
local notation "m" => Multiset.card μ

omit [DecidableEq I] in
private theorem oneBlack_lbl_injective (s : Seq μ) : Function.Injective s.lbl := by
  classical
  have hnodup : (Finset.univ.val.map s.lbl).Nodup := by
    rw [show Finset.univ.val.map s.lbl = μ from s.2]
    simp [stendhalWeight, List.nodup_ofFn, Sum.inr_injective]
  exact fun a b h => Multiset.inj_on_of_nodup_map hnodup a (by simp) b (by simp) h

omit [DecidableEq I] in
private theorem oneBlack_colour (s : Seq μ) {x : Fin m} {j : I}
    (hx : s.lbl x = .inl j) : j = i := by
  have h : (Sum.inl j : I ⊕ Fin ℓ) ∈ μ := by
    rw [← show Finset.univ.val.map s.lbl = μ from s.2, Multiset.mem_map]
    exact ⟨x, by simp, hx⟩
  simpa [stendhalWeight] using h

/-- In a one-black loading each retained cut records whether the unique black
position lies before every red of the block. -/
theorem blockBlackCount_oneBlack (s : Seq μ) (x : Fin m) (hx : s.lbl x = .inl i)
    (C : Finset (Fin ℓ)) (j : I) :
    blockBlackCount s C j =
      if j = i ∧ (∀ y r, r ∈ C → s.lbl y = .inr r → x < y) then 1 else 0 := by
  classical
  rw [blockBlackCount]
  split_ifs with h
  · have hfilter : (Finset.univ.filter fun z => s.lbl z = .inl j ∧
        ∀ y r, r ∈ C → s.lbl y = .inr r → z < y) = {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hz
        exact oneBlack_lbl_injective s (hz.1.trans (h.1 ▸ hx.symm))
      · rintro rfl
        exact ⟨h.1.symm ▸ hx, h.2⟩
    rw [hfilter, Finset.card_singleton]
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hj := oneBlack_colour s hz.1
    have hlabel : s.lbl x = .inl j := by rw [hj]; exact hx
    have hzx := oneBlack_lbl_injective s (hz.1.trans hlabel.symm)
    subst z
    exact h ⟨hj, hz.2⟩

/-- A singleton red cut in one-black content is read off from its two positions. -/
theorem blackCount_oneBlack_at (s : Seq μ) (x y : Fin m)
    (hx : s.lbl x = .inl i) {r : Fin ℓ} (hy : s.lbl y = .inr r) (j : I) :
    blackCount s r j = if j = i ∧ x < y then 1 else 0 := by
  rw [← blockBlackCount_singleton, blockBlackCount_oneBlack s x hx]
  have hh : (∀ z a, a ∈ ({r} : Finset (Fin ℓ)) → s.lbl z = .inr a → x < z) ↔ x < y := by
    refine ⟨fun h => h y r (by simp) hy, ?_⟩
    intro h z a ha hz
    obtain rfl := Finset.mem_singleton.mp ha
    exact (oneBlack_lbl_injective s (hy.trans hz.symm)) ▸ h
  simp only [hh]

/-- The first red of the pair carries the retained count for that boundary. -/
theorem adjacentBlockRoot_of_ne_second {s : Seq μ} {a b r : Fin ℓ} {L M : List (Fin ℓ)}
    (ho : redWord s = L ++ a :: b :: M) (hr : r ≠ b) :
    adjacentBlockRoot a b s r = blackCount s r := by
  by_cases ha : r = a
  · subst r
    have hab : a ≠ b := hr
    rw [← adjacentBlockRoot_pair ho]
    simp only [adjacentBlockRoot, or_true, true_or, ite_true]
  · funext j
    simp [adjacentBlockRoot, ha, hr, blockBlackCount_singleton]

/-- Retained-boundary dominance in one-black content is inclusion of the retained
reds that follow the unique black strand. -/
theorem adjacentBlockRoot_oneBlack_le_iff {s t : Seq μ} {a b : Fin ℓ}
    {L M : List (Fin ℓ)} (hs : redWord s = L ++ a :: b :: M)
    (ht : redWord t = L ++ a :: b :: M)
    (xs xt : Fin m) (hxs : s.lbl xs = .inl i) (hxt : t.lbl xt = .inl i) :
    adjacentBlockRoot a b s ≤ adjacentBlockRoot a b t ↔
      ∀ r : Fin ℓ, r ≠ b → ∀ ps pt, s.lbl ps = .inr r → t.lbl pt = .inr r →
        xs < ps → xt < pt := by
  have coordinate (r : Fin ℓ) (hr : r ≠ b) (ps pt : Fin m)
      (hps : s.lbl ps = .inr r) (hpt : t.lbl pt = .inr r) (j : I) :
      adjacentBlockRoot a b s r j ≤ adjacentBlockRoot a b t r j ↔
        (j = i ∧ xs < ps) → xt < pt := by
    rw [adjacentBlockRoot_of_ne_second hs hr, adjacentBlockRoot_of_ne_second ht hr,
      blackCount_oneBlack_at s xs ps hxs hps, blackCount_oneBlack_at t xt pt hxt hpt]
    by_cases hj : j = i <;> by_cases hx : xs < ps <;> by_cases hy : xt < pt <;>
      simp [hj, hx, hy]
  constructor
  · intro h r hr ps pt hps hpt hx
    exact (coordinate r hr ps pt hps hpt i).1 (h r i) ⟨rfl, hx⟩
  · intro h r j
    by_cases hr : r = b
    · subst r
      have hab : a ≠ b := by
        have hn := redWord_nodup s
        rw [hs] at hn
        exact fun he => by
          subst b
          have htail := (List.nodup_append.mp hn).2.1
          simp at htail
      obtain ⟨ps, hps⟩ := exists_lbl_eq_inr s a
      obtain ⟨pt, hpt⟩ := exists_lbl_eq_inr t a
      have hc := (coordinate a hab ps pt hps hpt j).2 (fun hxs => h a hab ps pt hps hpt hxs.2)
      rw [adjacentBlockRoot_of_ne_second hs hab, adjacentBlockRoot_of_ne_second ht hab] at hc
      simpa only [adjacentBlockRoot_pair hs, adjacentBlockRoot_pair ht] using hc
    · obtain ⟨ps, hps⟩ := exists_lbl_eq_inr s r
      obtain ⟨pt, hpt⟩ := exists_lbl_eq_inr t r
      exact (coordinate r hr ps pt hps hpt j).2 (fun hxs => h r hr ps pt hps hpt hxs.2)

/-- The omitted internal cut does not distinguish one-black loadings with the
same side of every retained boundary. -/
theorem adjacentBlockRoot_oneBlack_eq_iff {s t : Seq μ} {a b : Fin ℓ}
    {L M : List (Fin ℓ)} (hs : redWord s = L ++ a :: b :: M)
    (ht : redWord t = L ++ a :: b :: M)
    (xs xt : Fin m) (hxs : s.lbl xs = .inl i) (hxt : t.lbl xt = .inl i) :
    adjacentBlockRoot a b s = adjacentBlockRoot a b t ↔
      ∀ r : Fin ℓ, r ≠ b → ∀ ps pt, s.lbl ps = .inr r → t.lbl pt = .inr r →
        (xs < ps ↔ xt < pt) := by
  constructor
  · intro h r hr ps pt hps hpt
    exact ⟨(adjacentBlockRoot_oneBlack_le_iff hs ht xs xt hxs hxt).1 h.le r hr ps pt hps hpt,
      (adjacentBlockRoot_oneBlack_le_iff ht hs xt xs hxt hxs).1 h.ge r hr pt ps hpt hps⟩
  · intro h
    exact le_antisymm
      ((adjacentBlockRoot_oneBlack_le_iff hs ht xs xt hxs hxt).2
        fun r hr ps pt hps hpt => (h r hr ps pt hps hpt).1)
      ((adjacentBlockRoot_oneBlack_le_iff ht hs xt xs hxt hxs).2
        fun r hr pt ps hpt hps => (h r hr ps pt hps hpt).2)

/-- Strict retained dominance requires a retained red separating the two one-black
loadings, in addition to weak retained dominance. -/
theorem adjacentBlockRoot_oneBlack_lt_iff {s t : Seq μ} {a b : Fin ℓ}
    {L M : List (Fin ℓ)} (hs : redWord s = L ++ a :: b :: M)
    (ht : redWord t = L ++ a :: b :: M)
    (xs xt : Fin m) (hxs : s.lbl xs = .inl i) (hxt : t.lbl xt = .inl i) :
    adjacentBlockRoot a b s < adjacentBlockRoot a b t ↔
      adjacentBlockRoot a b s ≤ adjacentBlockRoot a b t ∧
        ∃ (r : Fin ℓ) (ps pt : Fin m), r ≠ b ∧ s.lbl ps = .inr r ∧ t.lbl pt = .inr r ∧
          ps ≤ xs ∧ xt < pt := by
  rw [lt_iff_le_not_ge, adjacentBlockRoot_oneBlack_le_iff ht hs xt xs hxt hxs]
  constructor
  · rintro ⟨hle, hno⟩
    classical
    push Not at hno
    obtain ⟨r, hr, pt, ps, hpt, hps, hp, hsep⟩ := hno
    exact ⟨hle, r, ps, pt, hr, hps, hpt, hsep, hp⟩
  · rintro ⟨hle, r, ps, pt, hr, hps, hpt, hsep, hp⟩
    exact ⟨hle, fun h => (not_lt_of_ge hsep) (h r hr pt ps hpt hps hp)⟩

end Categorification.Stendhal
