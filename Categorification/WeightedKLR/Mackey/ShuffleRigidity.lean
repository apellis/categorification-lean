/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.TypeShuffle
import Categorification.WeightedKLR.Mackey.Dominance

/-!
# Rigidity of the four-block shuffle

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). Let `B` be a four-block chamber for `X` and `Z`, and let
`T = shuffleTop Z B` be the chamber in which the strands of `Z` are moved to the left. The
gallery from `B` to `T` acts in the polynomial representation through relabellings `x` dominated
by `T` (`isSupported_opList_isDominated`). Among these, the identity is the only one that sends,
at every colour, at least as many strands outside `X` into `Z` as the identity does
(`IsDominated.eq_one_of_isFourBlock`). So every relabelling other than the identity occurring in
the shuffle has strictly smaller shuffle type at some colour: this is the statement that the
leading term of the four-block shuffle element is its only term of top type.

Within one colour `T` puts the strands of `Z` first and orders each of the two parts by rank
(`FullChamber.StrandLt.of_shuffleTop`). Dominance tested on initial segments of `T` then forces
a dominated relabelling not to lower the rank of a strand sent into `Z`, and, once `Z` is fixed,
not to lower the rank of any strand. A counting argument (`Finset.eq_and_forall_eq_of_rank_le`)
turns these inequalities into equalities.

## Main results

* `FullChamber.StrandLt.of_shuffleTop`: the order of the strands in `shuffleTop Z B`.
* `IsDominated.eq_one_of_isFourBlock`: a relabelling dominated by `shuffleTop Z B` that sends at
  least as many strands outside `X` into `Z`, at every colour, is the identity.
-/

namespace Categorification.WeightedKLR

open FullChamber

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-- **A counting lemma.** Let `f` map `S` injectively into `Q`, where `S, Q ⊆ A`, `Q` has at most
as many elements as `S`, `Q` is closed downwards in `A` for a function `r` injective on `A`, and
`f` does not lower `r`. Then `S = Q` and `f` is the identity on `S`. -/
theorem Finset.eq_and_forall_eq_of_rank_le {α : Type*} [DecidableEq α] {A S Q : Finset α}
    (r : α → ℕ) (hr : Set.InjOn r A) (hS : S ⊆ A) (hQ : Q ⊆ A)
    (hdown : ∀ a ∈ A, ∀ q ∈ Q, r a ≤ r q → a ∈ Q) (f : α → α) (hf : Set.InjOn f S)
    (hfS : ∀ t ∈ S, f t ∈ Q) (hcard : Q.card ≤ S.card) (hle : ∀ t ∈ S, r t ≤ r (f t)) :
    S = Q ∧ ∀ t ∈ S, f t = t := by
  have himg : S.image f = Q := by
    refine Finset.eq_of_subset_of_card_le (fun q hq => ?_) ?_
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
      exact hfS t ht
    · rw [Finset.card_image_of_injOn hf]
      exact hcard
  have hSQ : S = Q := Finset.eq_of_subset_of_card_le
    (fun t ht => hdown t (hS ht) (f t) (hfS t ht) (hle t ht)) hcard
  refine ⟨hSQ, ?_⟩
  have hsum : ∑ t ∈ S, r t = ∑ t ∈ S, r (f t) := by
    rw [← Finset.sum_image (f := r) hf, himg, hSQ]
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 hsum
  exact fun t ht => (hr (hS ht) (hQ (hfS t ht)) (heq t ht)).symm

namespace FullChamber

omit [DecidableEq I] in
/-- **The order of the strands in `shuffleTop Z B`.** For `B` rank-ordered, a strand is to the
left of another of the same colour in `shuffleTop Z B` only if it lies in `Z` and the other does
not, or both lie on the same side of `Z` and the first has smaller rank. -/
theorem StrandLt.of_shuffleTop {Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : B.IsRankOrdered) {s t : Strand ν} (h : (shuffleTop Z B).StrandLt s t) :
    s.1 = t.1 ∧ ((Z s = true ∧ Z t = false) ∨ (Z s = Z t ∧ s.2.val < t.2.val)) := by
  refine ⟨h.1, ?_⟩
  rcases lt_trichotomy s.2.val t.2.val with hlt | heq | hlt
  · let d : Diag ν := ⟨(s, t), h.1, hlt⟩
    by_cases hZ : Z s = Z t
    · exact Or.inr ⟨hZ, hlt⟩
    · have h1 := (strandLt_fst_snd (shuffleTop Z B) d).1 h
      have e : (shuffleTop Z B).1 (.inr d) = if Z s = Z t then B.1 (.inr d) else Z s :=
        shuffleTop_apply Z B _
      rw [e, ite_eq_right hZ] at h1
      refine Or.inl ⟨h1, ?_⟩
      cases hz : Z t
      · rfl
      · exact absurd (h1.trans hz.symm) hZ
  · exact absurd (Strand.ext_of h.1 heq ▸ h) (StrandLt.irrefl _ t)
  · let d : Diag ν := ⟨(t, s), h.1.symm, hlt⟩
    have h1 : (shuffleTop Z B).1 (.inr d) ≠ true := fun e =>
      ((strandLt_fst_snd (shuffleTop Z B) d).2 e).asymm h
    have e : (shuffleTop Z B).1 (.inr d) = if Z t = Z s then B.1 (.inr d) else Z t :=
      shuffleTop_apply Z B _
    rw [e] at h1
    by_cases hZ : Z t = Z s
    · rw [ite_eq_left hZ] at h1
      exact absurd (hB d) h1
    · rw [ite_eq_right hZ] at h1
      have ht : Z t = false := by simpa using h1
      refine Or.inl ⟨?_, ht⟩
      cases hs : Z s
      · exact absurd (ht.trans hs.symm) hZ
      · rfl

end FullChamber

theorem isRankUpper_rankGe (t : Strand ν) :
    IsRankUpper (Finset.univ.filter fun s : Strand ν => s.1 = t.1 ∧ t.2.val ≤ s.2.val) := by
  intro s u hc hlt hs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
  exact ⟨hc.symm.trans hs.1, hs.2.trans hlt.le⟩

/-- A relabelling dominated by `shuffleTop Z B` does not lower the rank of a strand it sends
into `Z`. -/
theorem IsDominated.rank_le_of_mem {Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : B.IsRankOrdered) {x : ColPerm ν} (hx : IsDominated (shuffleTop Z B) x) {t : Strand ν}
    (ht : Z (x.1 t) = true) : t.2.val ≤ (x.1 t).2.val := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  set L := Finset.univ.filter fun s : Strand ν => s.1 = t.1 ∧ Z s = true ∧ s.2.val ≤ (x.1 t).2.val
  set U := Finset.univ.filter fun s : Strand ν => s.1 = t.1 ∧ t.2.val ≤ s.2.val
  have hL : (shuffleTop Z B).IsLeftClosed L := by
    intro s u hsu hu
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨hc, h | h⟩ := StrandLt.of_shuffleTop hB hsu
    · rw [hu.2.1] at h
      exact absurd h.2 (by simp)
    · exact ⟨hc.trans hu.1, h.1.trans hu.2.1, h.2.le.trans hu.2.2⟩
  have h1 := hx L U hL (isRankUpper_rankGe t)
  have h0 : L ∩ U = ∅ := by
    ext s
    simp only [L, U, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    rintro ⟨⟨-, -, h2⟩, -, h3⟩
    omega
  have hmem : x.1 t ∈ L ∩ U.image x.1 := by
    refine Finset.mem_inter.2 ⟨?_, Finset.mem_image_of_mem _ ?_⟩
    · simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨colPerm_apply_fst x t, ht, le_rfl⟩
    · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      simp
  rw [h0, Finset.card_empty] at h1
  exact Finset.notMem_empty _ ((Finset.card_eq_zero.1 (Nat.le_zero.1 h1)) ▸ hmem)

/-- A relabelling dominated by `shuffleTop Z B` that fixes every strand of `Z` does not lower
the rank of any strand. -/
theorem IsDominated.rank_le_of_fix {Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : B.IsRankOrdered) {x : ColPerm ν} (hx : IsDominated (shuffleTop Z B) x)
    (hfix : ∀ s, Z s = true → x.1 s = s) (t : Strand ν) : t.2.val ≤ (x.1 t).2.val := by
  classical
  by_cases hZt : Z t = true
  · rw [hfix t hZt]
  by_contra hlt
  rw [not_le] at hlt
  have hZx : Z (x.1 t) = false := by
    cases h : Z (x.1 t)
    · rfl
    · exact absurd (x.1.injective (hfix _ h) ▸ h) hZt
  set L := Finset.univ.filter fun s : Strand ν =>
    s.1 = t.1 ∧ (Z s = true ∨ s.2.val ≤ (x.1 t).2.val)
  set U := Finset.univ.filter fun s : Strand ν => s.1 = t.1 ∧ t.2.val ≤ s.2.val
  have hL : (shuffleTop Z B).IsLeftClosed L := by
    intro s u hsu hu
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨hc, h | h⟩ := StrandLt.of_shuffleTop hB hsu
    · exact ⟨hc.trans hu.1, Or.inl h.1⟩
    · refine ⟨hc.trans hu.1, ?_⟩
      rcases hu.2 with hu2 | hu2
      · exact Or.inl (h.1.trans hu2)
      · exact Or.inr (h.2.le.trans hu2)
  have h1 := hx L U hL (isRankUpper_rankGe t)
  have hsub : insert (x.1 t) (L ∩ U) ⊆ L ∩ U.image x.1 := by
    intro s hs
    rcases Finset.mem_insert.1 hs with rfl | hs
    · refine Finset.mem_inter.2 ⟨?_, Finset.mem_image_of_mem _ ?_⟩
      · simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨colPerm_apply_fst x t, Or.inr le_rfl⟩
      · simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        simp
    · simp only [L, U, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      have hZs : Z s = true := by
        rcases hs.1.2 with h | h
        · exact h
        · omega
      refine Finset.mem_inter.2 ⟨?_, ?_⟩
      · simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hs.1
      · rw [← hfix s hZs]
        refine Finset.mem_image_of_mem _ ?_
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hs.2
  have hnot : x.1 t ∉ L ∩ U := by
    simp only [U, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
      not_le]
    intro _ _
    exact hlt
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at h2
  omega

theorem rank_injOn_colour (c : ν.support) {P : Strand ν → Prop} [DecidablePred P] :
    Set.InjOn (fun s : Strand ν => s.2.val)
      (Finset.univ.filter fun s : Strand ν => s.1 = c ∧ P s : Finset (Strand ν)) := by
  intro s hs t ht h
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hs ht
  exact Strand.ext_of (hs.1.trans ht.1.symm) h

/-- **Rigidity of the four-block shuffle.** Let `B` be a four-block chamber for `X` and `Z`, and
let `x` be a relabelling dominated by `shuffleTop Z B` which, at every colour, sends at least as
many strands outside `X` into `Z` as there are strands outside `X` in `Z`. Then `x = 1`.

In the proof of Webster, arXiv:1209.2463v4, Theorem 2.19, this says that the four-block shuffle
element has a single term of top shuffle type. -/
theorem IsDominated.eq_one_of_isFourBlock {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) {x : ColPerm ν} (hx : IsDominated (shuffleTop Z B) x)
    (htype : ∀ c : ν.support,
      (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = false ∧ Z t = true).card ≤
        (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = false ∧ Z (x.1 t) = true).card) :
    x = 1 := by
  classical
  have hsep := hB.isSeparated
  have hR := hB.1
  have hcol := colPerm_apply_fst x
  -- the strands outside `X` sent into `Z`
  have step1 : ∀ c : ν.support,
      (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = false ∧ Z (x.1 t) = true) =
        (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = false ∧ Z t = true) ∧
      ∀ t ∈ (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = false ∧ Z (x.1 t) = true),
        x.1 t = t := by
    intro c
    refine Finset.eq_and_forall_eq_of_rank_le (A := Finset.univ.filter fun t : Strand ν =>
      t.1 = c ∧ X t = false) (fun s => s.2.val) (rank_injOn_colour c) ?_ ?_ ?_ x.1
      x.1.injective.injOn ?_ (htype c) ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨ht.1, ht.2.1⟩
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨ht.1, ht.2.1⟩
    · intro a ha q hq hle
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hq ⊢
      refine ⟨ha.1, ha.2, ?_⟩
      rcases hle.lt_or_eq with hlt | heq
      · exact hB.down (ha.1.trans hq.1.symm) hlt (ha.2.trans hq.2.1.symm) hq.2.2
      · rw [Strand.ext_of (ha.1.trans hq.1.symm) heq]
        exact hq.2.2
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      refine ⟨(hcol t).trans ht.1, ?_, ht.2.2⟩
      cases hXx : X (x.1 t)
      · rfl
      · exfalso
        have hle := IsDominated.rank_le_of_mem hR hx ht.2.2
        rcases hle.lt_or_eq with hlt | heq
        · have := hsep.down_of_isRankOrdered hR (hcol t).symm hlt hXx
          rw [ht.2.1] at this
          exact absurd this (by simp)
        · rw [Strand.ext_of (hcol t) heq.symm] at hXx
          rw [ht.2.1] at hXx
          exact absurd hXx (by simp)
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact IsDominated.rank_le_of_mem hR hx ht.2.2
  have fix1 : ∀ t, X t = false → Z t = true → x.1 t = t := by
    intro t hX hZ
    have ht : t ∈ (Finset.univ.filter fun s : Strand ν => s.1 = t.1 ∧ X s = false ∧ Z s = true) :=
      by simp [hX, hZ]
    rw [← (step1 t.1).1] at ht
    exact (step1 t.1).2 t ht
  -- the strands of `X` sent into `Z`
  have step2 : ∀ c : ν.support,
      (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = true ∧ Z (x.1 t) = true) =
        (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = true ∧ Z t = true) ∧
      ∀ t ∈ (Finset.univ.filter fun t : Strand ν =>
        t.1 = c ∧ X t = true ∧ Z (x.1 t) = true), x.1 t = t := by
    intro c
    have hcardZ :
        (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ Z (x.1 t) = true).card =
          (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ Z t = true).card := by
      refine Finset.card_nbij' x.1 x.1.symm ?_ ?_ ?_ ?_
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        exact ⟨(hcol t).trans ht.1, ht.2⟩
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        refine ⟨?_, by simpa using ht.2⟩
        have := hcol (x.1.symm t)
        rw [Equiv.apply_symm_apply] at this
        exact this.symm.trans ht.1
      · intro t _
        exact x.1.symm_apply_apply t
      · intro t _
        exact x.1.apply_symm_apply t
    have hsplit : ∀ P : Strand ν → Prop, [DecidablePred P] →
        (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ P t).card =
          (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = false ∧ P t).card +
          (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = true ∧ P t).card := by
      intro P _
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        cases X t <;> simp
      · rw [Finset.disjoint_filter]
        intro t _ h1 h2
        rw [h1.2.1] at h2
        exact absurd h2.2.1 (by simp)
    have hcard2 := hsplit (fun t => Z (x.1 t) = true)
    have hcard2' := hsplit (fun t => Z t = true)
    rw [(step1 c).1] at hcard2
    have hcard :
        (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = true ∧ Z t = true).card ≤
          (Finset.univ.filter fun t : Strand ν => t.1 = c ∧ X t = true ∧
            Z (x.1 t) = true).card := by omega
    refine Finset.eq_and_forall_eq_of_rank_le (A := Finset.univ.filter fun t : Strand ν =>
      t.1 = c ∧ X t = true) (fun s => s.2.val) (rank_injOn_colour c) ?_ ?_ ?_ x.1
      x.1.injective.injOn ?_ hcard ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨ht.1, ht.2.1⟩
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨ht.1, ht.2.1⟩
    · intro a ha q hq hle
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hq ⊢
      refine ⟨ha.1, ha.2, ?_⟩
      rcases hle.lt_or_eq with hlt | heq
      · exact hB.down (ha.1.trans hq.1.symm) hlt (ha.2.trans hq.2.1.symm) hq.2.2
      · rw [Strand.ext_of (ha.1.trans hq.1.symm) heq]
        exact hq.2.2
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      refine ⟨(hcol t).trans ht.1, ?_, ht.2.2⟩
      cases hXx : X (x.1 t)
      · exfalso
        have e := x.1.injective (fix1 _ hXx ht.2.2)
        rw [e, ht.2.1] at hXx
        exact absurd hXx (by simp)
      · rfl
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      exact IsDominated.rank_le_of_mem hR hx ht.2.2
  have fixZ : ∀ t, Z t = true → x.1 t = t := by
    intro t hZ
    cases hX : X t
    · exact fix1 t hX hZ
    · have ht : t ∈ (Finset.univ.filter fun s : Strand ν =>
          s.1 = t.1 ∧ X s = true ∧ Z s = true) := by simp [hX, hZ]
      rw [← (step2 t.1).1] at ht
      exact (step2 t.1).2 t ht
  -- the strands outside `Z`
  have hle := IsDominated.rank_le_of_fix hR hx fixZ
  have fixN : ∀ t, Z t = false → x.1 t = t := by
    intro t hZ
    have hmem : t ∈ (Finset.univ.filter fun s : Strand ν => s.1 = t.1 ∧ Z s = false) := by
      simp [hZ]
    refine (Finset.eq_and_forall_eq_of_rank_le (A := Finset.univ.filter fun s : Strand ν =>
      s.1 = t.1 ∧ Z s = false) (fun s => s.2.val) (rank_injOn_colour t.1) subset_rfl subset_rfl
      (fun a ha _ _ _ => ha) x.1 x.1.injective.injOn ?_ le_rfl fun s _ => hle s).2 t hmem
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    refine ⟨(hcol s).trans hs.1, ?_⟩
    cases h : Z (x.1 s)
    · rfl
    · have e := x.1.injective (fixZ _ h)
      rw [e, hs.2] at h
      exact absurd h (by simp)
  refine Subtype.ext (Equiv.ext fun t => ?_)
  show x.1 t = t
  cases hZ : Z t
  · exact fixN t hZ
  · exact fixZ t hZ

end Categorification.WeightedKLR
