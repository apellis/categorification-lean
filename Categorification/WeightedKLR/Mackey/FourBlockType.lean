/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockShuffle

/-!
# The four-block chamber of a shuffle type

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). For a shuffle type `μ`, Webster's four blocks of the
strands of `ν = ν' + ν''` are, colour by colour: the strands of the first block `ν'` of rank
`< ν₁ - μ`, the remaining strands of `ν'`, the strands of the second block of rank `< ν' + μ`,
and the remaining strands of the second block. The first and third blocks together form the set
`blockLeft ν' ν₁ μ` of strands sent into the first block `ν₁` by the shuffle.

In a rank-ordered chamber, a set of strands separating each block of `ν'` is an initial segment
of each colour in that block, so it is determined by the number of its strands of each colour
(`FullChamber.IsFourBlock.down`, `iff_lt_add_card_of_downward`). Applied to the set of strands
that a relabelling `y` sends into the first block of `ν₁`, these numbers are `ν₁ - μ` and `μ`,
`μ` the shuffle type of `y` (`GalleryAlgebra.eq_blockLeft_of_isFourBlock`). So the bottom end of
the shuffle element `ψ^W_g` is a four-block chamber for `blockLeft ν' ν₁ μ`, `μ` the shuffle
type of `g`, and `ψ^W_g = fourShuffle (blockLeft ν' ν₁ μ) (rankShuffleBot g C)`
(`GalleryAlgebra.rankShuffleElt_eq_fourShuffle_blockLeft`).

## Main definitions

* `blockLeft ν' ν₁ μ`: the strands of the first and third of the four blocks of type `μ`.

## Main results

* `GalleryAlgebra.eq_blockLeft_of_isFourBlock`: a set of strands `{t | y t ∈ ν₁}` separating a
  four-block chamber is `blockLeft ν' ν₁ (shuffleType y)`.
* `GalleryAlgebra.rankShuffleElt_eq_fourShuffle_blockLeft`: `ψ^W_g` is the four-block shuffle
  element of type the shuffle type of `g`.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

/-! ### Initial segments of ranks -/

/-- A downward closed subset of an interval `[a, b)` of natural numbers is an initial segment:
`r` lies in it iff `r < a + #(it)`. -/
theorem Nat.iff_lt_add_card_of_downward (Q : ℕ → Prop) [DecidablePred Q] {a b r : ℕ}
    (ha : a ≤ r) (hb : r < b) (hdown : ∀ x y, a ≤ x → x < y → y < b → Q y → Q x) :
    Q r ↔ r < a + ((Finset.Ico a b).filter Q).card := by
  constructor
  · intro hr
    have hsub : Finset.Ico a (r + 1) ⊆ (Finset.Ico a b).filter Q := by
      intro x hx
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨hx.1, by omega⟩, ?_⟩
      rcases Nat.lt_or_ge x r with h | h
      · exact hdown x r hx.1 h hb hr
      · rwa [show x = r by omega]
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    omega
  · intro h
    by_contra hr
    have hsub : (Finset.Ico a b).filter Q ⊆ Finset.Ico a r := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_Ico] at hx
      rw [Finset.mem_Ico]
      refine ⟨hx.1.1, ?_⟩
      by_contra hxr
      rcases Nat.lt_or_ge r x with e | e
      · exact hr (hdown r x ha e hx.1.2 hx.2)
      · exact hr (show x = r by omega ▸ hx.2)
    have := Finset.card_le_card hsub
    rw [Nat.card_Ico] at this
    omega

/-- Counting strands of one colour with ranks in an interval. -/
theorem card_filter_colour (j : ν.support) (a b : ℕ) (hb : b ≤ ν j) (P : Strand ν → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun s : Strand ν => s.1 = j ∧ a ≤ s.2.val ∧ s.2.val < b ∧ P s).card =
      ((Finset.Ico a b).filter fun r => ∃ h : r < ν j, P ⟨j, ⟨r, h⟩⟩).card := by
  refine Finset.card_bij (fun s _ => s.2.val) ?_ ?_ ?_
  · rintro ⟨j', r⟩ hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨rfl, h1, h2, h3⟩ := hs
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨h1, h2⟩, r.isLt, h3⟩
  · intro s hs s' hs' he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hs'
    exact Strand.ext_of (hs.1.trans hs'.1.symm) he
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_Ico] at hr
    obtain ⟨⟨h1, h2⟩, h, h3⟩ := hr
    refine ⟨⟨j, ⟨r, h⟩⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl, h1, h2, h3⟩

/-- **A downward closed set of strands of one colour in a rank interval is an initial
segment.** -/
theorem iff_lt_add_card_of_downward (P : Strand ν → Prop) [DecidablePred P] {a b : ℕ}
    {t : Strand ν} (hb : b ≤ ν t.1) (ha : a ≤ t.2.val) (htb : t.2.val < b)
    (hdown : ∀ s s' : Strand ν, s.1 = t.1 → s'.1 = t.1 → a ≤ s.2.val → s.2.val < s'.2.val →
      s'.2.val < b → P s' → P s) :
    P t ↔ t.2.val <
      a + (Finset.univ.filter fun s : Strand ν =>
        s.1 = t.1 ∧ a ≤ s.2.val ∧ s.2.val < b ∧ P s).card := by
  rw [card_filter_colour t.1 a b hb P]
  have ht : P t ↔ ∃ h : t.2.val < ν t.1, P ⟨t.1, ⟨t.2.val, h⟩⟩ :=
    ⟨fun h => ⟨t.2.isLt, h⟩, fun ⟨_, h⟩ => h⟩
  rw [ht]
  refine Nat.iff_lt_add_card_of_downward (fun r => ∃ h : r < ν t.1, P ⟨t.1, ⟨r, h⟩⟩) ha htb fun x y hx hxy hy hQ => ?_
  obtain ⟨hy', hP⟩ := hQ
  exact ⟨lt_trans hxy hy', hdown ⟨t.1, ⟨x, _⟩⟩ ⟨t.1, ⟨y, hy'⟩⟩ rfl rfl hx hxy hy hP⟩

/-- The number of strands of one colour sent into the first block by a relabelling is `ν₁`. -/
theorem card_filter_isLeft_colPerm {ν₁ ν₂ : I →₀ ℕ} (hν₁ : ν₁ + ν₂ = ν) (y : ColPerm ν)
    (j : ν.support) :
    (Finset.univ.filter fun s : Strand ν => s.1 = j ∧ (y.1 s).IsLeft ν₁).card = ν₁ j := by
  have hle : ν₁ j ≤ ν j := by
    have := congrArg (fun f : I →₀ ℕ => f j.1) hν₁
    simp only [Finsupp.add_apply] at this
    omega
  have e1 : (Finset.univ.filter fun s : Strand ν => s.1 = j ∧ (y.1 s).IsLeft ν₁).card =
      (Finset.univ.filter fun s : Strand ν => s.1 = j ∧ s.IsLeft ν₁).card := by
    refine Finset.card_bij (fun s _ => y.1 s) ?_ ?_ ?_
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact ⟨(colPerm_apply_fst y s).trans hs.1, hs.2⟩
    · intro s _ s' _ he
      exact y.1.injective he
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      refine ⟨y.1⁻¹ s, ?_, y.1.apply_symm_apply s⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hc : (y.1⁻¹ s).1 = s.1 := by
        have := colPerm_apply_fst y (y.1⁻¹ s)
        rw [show y.1 (y.1⁻¹ s) = s from y.1.apply_symm_apply s] at this
        exact this.symm
      refine ⟨hc.trans hs.1, ?_⟩
      rw [show y.1 (y.1⁻¹ s) = s from y.1.apply_symm_apply s]
      exact hs.2
  have e2 : (Finset.univ.filter fun s : Strand ν => s.1 = j ∧ s.IsLeft ν₁) =
      (Finset.univ.filter fun s : Strand ν => s.1 = j ∧ 0 ≤ s.2.val ∧ s.2.val < ν₁ j ∧ True) := by
    refine Finset.filter_congr fun s _ => ?_
    unfold Strand.IsLeft
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Nat.zero_le _, by rw [← h1]; exact h2, trivial⟩
    · rintro ⟨h1, -, h2, -⟩
      exact ⟨h1, by rw [show ν₁ s.1 = ν₁ j by rw [h1]]; exact h2⟩
  rw [e1, e2, card_filter_colour j 0 (ν₁ j) hle]
  have e3 : ((Finset.Ico 0 (ν₁ j)).filter fun r => ∃ _ : r < ν j, True) =
      Finset.Ico 0 (ν₁ j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Ico, exists_prop, and_true]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by omega⟩
  rw [e3, Nat.card_Ico, Nat.sub_zero]

namespace FullChamber

omit [DecidableEq I] in
/-- In a four-block chamber for `X` and `Z`, the strands of `Z` of one colour inside one block of
`X` are an initial segment of ranks. -/
theorem IsFourBlock.down {X Z : Strand ν → Bool} {B : FullChamber Γ ν} (hB : IsFourBlock X Z B)
    {s t : Strand ν} (hc : s.1 = t.1) (hlt : s.2.val < t.2.val) (hX : X s = X t)
    (ht : Z t = true) : Z s = true := by
  let d : Diag ν := ⟨(s, t), hc, hlt⟩
  have h1 : B.1 (.inr d) = true := hB.1 d
  have h2 : (if X s = X t then (if Z s = Z t then B.1 (.inr d) else Z s) else X s) =
      B.1 (.inr d) := by
    have : (shuffleBot X Z B).1 (.inr d) = B.1 (.inr d) := by rw [hB.2]
    rw [shuffleBot_apply, shuffleTop_apply] at this
    exact this
  rw [ite_eq_left_iff.mpr (fun h => absurd hX h)] at h2
  by_cases hZ : Z s = Z t
  · rw [hZ]
    exact ht
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hZ)] at h2
    rw [h2]
    exact h1

omit [DecidableEq I] [IsStrictOrderedRing 𝕜] in
/-- In a rank-ordered chamber separated by `W`, the strands of `W` of one colour are an initial
segment of ranks. -/
theorem IsSeparated.down_of_isRankOrdered {W : Strand ν → Bool} {A : FullChamber Γ ν}
    (hW : IsSeparated W A) (hA : A.IsRankOrdered) {s t : Strand ν} (hc : s.1 = t.1)
    (hlt : s.2.val < t.2.val) (ht : W t = true) : W s = true := by
  let d : Diag ν := ⟨(s, t), hc, hlt⟩
  by_contra hs
  have hne : W (Hyp.lo (Sum.inr d : Hyp Γ ν)) ≠ W (Hyp.hi (Sum.inr d : Hyp Γ ν)) := by
    change W s ≠ W t
    rw [ht]
    exact hs
  have := hW (.inr d) hne
  rw [hA d] at this
  exact hs this.symm

end FullChamber

/-- **The four blocks of a shuffle type.** For a shuffle type `μ`, the strands `t` of the first
block of `ν'` of rank `< ν₁ - μ` and the strands of the second block of rank `< ν' + μ`: the
strands sent into the first block of `ν₁` by a shuffle of type `μ`. -/
def blockLeft (ν' ν₁ : I →₀ ℕ) (μ : I → ℕ) (t : Strand ν) : Bool :=
  if t.IsLeft ν' then decide (t.2.val < ν₁ t.1 - μ t.1) else decide (t.2.val < ν' t.1 + μ t.1)

namespace GalleryAlgebra

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

/-- **The set of strands sent into the first block is determined by the shuffle type.** If the
set `{t | y t ∈ ν₁}` separates a four-block chamber `B` (for the strands of `ν'`), it is
`blockLeft ν' ν₁ (shuffleType y)`. -/
theorem eq_blockLeft_of_isFourBlock (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (y : ColPerm ν)
    {B : FullChamber Γ ν}
    (hB : IsFourBlock (fun t => decide (t.IsLeft ν')) (fun t => decide ((y.1 t).IsLeft ν₁)) B) :
    (fun t => decide ((y.1 t).IsLeft ν₁)) = blockLeft ν' ν₁ (shuffleType ν' ν₁ y) := by
  funext t
  have hν'le : ν' t.1 ≤ ν t.1 := by
    have := congrArg (fun f : I →₀ ℕ => f t.1.1) hν'
    simp only [Finsupp.add_apply] at this
    omega
  have hX : ∀ s : Strand ν, s.1 = t.1 → (s.IsLeft ν' ↔ s.2.val < ν' t.1) := by
    intro s hs
    unfold Strand.IsLeft
    rw [show ν' s.1 = ν' t.1 by rw [hs]]
  -- the strands of colour `t.1` sent into the first block, split by the blocks of `ν'`
  set L := (Finset.univ.filter fun s : Strand ν =>
    s.1 = t.1 ∧ 0 ≤ s.2.val ∧ s.2.val < ν' t.1 ∧ (y.1 s).IsLeft ν₁).card
  set R := (Finset.univ.filter fun s : Strand ν =>
    s.1 = t.1 ∧ ν' t.1 ≤ s.2.val ∧ s.2.val < ν t.1 ∧ (y.1 s).IsLeft ν₁).card
  have hR : R = shuffleType ν' ν₁ y t.1 := by
    rw [shuffleType]
    refine congrArg Finset.card (Finset.filter_congr fun s _ => ?_)
    unfold Strand.IsLeft
    constructor
    · rintro ⟨h1, h2, -, h3⟩
      have e : ν' s.1 = ν' t.1 := by rw [h1]
      exact ⟨congrArg Subtype.val h1, by omega, h3⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' : s.1 = t.1 := Subtype.ext h1
      have e : ν' s.1 = ν' t.1 := by rw [h1']
      have e' : ν s.1 = ν t.1 := by rw [h1']
      have := s.2.isLt
      exact ⟨h1', by omega, by omega, h3⟩
  have hLR : L + R = ν₁ t.1 := by
    rw [← card_filter_isLeft_colPerm hν₁ y t.1]
    rw [← Finset.card_filter_add_card_filter_not (fun s : Strand ν => s.IsLeft ν'),
      Finset.filter_filter, Finset.filter_filter]
    refine congrArg₂ (· + ·) (congrArg Finset.card (Finset.filter_congr fun s _ => ?_))
      (congrArg Finset.card (Finset.filter_congr fun s _ => ?_))
    · unfold Strand.IsLeft
      constructor
      · rintro ⟨h1, -, h2, h3⟩
        have e : ν' s.1 = ν' t.1 := by rw [h1]
        exact ⟨⟨h1, h3⟩, by omega⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩
        have e : ν' s.1 = ν' t.1 := by rw [h1]
        exact ⟨h1, Nat.zero_le _, by omega, h3⟩
    · unfold Strand.IsLeft
      constructor
      · rintro ⟨h1, h2, -, h3⟩
        have e : ν' s.1 = ν' t.1 := by rw [h1]
        exact ⟨⟨h1, h3⟩, by omega⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩
        have e : ν' s.1 = ν' t.1 := by rw [h1]
        have e' : ν s.1 = ν t.1 := by rw [h1]
        have := s.2.isLt
        exact ⟨h1, by omega, by omega, h3⟩
  unfold blockLeft
  by_cases ht : t.IsLeft ν'
  · simp only [ht, ↓reduceIte]
    have ht' : t.2.val < ν' t.1 := ht
    have key := iff_lt_add_card_of_downward (fun s => (y.1 s).IsLeft ν₁) (a := 0) (b := ν' t.1)
      (t := t) hν'le (Nat.zero_le _) ht' fun s s' hs hs' _ hlt hb hZ =>
        of_decide_eq_true (hB.down (hs.trans hs'.symm) hlt
          (by simp only [decide_eq_decide]; rw [hX s hs, hX s' hs']; omega) (decide_eq_true hZ))
    rw [zero_add] at key
    change _ = decide (t.2.val < ν₁ t.1 - shuffleType ν' ν₁ y t.1)
    rw [← hR]
    have hL : L = ν₁ t.1 - R := by omega
    rw [← hL]
    exact Bool.eq_iff_iff.2 (decide_eq_true_iff.trans (key.trans decide_eq_true_iff.symm))
  · simp only [ht, ↓reduceIte]
    have ht' : ν' t.1 ≤ t.2.val := by
      unfold Strand.IsLeft at ht
      omega
    have key := iff_lt_add_card_of_downward (fun s => (y.1 s).IsLeft ν₁) (a := ν' t.1) (b := ν t.1)
      (t := t) le_rfl ht' t.2.isLt fun s s' hs hs' ha hlt hb hZ =>
        of_decide_eq_true (hB.down (hs.trans hs'.symm) hlt
          (by simp only [decide_eq_decide]; rw [hX s hs, hX s' hs']; omega) (decide_eq_true hZ))
    change _ = decide (t.2.val < ν' t.1 + shuffleType ν' ν₁ y t.1)
    rw [← hR]
    exact Bool.eq_iff_iff.2 (decide_eq_true_iff.trans (key.trans decide_eq_true_iff.symm))

/-- The set of strands of the bottom end of `ψ^W_g` sent into the first block is the union of
the first and third of the four blocks of the shuffle type of `g`. -/
theorem rankShuffleSet_eq_blockLeft (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (g : ColPerm ν)
    {C : FullChamber Γ ν} (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) :
    rankShuffleSet hν' ν₁ g C = blockLeft ν' ν₁ (shuffleType ν' ν₁ g) := by
  set v := blockSort hν' (shuffleBot (fun t => decide (t.IsLeft ν'))
    (fun t => decide ((g.1 t).IsLeft ν₁)) C)
  have hB := isFourBlock_rankShuffleBot (Γ := Γ) hν' ν₁ g hCs
  have hZ : rankShuffleSet hν' ν₁ g C = fun t => decide (((g * v⁻¹).1 t).IsLeft ν₁) := rfl
  rw [hZ] at hB ⊢
  rw [eq_blockLeft_of_isFourBlock hν' hν₁ (g * v⁻¹) hB]
  congr 1
  have e2 := shuffleType_mul_of_image_right ν' ν₁ (y := v)
    (fun i => image_rightStrands_of_mem (blockSort_mem_leftBlockStab hν'
      (shuffleBot (fun t => decide (t.IsLeft ν')) (fun t => decide ((g.1 t).IsLeft ν₁)) C)) i)
    (g * v⁻¹)
  rw [inv_mul_cancel_right] at e2
  exact e2.symm

/-- **`ψ^W_g` is the four-block shuffle element of its type.** For `C` separated by the strands
of `ν'`, `ψ^W_g = fourShuffle (blockLeft ν' ν₁ μ) (rankShuffleBot g C)`, `μ` the shuffle type of
`g`, and `rankShuffleBot g C` is a four-block chamber for `blockLeft ν' ν₁ μ`. -/
theorem rankShuffleElt_eq_fourShuffle_blockLeft (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν) {C : FullChamber Γ ν}
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) :
    rankShuffleElt k hν' hν₁ hD hZ g C =
      fourShuffle k hD hZ (blockLeft ν' ν₁ (shuffleType ν' ν₁ g)) (rankShuffleBot hν' ν₁ g C) ∧
    IsFourBlock (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ (shuffleType ν' ν₁ g))
      (rankShuffleBot hν' ν₁ g C) := by
  rw [← rankShuffleSet_eq_blockLeft hν' hν₁ g hCs]
  exact ⟨rankShuffleElt_eq_fourShuffle hν' hν₁ hD hZ g hCs, isFourBlock_rankShuffleBot hν' ν₁ g hCs⟩

end GalleryAlgebra

end Categorification.WeightedKLR
