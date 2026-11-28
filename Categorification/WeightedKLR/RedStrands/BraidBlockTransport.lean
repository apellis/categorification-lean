/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.BraidColumnBlockPermutation

/-!
# Transport of red-led blocks and the labels of a braided projective

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3,
Proposition 6.20 (mutation of the standard stratification). A nonviolated red-ordered loading
is the row of its red-led blocks (`exists_braidBlockPositions`); the block lengths are unique
(`eq_of_braidBlockPositions`). Moving the whole blocks by `w` gives the loading
`blockTransport w s` of red order `w`.

The standard filtration of `e(t) T^λ` is indexed by the projective wirings `φ` of
Proposition 5.20 (`ProjectiveBlockIndex`), with constituents `φ⁻¹ t`. Every constituent lies
above `t` in Webster's order (`stendhalLE_inv_smul`), and only `φ = 1` gives one that is not
strictly above (`eq_one_of_stendhalLE_inv_smul`): a projective wiring that keeps the black
counts left of each red is the identity.
-/

namespace Categorification.Stendhal

open KLR TypeA Equiv
open scoped BigOperators

variable {I : Type} [DecidableEq I] {ℓ : ℕ} {ν : Multiset I}

local notation "μ" => stendhalWeight ℓ ν
local notation "m" => Multiset.card μ

section Unique

omit [DecidableEq I]

private theorem val_braidBlockPositions_zero (n : Fin ℓ → ℕ) {d : ℕ}
    (hn : (∑ r, (n r + 1)) = d) (r : Fin ℓ) :
    (braidBlockPositions n hn ⟨r, 0⟩ : ℕ) =
      ∑ j ∈ Finset.range r, ((fun j => if h : j < ℓ then n ⟨j, h⟩ else 0) j + 1) := by
  simp only [braidBlockPositions, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply, Fin.val_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dite_eq_left (j.isLt.trans r.isLt)]
  rfl

private theorem sum_range_ext_eq (n : Fin ℓ → ℕ) :
    ∑ j ∈ Finset.range ℓ, ((fun j => if h : j < ℓ then n ⟨j, h⟩ else 0) j + 1) =
      ∑ r, (n r + 1) := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [dite_eq_left j.isLt]

end Unique

/-- **The red-led block lengths of a loading are unique.** -/
theorem eq_of_braidBlockPositions {s : Seq μ} {n n' : Fin ℓ → ℕ}
    {hn : (∑ r, (n r + 1)) = m} {hn' : (∑ r, (n' r + 1)) = m}
    (h : ∀ r : Fin ℓ, s.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r)
    (h' : ∀ r : Fin ℓ, s.lbl (braidBlockPositions n' hn' ⟨r, 0⟩) = .inr r) : n = n' := by
  let e : (Fin ℓ → ℕ) → ℕ → ℕ := fun n j => if h : j < ℓ then n ⟨j, h⟩ else 0
  let G : (Fin ℓ → ℕ) → ℕ → ℕ := fun n j => ∑ i ∈ Finset.range j, (e n i + 1)
  have hG : ∀ j ≤ ℓ, G n j = G n' j := by
    intro j hj
    rcases hj.lt_or_eq with hj | hj
    · have := congrArg Fin.val (lbl_eq_inr_unique (h ⟨j, hj⟩) (h' ⟨j, hj⟩))
      rwa [val_braidBlockPositions_zero, val_braidBlockPositions_zero] at this
    · rw [hj]
      change ∑ i ∈ Finset.range ℓ, (e n i + 1) = ∑ i ∈ Finset.range ℓ, (e n' i + 1)
      rw [sum_range_ext_eq, sum_range_ext_eq, hn, hn']
  funext r
  have h1 := hG (r + 1) r.isLt
  have h0 := hG r r.isLt.le
  simp only [G, Finset.sum_range_succ] at h1
  have : e n r = e n' r := by
    change G n r + (e n r + 1) = G n' r + (e n' r + 1) at h1
    omega
  simpa [e, dite_eq_left r.isLt] using this

open Classical in
/-- **Transport of red-led blocks**: for a nonviolated red-ordered loading `s`, the loading
obtained by moving its red-led blocks by `w` (the red at rank `r` of the result is `λ_{w r}`,
followed by its block). For other loadings it is `s`. -/
noncomputable def blockTransport (w : Perm (Fin ℓ)) (s : Seq μ) : Seq μ :=
  if h : ∃ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m),
      ∀ r : Fin ℓ, s.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r then
    braidBlockPermutation h.choose h.choose_spec.choose w • s
  else s

/-- The block transport computed from any block decomposition. -/
theorem blockTransport_eq (w : Perm (Fin ℓ)) {s : Seq μ} (n : Fin ℓ → ℕ)
    (hn : (∑ r, (n r + 1)) = m)
    (h : ∀ r : Fin ℓ, s.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r) :
    blockTransport w s = braidBlockPermutation n hn w • s := by
  have hex : ∃ (n : Fin ℓ → ℕ) (hn : (∑ r, (n r + 1)) = m),
      ∀ r : Fin ℓ, s.lbl (braidBlockPositions n hn ⟨r, 0⟩) = .inr r := ⟨n, hn, h⟩
  rw [blockTransport, dite_eq_left hex]
  obtain rfl := eq_of_braidBlockPositions hex.choose_spec.choose_spec h
  rfl

/-- The red order of a block transport is `w`. -/
theorem redWord_blockTransport (w : Perm (Fin ℓ)) {s : Seq μ} (hs : IsRedOrdered s)
    (hv : ¬ IsViolated s) : redWord (blockTransport w s) = (List.finRange ℓ).map w := by
  obtain ⟨n, hn, h⟩ := exists_braidBlockPositions s hs hv
  rw [blockTransport_eq w n hn h]
  exact redWord_braidBlockPermutation_smul s n hn w h

section Order

omit [DecidableEq I] in
private theorem perm_apply_inv (φ : Perm (Fin m)) (x : Fin m) : φ (φ⁻¹ x) = x :=
  φ.apply_symm_apply x

omit [DecidableEq I] in
private theorem lbl_inv_smul (φ : Perm (Fin m)) (s : Seq μ) (a : Fin m) :
    (φ⁻¹ • s).lbl a = s.lbl (φ a) := by
  rw [BraidedStendhalAlgebra.lbl_smul, inv_inv]

private theorem blackCount_eq_filter (s : Seq μ) (r : Fin ℓ) (i : I) :
    blackCount s r i =
      (Finset.univ.filter fun a => s.lbl a = .inl i ∧ a < redPos s r).card := by
  unfold blackCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_congr_right_iff]
  intro _
  exact ⟨fun h => h _ (lbl_redPos s r), fun h b hb => eq_redPos hb ▸ h⟩

omit [DecidableEq I] in
private theorem redPos_inv_smul (φ : Perm (Fin m)) (s : Seq μ) (r : Fin ℓ) :
    φ (redPos (φ⁻¹ • s) r) = redPos s r := by
  classical
  apply eq_redPos
  rw [← lbl_inv_smul, lbl_redPos]

omit [DecidableEq I] in
/-- In a projective wiring, a black strand left of `λ_r` at the top is left of `λ_r` at the
bottom. -/
theorem ProjectiveBlockIndex.lt_redPos_of_lt {t : Seq μ} {φ : Perm (Fin m)}
    (hφ : ProjectiveBlockIndex t φ) {a : Fin m} {i : I} (ha : (φ⁻¹ • t).lbl a = .inl i)
    {r : Fin ℓ} (h : φ a < redPos t r) : a < redPos (φ⁻¹ • t) r := by
  rcases lt_trichotomy a (redPos (φ⁻¹ • t) r) with h1 | h1 | h1
  · exact h1
  · rw [h1, lbl_redPos] at ha
    cases ha
  · exact absurd (hφ.only_rightwards a i r ha h1) (not_lt_of_gt h)

private theorem filter_subset_image {t : Seq μ} {φ : Perm (Fin m)}
    (hφ : ProjectiveBlockIndex t φ) (r : Fin ℓ) (i : I) :
    (Finset.univ.filter fun a => t.lbl a = .inl i ∧ a < redPos t r).image ⇑(φ⁻¹ : Perm (Fin m)) ⊆
      Finset.univ.filter fun a => (φ⁻¹ • t).lbl a = .inl i ∧ a < redPos (φ⁻¹ • t) r := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨hxi, hxr⟩ := (Finset.mem_filter.1 hx).2
  have hl : (φ⁻¹ • t).lbl (φ⁻¹ x) = .inl i := by
    rw [lbl_inv_smul, perm_apply_inv, hxi]
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hl, hφ.lt_redPos_of_lt hl ?_⟩
  rwa [perm_apply_inv]

/-- **The constituents of a projective lie above it** (Webster, arXiv:1309.3796v3, proof of
Proposition 5.20): for a projective wiring `φ` of `t`, `t ≤ φ⁻¹ t` in Webster's order. -/
theorem stendhalLE_inv_smul {t : Seq μ} {φ : Perm (Fin m)} (hφ : ProjectiveBlockIndex t φ) :
    StendhalLE t (φ⁻¹ • t) := by
  intro r i
  rw [blackCount_eq_filter, blackCount_eq_filter]
  refine le_trans (le_of_eq (Finset.card_image_of_injective _ φ⁻¹.injective).symm)
    (Finset.card_le_card (filter_subset_image hφ r i))

/-- If a projective wiring keeps the black counts, every black strand left of `λ_r` at the
bottom is left of `λ_r` at the top. -/
private theorem lt_redPos_of_stendhalLE {t : Seq μ} {φ : Perm (Fin m)}
    (hφ : ProjectiveBlockIndex t φ) (hle : StendhalLE (φ⁻¹ • t) t) {a : Fin m} {i : I}
    (ha : (φ⁻¹ • t).lbl a = .inl i) {r : Fin ℓ} (h : a < redPos (φ⁻¹ • t) r) :
    φ a < redPos t r := by
  have hsub := filter_subset_image hφ r i
  have hcard := hle r i
  rw [blackCount_eq_filter, blackCount_eq_filter] at hcard
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_image_of_injective _ φ⁻¹.injective]
    exact hcard)
  have hmem : a ∈ Finset.univ.filter fun a =>
      (φ⁻¹ • t).lbl a = .inl i ∧ a < redPos (φ⁻¹ • t) r :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, ha, h⟩
  rw [← heq] at hmem
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hmem
  rw [perm_apply_inv]
  exact (Finset.mem_filter.1 hx).2.2

/-- **Only the identity wiring gives a constituent not strictly above** (Webster,
arXiv:1309.3796v3, proof of Proposition 5.20): if a projective wiring `φ` of a red-ordered
loading `t` has `φ⁻¹ t ≤ t`, then `φ = 1`. -/
theorem eq_one_of_stendhalLE_inv_smul {t : Seq μ} (ht : IsRedOrdered t) {φ : Perm (Fin m)}
    (hφ : ProjectiveBlockIndex t φ) (hle : StendhalLE (φ⁻¹ • t) t) : φ = 1 := by
  set b := φ⁻¹ • t
  have hb : IsRedOrdered b := hφ.bottom_ordered
  have hlbl (a : Fin m) : t.lbl (φ a) = b.lbl a := (lbl_inv_smul φ t a).symm
  have hred (r : Fin ℓ) : φ (redPos b r) = redPos t r := redPos_inv_smul φ t r
  -- black left of a red, red left of a black, two reds
  have hbr : ∀ (a : Fin m) (i : I) (r : Fin ℓ), b.lbl a = .inl i → a < redPos b r →
      φ a < φ (redPos b r) := fun a i r ha h => by
    rw [hred]
    exact lt_redPos_of_stendhalLE hφ hle ha h
  have hrb : ∀ (a : Fin m) (i : I) (r : Fin ℓ), b.lbl a = .inl i → redPos b r < a →
      φ (redPos b r) < φ a := fun a i r ha h => by
    rw [hred]
    exact hφ.only_rightwards a i r ha h
  have hrr : ∀ r r' : Fin ℓ, redPos b r < redPos b r' → φ (redPos b r) < φ (redPos b r') :=
    fun r r' h => by
      rw [hred, hred]
      exact (redPos_lt_iff ht).2 ((redPos_lt_iff hb).1 h)
  have hmono : StrictMono φ := by
    intro a a' haa'
    cases ha : b.lbl a with
    | inr r =>
      have hra := eq_redPos ha
      cases ha' : b.lbl a' with
      | inr r' =>
        have hra' := eq_redPos ha'
        rw [hra, hra'] at haa' ⊢
        exact hrr r r' haa'
      | inl j =>
        rw [hra] at haa' ⊢
        exact hrb a' j r ha' haa'
    | inl i =>
      cases ha' : b.lbl a' with
      | inr r' =>
        have hra' := eq_redPos ha'
        rw [hra'] at haa' ⊢
        exact hbr a i r' ha haa'
      | inl j =>
        by_cases hbetween : ∃ r, a < redPos b r ∧ redPos b r < a'
        · obtain ⟨r, h1, h2⟩ := hbetween
          exact (hbr a i r ha h1).trans (hrb a' j r ha' h2)
        · exact hφ.bottom_block_order a a' i j ha ha' haa' fun r h => hbetween ⟨r, h⟩
  have hinv : StrictMono (φ⁻¹ : Perm (Fin m)) := fun x y hxy => by
    rw [← hmono.lt_iff_lt, perm_apply_inv, perm_apply_inv]
    exact hxy
  have hid : ∀ a, φ a = a := fun a => by
    have h1 : a ≤ φ a := hmono.id_le a
    have h2 : a ≤ φ⁻¹ a := hinv.id_le a
    have h3 : φ a ≤ a := by
      simpa only [perm_apply_inv] using hmono.monotone h2
    exact le_antisymm h3 h1
  exact Equiv.ext hid

end Order

end Categorification.Stendhal
