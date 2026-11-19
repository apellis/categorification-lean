/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.RedStrands.LastRedBlackBimodule

/-!
# Surjectivity of the bimodule map of Proposition 4.32

B. Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, §4.6,
Proposition 4.32. The map `g ↦ appendRed(g) · lastRedBlackCrossing` of
`Categorification.Stendhal.lastRedBlackMap` is onto `e_ℓ T_{i+ν} ν_i(e_ℓ)`. Webster's argument:
in a diagram from a loading `(s, λ_ℓ, i)` at the bottom to a loading ending in `λ_ℓ` at the top,
the last red strand and the black strand `i` cross, and the diagram can be isotoped so that this
crossing is at the bottom. Here this is a statement about the standard spanning set of
red-ordered Stendhal diagrams, for a choice of reduced words that ends with the crossing
`s_{N₀}` whenever possible.

## Main results

* `exists_lastRedBlackStendhal`: before taking the violating quotient, every diagram of
  `e_ℓ T̃_{i+ν} ν_i(e_ℓ)` is `appendRed(g) · crossingStendhalCut`.
* `exists_lastRedBlackMap_eq`: every element of `e_ℓ T_{i+ν} ν_i(e_ℓ)` lies in the image of
  `lastRedBlackMap`.
-/

noncomputable section

attribute [local instance 1100] IsIdempotentElem.instAlgebraCorner_categorification

namespace Categorification.Stendhal

open KLR KLRAlgebra TypeA Equiv

variable {I : Type} {ℓ : ℕ} [DecidableEq I] {k : Type*} [CommRing k]
  (Q : I → I → MvPolynomial (Fin 2) k) (Λ : Fin (ℓ + 1) → I →₀ ℕ) (i : I) (ν : Multiset I)

local notation "νᵢ" => ((Singleton.singleton i : Multiset I) + ν)
local notation "N₀" => Multiset.card (stendhalWeight ℓ ν)
local notation "m" => Multiset.card (stendhalWeight (ℓ + 1) νᵢ)

section Combinatorics

variable {i ν}

omit [DecidableEq I] in
theorem card_stendhalWeight_addRed_addBlack :
    Multiset.card (stendhalWeight (ℓ + 1) νᵢ) = N₀ + 2 := by
  simp [stendhalWeight]
  omega

omit [DecidableEq I] in
private theorem card_stendhalWeight_addRed :
    Multiset.card (stendhalWeight (ℓ + 1) ν) = N₀ + 1 := by
  simp [stendhalWeight]
  omega

omit [DecidableEq I] in
private theorem lastRedPosition_val :
    (lastRedPosition ℓ ν : ℕ) = N₀ := by
  simp [lastRedPosition, stendhalWeight]

omit [DecidableEq I] in
private theorem lastRedPosition_addBlack_val :
    (lastRedPosition ℓ νᵢ : ℕ) = N₀ + 1 := by
  simp [lastRedPosition, stendhalWeight]
  omega

/-- The position `N₀` of the last red strand in a loading `(s, λ_ℓ, i)`. -/
def redSlot : Fin m := ⟨N₀, by rw [card_stendhalWeight_addRed_addBlack]; omega⟩

/-- The position `N₀ + 1` of the black strand `i` in a loading `(s, λ_ℓ, i)`. -/
def blackSlot : Fin m := ⟨N₀ + 1, by rw [card_stendhalWeight_addRed_addBlack]; omega⟩

omit [DecidableEq I] in
private theorem red_unique {δ : Multiset (I ⊕ Fin (ℓ + 1))} {ν' : Multiset I}
    (h : δ = stendhalWeight (ℓ + 1) ν') (r : Fin (ℓ + 1)) (s : KLR.Seq δ)
    (a b : Fin δ.card) (ha : s.lbl a = Sum.inr r) (hb : s.lbl b = Sum.inr r) : a = b := by
  classical
  subst δ
  have hred : Multiset.count (Sum.inr r : I ⊕ Fin (ℓ + 1)) (ν'.map Sum.inl) = 0 := by
    apply Multiset.count_eq_zero_of_notMem
    simp
  have hcnt : Multiset.count (Sum.inr r : I ⊕ Fin (ℓ + 1)) (stendhalWeight (ℓ + 1) ν') ≤ 1 := by
    rw [stendhalWeight, Multiset.count_add, hred, zero_add]
    exact Multiset.nodup_iff_count_le_one.mp
      (Finset.univ.nodup.map Sum.inr_injective) _
  have hcard : (Finset.univ.filter (fun a => Sum.inr r = s.lbl a)).card ≤ 1 := by
    rw [← s.2, Multiset.count_map] at hcnt
    exact hcnt
  exact Finset.card_le_one_iff.mp hcard (by simp [ha]) (by simp [hb])

variable (i) in
omit [DecidableEq I] in
theorem appendBlackLoading_redSlot (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : HasLastRed s) :
    (appendBlackLoading i ν s).lbl (redSlot (i := i) (ν := ν)) = .inr (Fin.last ℓ) := by
  rw [appendBlackLoading_lbl_of_lt i ν s _
    (by change N₀ < _; rw [card_stendhalWeight_addRed]; omega)]
  rw [← hs]
  congr 1
  exact Fin.ext (lastRedPosition_val (ν := ν)).symm

variable (i) in
omit [DecidableEq I] in
theorem appendBlackLoading_blackSlot (s : Seq (stendhalWeight (ℓ + 1) ν)) :
    (appendBlackLoading i ν s).lbl (blackSlot (i := i) (ν := ν)) = .inl i :=
  appendBlackLoading_lbl_of_eq i ν s _ (by
    change N₀ + 1 = _; rw [card_stendhalWeight_addRed])

omit [DecidableEq I] in
private theorem sadj_redSlot :
    sadj m N₀ (redSlot (i := i) (ν := ν)) = blackSlot (i := i) (ν := ν) := by
  apply Fin.ext
  rw [sadj_val_of_lt (by rw [card_stendhalWeight_addRed_addBlack]; omega)]
  simp [swapNat, redSlot, blackSlot]

omit [DecidableEq I] in
private theorem sadj_blackSlot :
    sadj m N₀ (blackSlot (i := i) (ν := ν)) = redSlot (i := i) (ν := ν) := by
  apply Fin.ext
  rw [sadj_val_of_lt (by rw [card_stendhalWeight_addRed_addBlack]; omega)]
  simp [swapNat, redSlot, blackSlot]

variable (i) in
/-- The loading `(s, i, λ_ℓ)` at the top of the crossing. -/
def crossedLoading (s : Seq (stendhalWeight (ℓ + 1) ν)) : Seq (stendhalWeight (ℓ + 1) νᵢ) :=
  sadj m N₀ • appendBlackLoading i ν s

variable (i) in
omit [DecidableEq I] in
theorem hasLastRed_crossedLoading (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : HasLastRed s) :
    HasLastRed (crossedLoading i s) := by
  have hpos : lastRedPosition ℓ νᵢ = blackSlot (i := i) (ν := ν) :=
    Fin.ext (lastRedPosition_addBlack_val (i := i) (ν := ν))
  change (crossedLoading i s).1 (lastRedPosition ℓ νᵢ) = _
  rw [hpos, crossedLoading, Seq.smul_apply, sadj_symm, sadj_blackSlot]
  exact appendBlackLoading_redSlot i s hs

variable (i) in
omit [DecidableEq I] in
theorem isRedOrdered_crossedLoading (s : Seq (stendhalWeight (ℓ + 1) ν)) (ho : IsRedOrdered s) :
    IsRedOrdered (crossedLoading i s) := by
  have hm := card_stendhalWeight_addRed_addBlack (i := i) (ν := ν) (ℓ := ℓ)
  have hlt : N₀ + 1 < m := by omega
  have ho' := appendBlackLoading_ordered i ν s ho
  intro a b r r' hab ha hb
  change (appendBlackLoading i ν s).1 ((sadj m N₀).symm a) = _ at ha
  change (appendBlackLoading i ν s).1 ((sadj m N₀).symm b) = _ at hb
  rw [sadj_symm] at ha hb
  have hva := sadj_val_of_lt hlt a
  have hvb := sadj_val_of_lt hlt b
  rcases lt_trichotomy (sadj m N₀ a) (sadj m N₀ b) with h | h | h
  · exact ho' _ _ r r' h ha hb
  · exact absurd ((sadj m N₀).injective h) (ne_of_lt hab)
  · have hab' : (a : ℕ) < b := hab
    have h' : (sadj m N₀ b : ℕ) < sadj m N₀ a := h
    rw [hva, hvb] at h'
    have hb0 : (b : ℕ) = N₀ + 1 := by
      rcases swapNat_cases N₀ a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;>
      rcases swapNat_cases N₀ b with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5, h6⟩ <;> omega
    have hbs : sadj m N₀ b = redSlot (i := i) (ν := ν) := by
      apply Fin.ext; rw [hvb]; simp [swapNat, hb0, redSlot]
    have ha0 : (a : ℕ) = N₀ := by
      rcases swapNat_cases N₀ a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;>
      rcases swapNat_cases N₀ b with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h5, h6⟩ <;> omega
    have has : sadj m N₀ a = blackSlot (i := i) (ν := ν) := by
      apply Fin.ext; rw [hva]; simp [swapNat, ha0, blackSlot]
    rw [has] at ha
    exact absurd (ha.symm.trans (appendBlackLoading_blackSlot i s)) (by simp)

omit [DecidableEq I] in
/-- If a permutation carries the last red strand of `(s, λ_ℓ, i)` to the far right, it moves
the strands at `N₀` and `N₀ + 1` out of order. -/
theorem lt_of_hasLastRed_smul (s : Seq (stendhalWeight (ℓ + 1) ν)) (hs : HasLastRed s)
    (w : Perm (Fin m)) (hw : HasLastRed (w • appendBlackLoading i ν s)) :
    w (blackSlot (i := i) (ν := ν)) < w (redSlot (i := i) (ν := ν)) := by
  have hpos : lastRedPosition ℓ νᵢ = blackSlot (i := i) (ν := ν) :=
    Fin.ext (lastRedPosition_addBlack_val (i := i) (ν := ν))
  change (w • appendBlackLoading i ν s).1 (lastRedPosition ℓ νᵢ) = _ at hw
  rw [hpos, Seq.smul_apply] at hw
  have he := red_unique rfl _ _ _ _ hw (appendBlackLoading_redSlot i s hs)
  have hw' : w (redSlot (i := i) (ν := ν)) = blackSlot (i := i) (ν := ν) := by
    rw [← he]; exact w.apply_symm_apply _
  rw [hw']
  have hne : w (blackSlot (i := i) (ν := ν)) ≠ blackSlot (i := i) (ν := ν) := by
    intro h
    have h2 := w.injective (h.trans hw'.symm)
    have h3 := congrArg Fin.val h2
    simp only [redSlot, blackSlot] at h3
    omega
  have hle := (w (blackSlot (i := i) (ν := ν))).isLt
  have hm := card_stendhalWeight_addRed_addBlack (i := i) (ν := ν) (ℓ := ℓ)
  change (w (blackSlot (i := i) (ν := ν)) : ℕ) < N₀ + 1
  have : (w (blackSlot (i := i) (ν := ν)) : ℕ) ≠ N₀ + 1 := fun h => hne (Fin.ext h)
  omega

/-- Reduced words ending with the crossing `s_{N₀}` whenever the permutation has a descent at
`N₀`. -/
def lastCrossingWord (w : Perm (Fin m)) : List ℕ :=
  if w (blackSlot (i := i) (ν := ν)) < w (redSlot (i := i) (ν := ν)) then
    canWord m (w * sadj m N₀) ++ [N₀]
  else canWord m w

omit [DecidableEq I] in
theorem lastCrossingWord_spec (w : Perm (Fin m)) :
    IsReduced m (lastCrossingWord (i := i) (ν := ν) w) ∧
      wordProd m (lastCrossingWord (i := i) (ν := ν) w) = w := by
  unfold lastCrossingWord
  split_ifs with h
  · have hm := card_stendhalWeight_addRed_addBlack (i := i) (ν := ν) (ℓ := ℓ)
    have hlt : N₀ + 1 < m := by omega
    have hw : wordProd m (canWord m (w * sadj m N₀) ++ [N₀]) = w := by
      rw [wordProd_append, wordProd_canWord, wordProd_singleton, mul_assoc, TypeA.sadj_mul_self,
        mul_one]
    refine ⟨(isReduced_iff_length_le ?_).2 ?_, hw⟩
    · exact validWord_append.2 ⟨validWord_canWord m _, validWord_cons.2 ⟨hlt, validWord_nil m⟩⟩
    · rw [hw, List.length_append, length_canWord, List.length_singleton]
      exact (length_mul_sadj_of_gt hlt h).le
  · exact ⟨isReduced_canWord m w, wordProd_canWord m w⟩

end Combinatorics

end Categorification.Stendhal
