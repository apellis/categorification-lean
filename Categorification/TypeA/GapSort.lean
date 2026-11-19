/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Inversions

/-!
# Length-additive factorizations in the symmetric group

A factorization `w = τ⁻¹ * (τ * w)` is length additive when every pair of positions whose
order `τ` reverses is also crossed by `w`. We use this to slide two strands that are adjacent
at the bottom of a permutation diagram together at the top, through an intermediate
permutation: the strands between them at the top are moved out of the gap, those coming from
the left to the left and the others to the right. This is the reduction used in the proof of
Webster, *Knot invariants and higher representation theory*, arXiv:1309.3796v3, Prop. 4.21,
where a diagram passing through a violated loading is factored through a loading in which two
red strands are adjacent.

## Main results

* `TypeA.invCount_mul_of_cross` and `TypeA.length_eq_add_of_cross` : length additivity of
  `w = τ⁻¹ * (τ * w)` when every pair reversed by `τ` is crossed by `w`.
* `TypeA.IsReduced.append_of_length_eq` : concatenating reduced words of a length-additive
  factorization gives a reduced word.
* `TypeA.exists_perm_lt_iff` : sorting by an injective key.
* `TypeA.exists_gapSort` : for `p = w i < q = w (i + 1)`, a permutation `τ` making `p` and `q`
  adjacent, length additive for `w`, fixing the order of all positions outside the gap.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

/-- If every pair of positions whose order `τ` reverses is crossed by `w`, then the inversions
of `w` split into those of `τ * w` and those of `τ⁻¹`. -/
theorem invCount_mul_of_cross (w τ : Perm (Fin m))
    (h : ∀ X Y, Y < X → τ X < τ Y → w⁻¹ X < w⁻¹ Y) :
    invCount m w = invCount m τ⁻¹ + invCount m (τ * w) := by
  set v := τ * w with hv
  have hw : w = τ⁻¹ * v := by rw [hv, ← mul_assoc, inv_mul_cancel, one_mul]
  -- the map from inversions of `τ⁻¹` to the remaining inversions of `w`
  let f : Fin m × Fin m ↪ Fin m × Fin m :=
    ⟨fun p => (v⁻¹ p.1, v⁻¹ p.2), fun p q hpq => by
      simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at hpq
      exact Prod.ext hpq.1 hpq.2⟩
  have hsplit : invSet m w = invSet m v ∪ (invSet m τ⁻¹).map f := by
    ext ⟨a, b⟩
    simp only [Finset.mem_union, Finset.mem_map, mem_invSet, hw, Perm.mul_apply]
    constructor
    · rintro ⟨hab, hba⟩
      rcases lt_or_gt_of_ne (show v a ≠ v b from fun e => hab.ne (v.injective e)) with h' | h'
      · right
        exact ⟨(v a, v b), ⟨h', hba⟩, by simp [f]⟩
      · left; exact ⟨hab, h'⟩
    · rintro (⟨hab, hba⟩ | ⟨⟨x, y⟩, ⟨hxy, hyx⟩, he⟩)
      · refine ⟨hab, ?_⟩
        -- the pair `(v b, v a)` is crossed by `v`; it is not reversed by `τ⁻¹`
        rcases lt_or_gt_of_ne (show τ⁻¹ (v a) ≠ τ⁻¹ (v b) from
          fun e => hab.ne (v.injective (τ⁻¹.injective e))) with h' | h'
        · exfalso
          have := h (τ⁻¹ (v b)) (τ⁻¹ (v a)) h' (by simpa using hba)
          simp [hw] at this
          exact absurd hab (not_lt.2 this.le)
        · exact h'
      · simp only [f] at he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨?_, by simpa using hyx⟩
        have := h (τ⁻¹ x) (τ⁻¹ y) (by simpa using hyx) (by simpa using hxy)
        simpa [hw] using this
  have hdisj : Disjoint (invSet m v) ((invSet m τ⁻¹).map f) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h₁ h₂
    simp only [mem_invSet, Finset.mem_map] at h₁ h₂
    obtain ⟨⟨x, y⟩, ⟨hxy, -⟩, he⟩ := h₂
    simp only [f] at he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    simp at h₁
    exact lt_asymm hxy h₁.2
  rw [invCount, hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_map, add_comm]
  rfl

/-- Length additivity of `w = τ⁻¹ * (τ * w)` when every pair reversed by `τ` is crossed by
`w`. -/
theorem length_eq_add_of_cross (w τ : Perm (Fin m))
    (h : ∀ X Y, Y < X → τ X < τ Y → w⁻¹ X < w⁻¹ Y) :
    length m w = length m τ + length m (τ * w) := by
  rw [length_eq_invCount, length_eq_invCount, length_eq_invCount,
    invCount_mul_of_cross w τ h, ← length_eq_invCount, length_inv, length_eq_invCount]

/-- Concatenating reduced words of a length-additive factorization gives a reduced word. -/
theorem IsReduced.append_of_length_eq {α β : List ℕ} (hα : IsReduced m α)
    (hβ : IsReduced m β)
    (h : length m (wordProd m (α ++ β)) = length m (wordProd m α) + length m (wordProd m β)) :
    IsReduced m (α ++ β) :=
  ⟨validWord_append.2 ⟨hα.1, hβ.1⟩, by rw [List.length_append, hα.2, hβ.2, h]⟩

/-- Sorting by an injective key: a permutation ordering positions as the key does. -/
theorem exists_perm_lt_iff (key : Fin m → ℕ) (hkey : Function.Injective key) :
    ∃ τ : Perm (Fin m), ∀ x y, τ x < τ y ↔ key x < key y := by
  have hs : StrictMono (key ∘ Tuple.sort key) :=
    (Tuple.monotone_sort key).strictMono_of_injective (hkey.comp (Tuple.sort key).injective)
  refine ⟨(Tuple.sort key)⁻¹, fun x y => ?_⟩
  rw [← hs.lt_iff_lt]
  simp

/-- The group of a top position in the gap sort of `w` around the bottom positions `i`,
`i + 1` with `p = w i`, `q = w (i + 1)`: positions left of `p`, gap strands coming from the
left, `p`, `q`, the other gap strands, positions right of `q`. -/
private def gapGroup (p q i : ℕ) (X wX : ℕ) : ℕ :=
  if X < p then 0 else if X = p then 2 else if X < q then (if wX < i then 1 else 4)
  else if X = q then 3 else 5

private theorem gapGroup_cases (p q i X wX : ℕ) :
    (X < p ∧ gapGroup p q i X wX = 0) ∨ (X = p ∧ gapGroup p q i X wX = 2) ∨
      (p < X ∧ X < q ∧ wX < i ∧ gapGroup p q i X wX = 1) ∨
      (p < X ∧ X < q ∧ i ≤ wX ∧ gapGroup p q i X wX = 4) ∨
      (p < X ∧ X = q ∧ gapGroup p q i X wX = 3) ∨
      (p < X ∧ q < X ∧ gapGroup p q i X wX = 5) := by
  unfold gapGroup; split_ifs <;> omega

private theorem key_lt_iff {m g g' x y : ℕ} (hx : x < m) (hy : y < m) :
    g * m + x < g' * m + y ↔ g < g' ∨ (g = g' ∧ x < y) := by
  rcases lt_trichotomy g g' with h | rfl | h
  · have : (g + 1) * m ≤ g' * m := Nat.mul_le_mul_right _ h
    rw [add_mul, one_mul] at this
    exact ⟨fun _ => Or.inl h, fun _ => by omega⟩
  · omega
  · have : (g' + 1) * m ≤ g * m := Nat.mul_le_mul_right _ h
    rw [add_mul, one_mul] at this
    constructor
    · intro; omega
    · rintro (h' | ⟨rfl, -⟩) <;> omega

/-- The gap sort: for `w i < w (i + 1)` there is `τ` with `τ (w i) + 1 = τ (w (i + 1))`, such
that `w = τ⁻¹ * (τ * w)` is length additive and `τ` preserves the order of positions outside
the open gap between `w i` and `w (i + 1)`. -/
theorem exists_gapSort (w : Perm (Fin m)) (i : Fin m) (i' : Fin m) (hi : (i' : ℕ) = i + 1)
    (hpq : w i < w i') :
    ∃ τ : Perm (Fin m), (τ (w i) : ℕ) + 1 = τ (w i') ∧
      length m w = length m τ + length m (τ * w) ∧
      (∀ X Y, (X ≤ w i ∨ w i' ≤ X) → (Y ≤ w i ∨ w i' ≤ Y) → (τ X < τ Y ↔ X < Y)) ∧
      (∀ h : 0 < m, (0 : ℕ) < w i → τ ⟨0, h⟩ = ⟨0, h⟩) := by
  let key : Fin m → ℕ := fun X => gapGroup (w i) (w i') i X (w⁻¹ X) * m + X
  have hX (X : Fin m) : (X : ℕ) < m := X.2
  have hkey : Function.Injective key := by
    intro X Y hXY
    have hX := X.2; have hY := Y.2
    have h1 := Nat.div_add_mod' (key X) m
    simp only [key] at hXY
    apply Fin.ext
    have := congrArg (· % m) hXY
    simp only [Nat.mul_add_mod_of_lt hX, Nat.mul_add_mod_of_lt hY] at this
    exact this
  obtain ⟨τ, hτ⟩ := exists_perm_lt_iff key hkey
  have hwp : w⁻¹ (w i) = i := by simp
  have hwq : w⁻¹ (w i') = i' := by simp
  have hpq' : (w i : ℕ) < w i' := hpq
  -- a position is `p` (resp. `q`) iff it comes from `i` (resp. `i + 1`)
  have hZ : ∀ Z : Fin m, ((Z : ℕ) = w i ↔ (w⁻¹ Z : ℕ) = i) ∧
      ((Z : ℕ) = w i' ↔ (w⁻¹ Z : ℕ) = i + 1) := by
    intro Z
    rw [← hi, ← Fin.ext_iff, ← Fin.ext_iff, ← Fin.ext_iff, ← Fin.ext_iff,
      Perm.inv_eq_iff_eq, Perm.inv_eq_iff_eq]
    exact ⟨Iff.rfl, Iff.rfl⟩
  have hk : ∀ X Y : Fin m, key X < key Y ↔
      gapGroup (w i) (w i') i X (w⁻¹ X) < gapGroup (w i) (w i') i Y (w⁻¹ Y) ∨
        (gapGroup (w i) (w i') i X (w⁻¹ X) = gapGroup (w i) (w i') i Y (w⁻¹ Y) ∧
          (X : ℕ) < Y) :=
    fun X Y => key_lt_iff X.2 Y.2
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · -- nothing has key strictly between those of `p` and `q`
    have hlt : τ (w i) < τ (w i') := by
      rw [hτ, hk]
      have h₁ := gapGroup_cases (w i) (w i') i (w i) (w⁻¹ (w i))
      have h₂ := gapGroup_cases (w i) (w i') i (w i') (w⁻¹ (w i'))
      generalize gapGroup (w i) (w i') i (w i) (w⁻¹ (w i)) = a at *
      generalize gapGroup (w i) (w i') i (w i') (w⁻¹ (w i')) = b at *
      omega
    by_contra hne
    have hlt' : (τ (w i) : ℕ) + 1 < τ (w i') := by
      have := Fin.lt_def.1 hlt; omega
    obtain ⟨Z, hZ'⟩ : ∃ Z : Fin m, (τ Z : ℕ) = τ (w i) + 1 :=
      ⟨τ.symm ⟨τ (w i) + 1, by omega⟩, by simp⟩
    have h₁ : key (w i) < key Z := (hτ _ _).1 (by rw [Fin.lt_def, hZ']; omega)
    have h₂ : key Z < key (w i') := (hτ _ _).1 (by rw [Fin.lt_def, hZ']; omega)
    rw [hk] at h₁ h₂
    have c₁ := gapGroup_cases (w i) (w i') i (w i) (w⁻¹ (w i))
    have c₂ := gapGroup_cases (w i) (w i') i (w i') (w⁻¹ (w i'))
    have c₃ := gapGroup_cases (w i) (w i') i Z (w⁻¹ Z)
    generalize gapGroup (w i) (w i') i (w i) (w⁻¹ (w i)) = a at *
    generalize gapGroup (w i) (w i') i (w i') (w⁻¹ (w i')) = b at *
    generalize gapGroup (w i) (w i') i Z (w⁻¹ Z) = c at *
    omega
  · apply length_eq_add_of_cross
    intro X Y hYX hτXY
    rw [hτ, hk] at hτXY
    have hYX' : (Y : ℕ) < X := hYX
    have hne : (w⁻¹ X : ℕ) ≠ w⁻¹ Y := fun e =>
      hYX.ne (w⁻¹.injective (Fin.ext e)).symm
    have hXZ := hZ X; have hYZ := hZ Y
    have c₁ := gapGroup_cases (w i) (w i') i X (w⁻¹ X)
    have c₂ := gapGroup_cases (w i) (w i') i Y (w⁻¹ Y)
    generalize gapGroup (w i) (w i') i X (w⁻¹ X) = a at *
    generalize gapGroup (w i) (w i') i Y (w⁻¹ Y) = b at *
    rw [Fin.lt_def]
    omega
  · intro X Y hX' hY'
    rw [hτ, hk, Fin.lt_def]
    rw [Fin.le_def, Fin.le_def] at hX' hY'
    have c₁ := gapGroup_cases (w i) (w i') i X (w⁻¹ X)
    have c₂ := gapGroup_cases (w i) (w i') i Y (w⁻¹ Y)
    generalize gapGroup (w i) (w i') i X (w⁻¹ X) = a at *
    generalize gapGroup (w i) (w i') i Y (w⁻¹ Y) = b at *
    omega
  · intro h h0
    by_contra hne
    obtain ⟨Z, hZ0⟩ : ∃ Z : Fin m, τ Z = ⟨0, h⟩ := ⟨τ.symm ⟨0, h⟩, by simp⟩
    have hZ : Z ≠ ⟨0, h⟩ := fun e => hne (e ▸ hZ0)
    have hlt : τ Z < τ ⟨0, h⟩ := by
      rw [hZ0, Fin.lt_def]
      exact Nat.pos_of_ne_zero fun e => hne (Fin.ext e)
    rw [hτ, hk] at hlt
    have hZv : (Z : ℕ) ≠ 0 := fun e => hZ (Fin.ext e)
    have c₁ := gapGroup_cases (w i) (w i') i Z (w⁻¹ Z)
    have c₂ := gapGroup_cases (w i) (w i') i 0 (w⁻¹ ⟨0, h⟩)
    generalize gapGroup (w i) (w i') i Z (w⁻¹ Z) = a at *
    simp only [] at hlt
    generalize gapGroup (w i) (w i') i 0 (w⁻¹ ⟨0, h⟩) = b at *
    omega

end Categorification.TypeA
