/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.WeakOrder

/-!
# Exits of a red-black permutation

Fix `τ : Equiv.Perm (Fin m)`, a set `R` of red strands and two consecutive red strands
`q < p` that cross in `τ`. An *exit* is a permutation `e` below `τ` in the left weak order,
with no crossing of two red strands, in which `q` and `p` end next to each other
(`e p = e q + 1`). These are the frames used in the proof of Webster, arXiv:1309.3796v2,
Lemma 6.5, to factor a red-red crossing out of a diagram for `τ`.

We show that exits exist and that any two exits are connected by two kinds of moves:
*squares*, `e ↦ s_j e` at an ascent `j` away from the values of `q` and `p`, and *hexagons*,
`e ↦ s_x s_{x+1} e` with `x = e q`, moving the strand just above `p` below `q`.

## Main definitions

* `TypeA.classPerm c` : the permutation ordering the points by the value of `c`, then by
  position.
* `TypeA.IsExit`, `TypeA.ExitMove`, `TypeA.ExitRel`.

## Main results

* `TypeA.exists_isExit` : exits exist.
* `TypeA.exitRel_connected` : any two exits are connected by squares and hexagons.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

section Rank

variable {α : Type*} [LinearOrder α] (key : Fin m → α)

/-- The number of points whose key is smaller than that of `s`. -/
def rankNat (s : Fin m) : ℕ := (Finset.univ.filter fun t => key t < key s).card

theorem rankNat_lt (s : Fin m) : rankNat key s < m := by
  refine lt_of_lt_of_le (Finset.card_lt_card (s := _) (t := Finset.univ) ?_) (by simp)
  exact Finset.ssubset_iff_of_subset (Finset.subset_univ _) |>.2 ⟨s, by simp, by simp⟩

theorem rankNat_lt_rankNat {a b : Fin m} (h : key a < key b) : rankNat key a < rankNat key b := by
  refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨a, by simp [h], by simp⟩)
  intro t ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  exact ht.trans h

/-- Two points with the same keys below them have the same rank. -/
theorem rankNat_eq_of_iff {β : Type*} [LinearOrder β] {key' : Fin m → β} {s s' : Fin m}
    (h : ∀ t, key t < key s ↔ key' t < key' s') : rankNat key s = rankNat key' s' := by
  unfold rankNat
  congr 1
  ext t
  simp [h t]

/-- If no key lies strictly between those of `q` and `p`, the rank goes up by one. -/
theorem rankNat_succ (hkey : Function.Injective key) {q p : Fin m} (hqp : key q < key p)
    (h : ∀ t, key q < key t → key p ≤ key t) : rankNat key p = rankNat key q + 1 := by
  unfold rankNat
  rw [← Finset.card_insert_of_notMem (a := q) (by simp)]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro ht
    rcases lt_trichotomy (key t) (key q) with h1 | h1 | h1
    · exact Or.inr h1
    · exact Or.inl (hkey h1)
    · exact absurd (h t h1) (not_le.2 ht)
  · rintro (rfl | ht)
    · exact hqp
    · exact ht.trans hqp

variable {key}

/-- Ranking the points of `Fin m` by an injective key. -/
noncomputable def rankPerm (hkey : Function.Injective key) : Perm (Fin m) :=
  Equiv.ofBijective (fun s => ⟨rankNat key s, rankNat_lt key s⟩) <| by
    refine Finite.injective_iff_bijective.1 fun a b h => ?_
    simp only [Fin.mk.injEq] at h
    by_contra hab
    rcases lt_or_gt_of_ne (hkey.ne hab) with h' | h'
    · exact absurd h (rankNat_lt_rankNat key h').ne
    · exact absurd h (rankNat_lt_rankNat key h').ne'

theorem rankPerm_val (hkey : Function.Injective key) (s : Fin m) :
    (rankPerm hkey s : ℕ) = rankNat key s := rfl

theorem rankPerm_lt_iff (hkey : Function.Injective key) {a b : Fin m} :
    rankPerm hkey a < rankPerm hkey b ↔ key a < key b := by
  refine ⟨fun h => ?_, fun h => rankNat_lt_rankNat key h⟩
  by_contra h'
  rcases (not_lt.1 h').lt_or_eq with h'' | h''
  · exact absurd (rankNat_lt_rankNat key h'') (not_lt.2 (le_of_lt h))
  · exact absurd (hkey h'') (by rintro rfl; exact lt_irrefl _ h)

end Rank


section ClassPerm

/-- The key ordering points by the value of `c`, then by position. -/
def classKey (c : Fin m → ℕ) (s : Fin m) : Lex (ℕ × Fin m) := toLex (c s, s)

theorem classKey_injective (c : Fin m → ℕ) : Function.Injective (classKey c) :=
  fun _ _ h => congrArg Prod.snd (toLex.injective h)

theorem classKey_lt_iff (c : Fin m → ℕ) {a b : Fin m} :
    classKey c a < classKey c b ↔ c a < c b ∨ c a = c b ∧ a < b :=
  Prod.Lex.toLex_lt_toLex

/-- The permutation sending the points in order of `c`, ties broken by position, to
`0, 1, …, m - 1`. -/
noncomputable def classPerm (c : Fin m → ℕ) : Perm (Fin m) := rankPerm (classKey_injective c)

theorem classPerm_val (c : Fin m → ℕ) (s : Fin m) :
    (classPerm c s : ℕ) = rankNat (classKey c) s := rfl

theorem classPerm_lt_iff (c : Fin m → ℕ) {a b : Fin m} :
    classPerm c a < classPerm c b ↔ c a < c b ∨ c a = c b ∧ a < b := by
  rw [classPerm, rankPerm_lt_iff, classKey_lt_iff]

theorem mem_invSet_classPerm (c : Fin m → ℕ) {a b : Fin m} :
    (a, b) ∈ invSet m (classPerm c) ↔ a < b ∧ c b < c a := by
  rw [mem_invSet, classPerm_lt_iff]
  constructor
  · rintro ⟨hab, h | ⟨-, h⟩⟩
    · exact ⟨hab, h⟩
    · exact absurd hab (lt_asymm h)
  · rintro ⟨hab, h⟩
    exact ⟨hab, Or.inl h⟩

/-- The inversions of a class permutation are inversions of every permutation compatible with
the classes. -/
theorem invSet_classPerm_subset (c : Fin m → ℕ) {w : Perm (Fin m)}
    (h : ∀ a b, a < b → c b < c a → w b < w a) : invSet m (classPerm c) ⊆ invSet m w := by
  intro ⟨a, b⟩ hab
  rw [mem_invSet_classPerm] at hab
  exact mem_invSet.2 ⟨hab.1, h a b hab.1 hab.2⟩

/-- Consecutive values: if `c q < c p` and no other point has class in `[c q, c p]`. -/
theorem classPerm_succ (c : Fin m → ℕ) {q p : Fin m} (hqp : c q < c p)
    (h : ∀ t, t ≠ q → t ≠ p → c t < c q ∨ c p < c t) :
    (classPerm c p : ℕ) = classPerm c q + 1 := by
  rw [classPerm_val, classPerm_val]
  refine rankNat_succ _ (classKey_injective c) ((classKey_lt_iff c).2 (Or.inl hqp)) fun t ht => ?_
  rw [classKey_lt_iff] at ht
  by_cases htq : t = q
  · subst htq; simp at ht
  by_cases htp : t = p
  · subst htp; exact le_refl _
  refine le_of_lt ((classKey_lt_iff c).2 (Or.inl ?_))
  rcases h t htq htp with h' | h'
  · omega
  · exact h'

/-- Equal sets of keys below give equal values. -/
theorem classPerm_val_eq (c c' : Fin m → ℕ) {s s' : Fin m}
    (h : ∀ t, (c t < c s ∨ c t = c s ∧ t < s) ↔ (c' t < c' s' ∨ c' t = c' s' ∧ t < s')) :
    (classPerm c s : ℕ) = classPerm c' s' := by
  rw [classPerm_val, classPerm_val]
  exact rankNat_eq_of_iff _ fun t => by rw [classKey_lt_iff, classKey_lt_iff]; exact h t

end ClassPerm

section Exits

variable (τ : Perm (Fin m)) (R : Finset (Fin m)) (q p : Fin m)

/-- An exit of `τ` for the red strands `q, p`: a permutation below `τ` in the left weak order,
with no crossing of two red strands, in which `q` and `p` end next to each other. -/
structure IsExit (e : Perm (Fin m)) : Prop where
  redFree : ∀ a b, (a, b) ∈ invSet m e → ¬ (a ∈ R ∧ b ∈ R)
  adj : (e p : ℕ) = e q + 1
  le : invSet m e ⊆ invSet m τ

/-- The two moves between exits. A square multiplies by `s_j` at an ascent away from the
values of `q` and `p`; a hexagon moves the strand ending just above `p` below `q`. -/
inductive ExitMove : Perm (Fin m) → Perm (Fin m) → Prop
  | square (e : Perm (Fin m)) (j : ℕ) (hj : j + 1 < m)
      (hfar : j + 1 < (e q : ℕ) ∨ (e q : ℕ) + 1 < j)
      (hlt : e⁻¹ ⟨j, by omega⟩ < e⁻¹ ⟨j + 1, hj⟩) : ExitMove e (sadj m j * e)
  | hexagon (e : Perm (Fin m)) (hx : (e q : ℕ) + 2 < m) :
      ExitMove e (sadj m (e q) * sadj m (e q + 1) * e)

/-- A move between two exits. -/
def ExitRel (e e' : Perm (Fin m)) : Prop :=
  IsExit τ R q p e ∧ IsExit τ R q p e' ∧ ExitMove q e e'

variable {τ R q p}

/-- An exit determines the inversions removed below it: comparable exits whose inversion sets
differ away from `q` and `p` are connected by squares. -/
theorem eqvGen_exitRel_of_invSet_subset {e e' : Perm (Fin m)} (he : IsExit τ R q p e)
    (he' : IsExit τ R q p e') (hsub : invSet m e ⊆ invSet m e')
    (havoid : ∀ a b, (a, b) ∈ invSet m e' → (a, b) ∉ invSet m e →
      a ≠ q ∧ a ≠ p ∧ b ≠ q ∧ b ≠ p) :
    Relation.EqvGen (ExitRel τ R q p) e e' := by
  induction hn : (invSet m e' \ invSet m e).card using Nat.strong_induction_on
    generalizing e' with
  | _ n ih =>
    by_cases hne : e' = e
    · subst hne; exact Relation.EqvGen.refl _
    obtain ⟨k, hk, -, ha, hP, hins, hsub', -⟩ := exists_peel hsub hne
    have hPmem : (e'⁻¹ ⟨k + 1, hk⟩, e'⁻¹ ⟨k, by omega⟩) ∈ invSet m e' := by
      rw [hins]; exact Finset.mem_insert_self _ _
    obtain ⟨h1, h2, h3, h4⟩ := havoid _ _ hPmem hP
    have hne1 : ∀ s, e'⁻¹ ⟨k, by omega⟩ ≠ s → (e' s : ℕ) ≠ k := fun s hs h =>
      hs (by rw [show (⟨k, by omega⟩ : Fin m) = e' s from Fin.ext h.symm]; simp)
    have hne2 : ∀ s, e'⁻¹ ⟨k + 1, hk⟩ ≠ s → (e' s : ℕ) ≠ k + 1 := fun s hs h =>
      hs (by rw [show (⟨k + 1, hk⟩ : Fin m) = e' s from Fin.ext h.symm]; simp)
    have hq1 := hne1 q h3
    have hq2 := hne2 q h1
    have hp1 := hne1 p h4
    have hp2 := hne2 p h2
    set e'' := sadj m k * e' with he''
    have hsub'' : invSet m e'' ⊆ invSet m e' := by rw [hins]; exact Finset.subset_insert _ _
    have heq : ∀ s, (e' s : ℕ) ≠ k → (e' s : ℕ) ≠ k + 1 → e'' s = e' s := fun s a b => by
      rw [he'', Perm.mul_apply, sadj_apply_of_ne _ a b]
    have hex : IsExit τ R q p e'' :=
      ⟨fun a b hab => he'.redFree a b (hsub'' hab),
        by rw [heq q hq1 hq2, heq p hp1 hp2]; exact he'.adj, hsub''.trans he'.le⟩
    have hback : sadj m k * e'' = e' := by rw [he'', ← mul_assoc, sadj_mul_self, one_mul]
    have hmove : ExitRel τ R q p e'' e' := by
      refine ⟨hex, he', ?_⟩
      have hm := ExitMove.square (q := q) e'' k hk (by
        rw [heq q hq1 hq2]; have := he'.adj; omega) ha
      rwa [hback] at hm
    have hPnot : (e'⁻¹ ⟨k + 1, hk⟩, e'⁻¹ ⟨k, by omega⟩) ∉ invSet m e'' := by
      rw [mem_invSet]
      have hc : ∀ x, e' (e'⁻¹ x) = x := fun x => by
        rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
      simp only [he'', Perm.mul_apply, hc, sadj_apply_left hk,
        sadj_apply_right hk, Fin.mk_lt_mk]
      omega
    have hlt : (invSet m e'' \ invSet m e).card < n := by
      rw [← hn]
      refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2
        ⟨(e'⁻¹ ⟨k + 1, hk⟩, e'⁻¹ ⟨k, by omega⟩), ?_, ?_⟩)
      · exact Finset.sdiff_subset_sdiff hsub'' le_rfl
      · exact Finset.mem_sdiff.2 ⟨hPmem, hP⟩
      · exact fun h => hPnot (Finset.mem_sdiff.1 h).1
    refine Relation.EqvGen.trans _ _ _ (ih _ hlt hex hsub' (fun a b hab hab' =>
      havoid a b (hsub'' hab) hab') rfl) (Relation.EqvGen.rel _ _ hmove)

end Exits

end Categorification.TypeA
