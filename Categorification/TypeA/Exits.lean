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


section SetPerm

variable (τ : Perm (Fin m)) (R : Finset (Fin m)) (q p : Fin m)

/-- The class function of `A`: the points of `A`, then `q`, then `p`, then the rest. -/
def setClass (A : Finset (Fin m)) (s : Fin m) : ℕ :=
  if s ∈ A then 0 else if s = q then 1 else if s = p then 2 else 4

/-- The permutation listing the points of `A`, then `q`, then `p`, then the rest. -/
noncomputable def setPerm (A : Finset (Fin m)) : Perm (Fin m) := classPerm (setClass q p A)

/-- A pair that may not cross in an exit: either it does not cross in `τ` or both strands are
red. The pair `(q, p)` is excluded. -/
def Bad (u v : Fin m) : Prop := ((u, v) ∉ invSet m τ ∨ (u ∈ R ∧ v ∈ R)) ∧ ¬ (u = q ∧ v = p)

/-- `A` lists the strands to the left of `q` in an exit: it avoids `q` and `p` and is closed
under bad predecessors of its points, of `q` and of `p`. -/
structure IsValid (A : Finset (Fin m)) : Prop where
  q_notMem : q ∉ A
  p_notMem : p ∉ A
  closed : ∀ u v, u < v → Bad τ R q p u v → (v ∈ A ∨ v = q ∨ v = p) → u ∈ A

variable {τ R q p}

theorem setPerm_adj {A : Finset (Fin m)} (hqp : q ≠ p) (hq : q ∉ A) (hp : p ∉ A) :
    (setPerm q p A p : ℕ) = setPerm q p A q + 1 := by
  refine classPerm_succ _ (by simp [setClass, hq, hp, Ne.symm hqp]) fun t htq htp => ?_
  simp only [setClass, hq, hp, ite_true, ite_false, htq, htp]
  split_ifs <;> simp_all

theorem setPerm_inv_not_bad {A : Finset (Fin m)} (hA : IsValid τ R q p A) {a b : Fin m}
    (hab : (a, b) ∈ invSet m (setPerm q p A)) : ¬ Bad τ R q p a b := by
  rw [setPerm, mem_invSet_classPerm] at hab
  obtain ⟨hab, hc⟩ := hab
  intro hbad
  have hb : b ∈ A ∨ b = q ∨ b = p := by
    by_contra h
    simp only [not_or] at h
    simp only [setClass, h.1, h.2.1, h.2.2, ite_false] at hc
    split_ifs at hc <;> omega
  have ha := hA.closed a b hab hbad hb
  simp only [setClass, ha, ite_true] at hc
  omega

theorem isExit_setPerm (hqp : q < p) (hT : (q, p) ∈ invSet m τ) {A : Finset (Fin m)}
    (hA : IsValid τ R q p A) : IsExit τ R q p (setPerm q p A) := by
  refine ⟨fun a b hab hR => ?_, setPerm_adj hqp.ne hA.q_notMem hA.p_notMem, fun ⟨a, b⟩ hab => ?_⟩
  · refine setPerm_inv_not_bad hA hab ⟨Or.inr hR, ?_⟩
    rintro ⟨rfl, rfl⟩
    rw [setPerm, mem_invSet_classPerm] at hab
    simp [setClass, hA.q_notMem, hA.p_notMem, hqp.ne'] at hab
  · by_contra h
    refine setPerm_inv_not_bad hA hab ⟨Or.inl h, ?_⟩
    rintro ⟨rfl, rfl⟩
    exact h hT

theorem isValid_of_isExit {A : Finset (Fin m)} (hqp : q < p) (hq : q ∉ A) (hp : p ∉ A)
    (he : IsExit τ R q p (setPerm q p A)) : IsValid τ R q p A := by
  refine ⟨hq, hp, fun u v huv hbad hv => ?_⟩
  by_contra hu
  have hinv : (u, v) ∈ invSet m (setPerm q p A) := by
    rw [setPerm, mem_invSet_classPerm]
    refine ⟨huv, ?_⟩
    have hqp' := hqp.ne
    rcases hv with hv | rfl | rfl
    · have hvq : v ≠ q := fun h => hq (h ▸ hv)
      simp only [setClass, hv, hu, ite_true, ite_false]
      (try split_ifs) <;> omega
    · have : u ≠ p := fun h => absurd (h ▸ huv) (not_lt.2 hqp.le)
      simp only [setClass, hq, hu, ite_true, ite_false, huv.ne, this]
      omega
    · have : u ≠ q := fun h => hbad.2 ⟨h, rfl⟩
      simp only [setClass, hp, hu, hqp'.symm, ite_true, ite_false, huv.ne, this]
      omega
  rcases hbad.1 with h | h
  · exact h (he.le hinv)
  · exact he.redFree u v hinv h

theorem IsValid.inter {A A' : Finset (Fin m)} (hA : IsValid τ R q p A)
    (hA' : IsValid τ R q p A') : IsValid τ R q p (A ∩ A') := by
  refine ⟨fun h => hA.q_notMem (Finset.mem_inter.1 h).1,
    fun h => hA.p_notMem (Finset.mem_inter.1 h).1, fun u v huv hbad hv => ?_⟩
  simp only [Finset.mem_inter] at hv ⊢
  rcases hv with hv | hv
  · exact ⟨hA.closed u v huv hbad (Or.inl hv.1), hA'.closed u v huv hbad (Or.inl hv.2)⟩
  · exact ⟨hA.closed u v huv hbad (Or.inr hv), hA'.closed u v huv hbad (Or.inr hv)⟩

end SetPerm


section ClassMono

theorem invSet_classPerm_mono {c c' : Fin m → ℕ} (h : ∀ a b, a < b → c b < c a → c' b < c' a) :
    invSet m (classPerm c) ⊆ invSet m (classPerm c') :=
  invSet_classPerm_subset c fun a b hab hc =>
    (classPerm_lt_iff c').2 (Or.inl (h a b hab hc))

theorem invSet_classPerm_subset_union {c c' c'' : Fin m → ℕ}
    (h : ∀ a b, a < b → c b < c a → c' b < c' a ∨ c'' b < c'' a) :
    invSet m (classPerm c) ⊆ invSet m (classPerm c') ∪ invSet m (classPerm c'') := by
  intro ⟨a, b⟩ hab
  rw [mem_invSet_classPerm] at hab
  rw [Finset.mem_union, mem_invSet_classPerm, mem_invSet_classPerm]
  rcases h a b hab.1 hab.2 with h' | h'
  · exact Or.inl ⟨hab.1, h'⟩
  · exact Or.inr ⟨hab.1, h'⟩

end ClassMono

section LeftSet

variable {τ R q p}

/-- The strands ending below `q` in `e`. -/
def leftSet (q : Fin m) (e : Perm (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter fun s => e s < e q

/-- The classes of `setPerm (leftSet e)` read off from the values of `e`. -/
def valueClass (x v : ℕ) : ℕ := if v < x then 0 else if v = x then 1 else if v = x + 1 then 2 else 4

theorem setClass_leftSet {e : Perm (Fin m)} (he : IsExit τ R q p e) (s : Fin m) :
    setClass q p (leftSet q e) s = valueClass (e q) (e s) := by
  have hadj := he.adj
  have hqp : q ≠ p := fun h => by rw [h] at hadj; omega
  simp only [setClass, leftSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def,
    valueClass]
  by_cases h1 : s = q
  · subst h1; simp
  by_cases h2 : s = p
  · subst h2; simp [h1, hadj]
  have h3 : (e s : ℕ) ≠ e q := fun h => h1 (e.injective (Fin.ext h))
  have h4 : (e s : ℕ) ≠ e p := fun h => h2 (e.injective (Fin.ext h))
  simp only [h1, h2, ite_false]
  split_ifs <;> omega

theorem IsExit.leftSet_notMem_q {e : Perm (Fin m)} : q ∉ leftSet q e := by
  simp [leftSet]

theorem IsExit.leftSet_notMem_p {e : Perm (Fin m)} (he : IsExit τ R q p e) :
    p ∉ leftSet q e := by
  have := he.adj
  simp only [leftSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, not_lt]
  omega

theorem IsExit.invSet_setPerm_leftSet_subset {e : Perm (Fin m)} (he : IsExit τ R q p e) :
    invSet m (setPerm q p (leftSet q e)) ⊆ invSet m e := by
  refine invSet_classPerm_subset _ fun a b _ hc => ?_
  rw [setClass_leftSet he, setClass_leftSet he, valueClass, valueClass] at hc
  rw [Fin.lt_def]
  split_ifs at hc <;> omega

theorem IsExit.isExit_setPerm_leftSet (hqp : q < p) {e : Perm (Fin m)}
    (he : IsExit τ R q p e) : IsExit τ R q p (setPerm q p (leftSet q e)) :=
  ⟨fun a b hab => he.redFree a b (he.invSet_setPerm_leftSet_subset hab),
    setPerm_adj hqp.ne IsExit.leftSet_notMem_q he.leftSet_notMem_p,
    he.invSet_setPerm_leftSet_subset.trans he.le⟩

theorem IsExit.isValid_leftSet (hqp : q < p) {e : Perm (Fin m)} (he : IsExit τ R q p e) :
    IsValid τ R q p (leftSet q e) :=
  isValid_of_isExit hqp IsExit.leftSet_notMem_q he.leftSet_notMem_p
    (he.isExit_setPerm_leftSet hqp)

/-- Every exit is connected by squares to the exit listing the strands that end below `q`. -/
theorem IsExit.eqvGen_setPerm_leftSet (hqp : q < p) {e : Perm (Fin m)}
    (he : IsExit τ R q p e) :
    Relation.EqvGen (ExitRel τ R q p) (setPerm q p (leftSet q e)) e := by
  refine eqvGen_exitRel_of_invSet_subset (he.isExit_setPerm_leftSet hqp) he
    he.invSet_setPerm_leftSet_subset fun a b hab hab' => ?_
  rw [setPerm, mem_invSet_classPerm, setClass_leftSet he, setClass_leftSet he] at hab'
  have hab'' : a < b ∧ e b < e a := mem_invSet.1 hab
  have hlt : (e b : ℕ) < e a := hab''.2
  have hadj := he.adj
  have key : ¬ (valueClass (e q) (e b) < valueClass (e q) (e a)) := fun h => hab' ⟨hab''.1, h⟩
  have hv : (e a : ℕ) ≠ e q ∧ (e a : ℕ) ≠ e p ∧ (e b : ℕ) ≠ e q ∧ (e b : ℕ) ≠ e p := by
    simp only [valueClass] at key
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> apply key <;> split_ifs <;> omega
  exact ⟨fun h => hv.1 (by rw [h]), fun h => hv.2.1 (by rw [h]),
    fun h => hv.2.2.1 (by rw [h]), fun h => hv.2.2.2 (by rw [h])⟩

end LeftSet


section Hexagon

variable {τ R q p}

/-- The classes `B`, `q`, `p`, `β`, rest, numbered `0, …, 4`. -/
def hexClass (B : Finset (Fin m)) (q p β : Fin m) (s : Fin m) : ℕ :=
  if s ∈ B then 0 else if s = q then 1 else if s = p then 2 else if s = β then 3 else 4

/-- Merging the class of `β` into `B`. -/
def hexA (n : ℕ) : ℕ := if n = 3 then 0 else n

/-- Merging the class of `β` into the rest. -/
def hexB (n : ℕ) : ℕ := if n = 3 then 4 else n

/-- Moving the class of `β` below `q` and `p`. -/
def hexSwap (n : ℕ) : ℕ := if n = 1 then 2 else if n = 2 then 3 else if n = 3 then 1 else n

variable {A : Finset (Fin m)} {β : Fin m}

private structure HexData (A : Finset (Fin m)) (q p β : Fin m) : Prop where
  hq : q ∉ A
  hp : p ∉ A
  hβ : β ∈ A
  hqp : q ≠ p

private theorem hexClass_le (s : Fin m) : hexClass (A.erase β) q p β s ≤ 4 := by
  unfold hexClass; split_ifs <;> omega

private theorem hexClass_eq_one {s : Fin m} (hs : hexClass (A.erase β) q p β s = 1) : s = q := by
  unfold hexClass at hs; split_ifs at hs <;> simp_all

private theorem hexClass_eq_two {s : Fin m} (hs : hexClass (A.erase β) q p β s = 2) : s = p := by
  unfold hexClass at hs; split_ifs at hs <;> simp_all

private theorem hexClass_eq_three {s : Fin m} (hs : hexClass (A.erase β) q p β s = 3) : s = β := by
  unfold hexClass at hs; split_ifs at hs <;> simp_all

private theorem hexClass_other {s : Fin m} (hq : s ≠ q) (hp : s ≠ p) (hβ : s ≠ β) :
    hexClass (A.erase β) q p β s = 0 ∨ hexClass (A.erase β) q p β s = 4 := by
  unfold hexClass; split_ifs <;> simp_all

private theorem setClass_erase_hexB (s : Fin m) :
    setClass q p (A.erase β) s = hexB (hexClass (A.erase β) q p β s) := by
  unfold setClass hexClass hexB
  split_ifs <;> simp_all

namespace HexData

variable (h : HexData A q p β)
include h

private theorem βq : β ≠ q := fun e => h.hq (e ▸ h.hβ)
private theorem βp : β ≠ p := fun e => h.hp (e ▸ h.hβ)

private theorem c_q : hexClass (A.erase β) q p β q = 1 := by
  simp [hexClass, h.hq]

private theorem c_p : hexClass (A.erase β) q p β p = 2 := by
  simp [hexClass, h.hp, h.hqp.symm]

private theorem c_β : hexClass (A.erase β) q p β β = 3 := by
  simp [hexClass, h.βq, h.βp]

private theorem setClass_eq (s : Fin m) :
    setClass q p A s = hexA (hexClass (A.erase β) q p β s) := by
  unfold setClass hexClass hexA
  by_cases hs : s = β
  · subst hs; simp [h.hβ, h.βq, h.βp]
  simp only [Finset.mem_erase, hs, ne_eq, not_false_eq_true, true_and]
  split_ifs <;> simp_all

end HexData

/-- Removing the last strand of `A` that may be removed: the exits of `A` and of `A.erase β`
are connected by squares and one hexagon. -/
theorem eqvGen_setPerm_erase (hqp : q < p) (hT : (q, p) ∈ invSet m τ)
    (hA : IsValid τ R q p A) (hβ : β ∈ A) (hB : IsValid τ R q p (A.erase β)) :
    Relation.EqvGen (ExitRel τ R q p) (setPerm q p A) (setPerm q p (A.erase β)) := by
  have h : HexData A q p β := ⟨hA.q_notMem, hA.p_notMem, hβ, hqp.ne⟩
  set c := hexClass (A.erase β) q p β with hc
  have hσA : setPerm q p A = classPerm fun s => hexA (c s) := by
    rw [setPerm]; congr 1; funext s; exact h.setClass_eq s
  have hσB : setPerm q p (A.erase β) = classPerm fun s => hexB (c s) := by
    rw [setPerm]; congr 1; funext s; exact setClass_erase_hexB s
  have heA := isExit_setPerm hqp hT hA
  have heB := isExit_setPerm hqp hT hB
  rw [hσA] at heA ⊢
  rw [hσB] at heB ⊢
  set e1 := classPerm c with he1
  set e2 := classPerm fun s => hexSwap (c s) with he2
  have hcq : c q = 1 := h.c_q
  have hcp : c p = 2 := h.c_p
  have hcβ : c β = 3 := h.c_β
  have cle : ∀ t, c t ≤ 4 := hexClass_le
  have c1 : ∀ {t}, c t = 1 → t = q := hexClass_eq_one
  have c2 : ∀ {t}, c t = 2 → t = p := hexClass_eq_two
  have c3 : ∀ {t}, c t = 3 → t = β := hexClass_eq_three
  have cother : ∀ {t}, t ≠ q → t ≠ p → t ≠ β → c t = 0 ∨ c t = 4 := hexClass_other
  -- the two new exits
  have hexit : ∀ {w : Perm (Fin m)}, (w p : ℕ) = w q + 1 →
      invSet m w ⊆ invSet m (classPerm fun s => hexA (c s)) ∪
        invSet m (classPerm fun s => hexB (c s)) → IsExit τ R q p w := by
    intro w hadj hsub
    refine ⟨fun a b hab => ?_, hadj, fun x hx => ?_⟩
    · rcases Finset.mem_union.1 (hsub hab) with h' | h'
      · exact heA.redFree a b h'
      · exact heB.redFree a b h'
    · rcases Finset.mem_union.1 (hsub hx) with h' | h'
      · exact heA.le h'
      · exact heB.le h'
  have he1x : IsExit τ R q p e1 := by
    refine hexit (classPerm_succ c (by omega) fun t htq htp => ?_)
      (invSet_classPerm_subset_union fun a b _ hab => ?_)
    · have h1 : c t ≠ 1 := fun e => htq (c1 e)
      have h2 : c t ≠ 2 := fun e => htp (c2 e)
      have := cle t
      omega
    · have := cle a
      have := cle b
      simp only [hexA, hexB]
      split_ifs <;> omega
  have he2x : IsExit τ R q p e2 := by
    refine hexit (classPerm_succ _ (by simp [hcq, hcp, hexSwap]) fun t htq htp => ?_)
      (invSet_classPerm_subset_union fun a b _ hab => ?_)
    · have h1 : c t ≠ 1 := fun e => htq (c1 e)
      have h2 : c t ≠ 2 := fun e => htp (c2 e)
      have := cle t
      simp only [hcq, hcp, hexSwap]
      split_ifs <;> omega
    · have := cle a
      have := cle b
      simp only [hexA, hexB, hexSwap] at hab ⊢
      split_ifs at hab ⊢ <;> omega
  -- values
  set x : ℕ := (e1 q : ℕ) with hx
  have hx1 : (e1 p : ℕ) = x + 1 := he1x.adj
  have hx2 : (e1 β : ℕ) = x + 2 := by
    have : (e1 β : ℕ) = e1 p + 1 := classPerm_succ c (by omega) fun t htp htβ => by
      have h2 : c t ≠ 2 := fun e => htp (c2 e)
      have h3 : c t ≠ 3 := fun e => htβ (c3 e)
      have := cle t
      omega
    omega
  have hy0 : (e2 β : ℕ) = x := by
    refine (classPerm_val_eq _ _ fun t => ?_).symm
    rw [hcq, hcβ]
    have := cle t
    rcases (by omega : c t = 0 ∨ c t = 1 ∨ c t = 2 ∨ c t = 3 ∨ c t = 4) with
      e | e | e | e | e
    · simp [e, hexSwap]
    · rw [e, c1 e]; simp [hexSwap]
    · simp [e, hexSwap]
    · rw [e, c3 e]; simp [hexSwap]
    · simp [e, hexSwap]
  have hy1 : (e2 q : ℕ) = x + 1 := by
    rw [← hy0]
    refine classPerm_succ _ (by simp [hcq, hcβ, hexSwap]) fun t htβ htq => ?_
    have h1 : c t ≠ 1 := fun e => htq (c1 e)
    have h3 : c t ≠ 3 := fun e => htβ (c3 e)
    have := cle t
    simp only [hcq, hcβ, hexSwap]
    split_ifs <;> omega
  have hy2 : (e2 p : ℕ) = x + 2 := by rw [he2x.adj, hy1]
  have hoth : ∀ s, s ≠ q → s ≠ p → s ≠ β → (e2 s : ℕ) = e1 s := fun s hsq hsp hsβ => by
    refine classPerm_val_eq _ _ fun t => ?_
    have := cle t
    rcases cother hsq hsp hsβ with ev | ev <;>
    rcases (by omega : c t = 0 ∨ c t = 1 ∨ c t = 2 ∨ c t = 3 ∨ c t = 4) with
      e | e | e | e | e <;> simp [e, ev, hexSwap]
  have hxm : x + 2 < m := by rw [← hx2]; exact (e1 β).2
  have hmove : sadj m x * sadj m (x + 1) * e1 = e2 := by
    ext s
    rw [Perm.mul_apply, Perm.mul_apply, sadj_val_of_lt (by omega),
      sadj_val_of_lt (by omega : x + 1 + 1 < m)]
    by_cases hsq : s = q
    · subst hsq; rw [hy1, ← hx]; unfold swapNat; split_ifs <;> omega
    by_cases hsp : s = p
    · subst hsp; rw [hy2, hx1]; unfold swapNat; split_ifs <;> omega
    by_cases hsβ : s = β
    · subst hsβ; rw [hy0, hx2]; unfold swapNat; split_ifs <;> omega
    rw [hoth s hsq hsp hsβ]
    have n1 : (e1 s : ℕ) ≠ x := fun e => hsq (e1.injective (Fin.ext e))
    have n2 : (e1 s : ℕ) ≠ x + 1 := fun e => hsp (e1.injective (Fin.ext (e.trans hx1.symm)))
    have n3 : (e1 s : ℕ) ≠ x + 2 := fun e => hsβ (e1.injective (Fin.ext (e.trans hx2.symm)))
    have := swapNat_cases (x + 1) (e1 s)
    have := swapNat_cases x (swapNat (x + 1) (e1 s))
    omega
  have hhex : ExitRel τ R q p e1 e2 := by
    refine ⟨he1x, he2x, ?_⟩
    have := ExitMove.hexagon (q := q) e1 (by rw [← hx]; exact hxm)
    rwa [← hx, hmove] at this
  -- squares on either side
  have hsqA : Relation.EqvGen (ExitRel τ R q p) (classPerm fun s => hexA (c s)) e2 := by
    refine eqvGen_exitRel_of_invSet_subset heA he2x
      (invSet_classPerm_mono fun a b _ hab => ?_) fun a b hab hab' => ?_
    · have := cle a
      have := cle b
      simp only [hexA, hexSwap] at hab ⊢
      split_ifs at hab ⊢ <;> omega
    · rw [mem_invSet_classPerm] at hab hab'
      have hn : ¬ hexA (c b) < hexA (c a) := fun e => hab' ⟨hab.1, e⟩
      have := cle a
      have := cle b
      have key : c a ≠ 1 ∧ c a ≠ 2 ∧ c b ≠ 1 ∧ c b ≠ 2 := by
        have h2 := hab.2
        simp only [hexA, hexSwap] at hn h2
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e <;> rw [e] at hn h2 <;> split_ifs at hn h2 <;>
          omega
      exact ⟨fun e => key.1 (by rw [e, hcq]), fun e => key.2.1 (by rw [e, hcp]),
        fun e => key.2.2.1 (by rw [e, hcq]), fun e => key.2.2.2 (by rw [e, hcp])⟩
  have hsqB : Relation.EqvGen (ExitRel τ R q p) (classPerm fun s => hexB (c s)) e1 := by
    refine eqvGen_exitRel_of_invSet_subset heB he1x
      (invSet_classPerm_mono fun a b _ hab => ?_) fun a b hab hab' => ?_
    · have := cle a
      have := cle b
      simp only [hexB] at hab
      split_ifs at hab <;> omega
    · rw [mem_invSet_classPerm] at hab hab'
      have hn : ¬ hexB (c b) < hexB (c a) := fun e => hab' ⟨hab.1, e⟩
      have := cle a
      have := cle b
      have key : c a ≠ 1 ∧ c a ≠ 2 ∧ c b ≠ 1 ∧ c b ≠ 2 := by
        have h2 := hab.2
        simp only [hexB] at hn
        refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e <;> rw [e] at hn h2 <;> split_ifs at hn <;>
          omega
      exact ⟨fun e => key.1 (by rw [e, hcq]), fun e => key.2.1 (by rw [e, hcp]),
        fun e => key.2.2.1 (by rw [e, hcq]), fun e => key.2.2.2 (by rw [e, hcp])⟩
  exact hsqA.trans _ _ _ ((Relation.EqvGen.rel _ _ hhex).symm _ _ |>.trans _ _ _
    (hsqB.symm _ _))

end Hexagon

section Connected

variable {τ R q p}

theorem IsValid.erase_max {A A' : Finset (Fin m)} (hA : IsValid τ R q p A)
    (hA' : IsValid τ R q p A') (hne : (A \ A').Nonempty) :
    IsValid τ R q p (A.erase ((A \ A').max' hne)) := by
  have hβ := Finset.mem_sdiff.1 ((A \ A').max'_mem hne)
  refine ⟨fun h => hA.q_notMem (Finset.mem_of_mem_erase h),
    fun h => hA.p_notMem (Finset.mem_of_mem_erase h), fun u v huv hbad hv => ?_⟩
  have huA : u ∈ A :=
    hA.closed u v huv hbad (hv.imp_left Finset.mem_of_mem_erase)
  refine Finset.mem_erase.2 ⟨fun hu => ?_, huA⟩
  rcases hv with hv | hv
  · by_cases hvA' : v ∈ A'
    · exact hβ.2 (hu ▸ hA'.closed u v huv hbad (Or.inl hvA'))
    · have := (A \ A').le_max' v (Finset.mem_sdiff.2 ⟨Finset.mem_of_mem_erase hv, hvA'⟩)
      rw [← hu] at this
      exact absurd huv (not_lt.2 this)
  · exact hβ.2 (hu ▸ hA'.closed u v huv hbad (Or.inr hv))

/-- The exits attached to nested valid sets are connected. -/
theorem eqvGen_setPerm_of_subset (hqp : q < p) (hT : (q, p) ∈ invSet m τ)
    {A A' : Finset (Fin m)} (hA : IsValid τ R q p A) (hA' : IsValid τ R q p A')
    (hsub : A' ⊆ A) :
    Relation.EqvGen (ExitRel τ R q p) (setPerm q p A) (setPerm q p A') := by
  induction hn : (A \ A').card using Nat.strong_induction_on generalizing A with
  | _ n ih =>
    by_cases hne : (A \ A').Nonempty
    · have hβ := Finset.mem_sdiff.1 ((A \ A').max'_mem hne)
      have hB := hA.erase_max hA' hne
      have hBsub : A' ⊆ A.erase ((A \ A').max' hne) := fun x hx =>
        Finset.mem_erase.2 ⟨fun h => hβ.2 (h ▸ hx), hsub hx⟩
      have hcard : (A.erase ((A \ A').max' hne) \ A').card < n := by
        rw [← hn]
        refine Finset.card_lt_card (Finset.ssubset_iff_of_subset
          (Finset.sdiff_subset_sdiff (Finset.erase_subset _ _) le_rfl) |>.2
            ⟨_, (A \ A').max'_mem hne, fun h => ?_⟩)
        simp at h
      exact (eqvGen_setPerm_erase hqp hT hA hβ.1 hB).trans _ _ _
        (ih _ hcard hB hBsub rfl)
    · have : A = A' := Finset.Subset.antisymm
        (Finset.sdiff_eq_empty_iff_subset.1 (Finset.not_nonempty_iff_eq_empty.1 hne)) hsub
      subst this
      exact Relation.EqvGen.refl _

/-- **Connectivity of exits.** Any two exits are connected by square and hexagon moves. -/
theorem exitRel_connected (hqp : q < p) (hT : (q, p) ∈ invSet m τ) {e e' : Perm (Fin m)}
    (he : IsExit τ R q p e) (he' : IsExit τ R q p e') :
    Relation.EqvGen (ExitRel τ R q p) e e' := by
  have hL := he.isValid_leftSet hqp
  have hL' := he'.isValid_leftSet hqp
  have hI := hL.inter hL'
  exact ((he.eqvGen_setPerm_leftSet hqp).symm _ _).trans _ _ _
    ((eqvGen_setPerm_of_subset hqp hT hL hI Finset.inter_subset_left).trans _ _ _
      (((eqvGen_setPerm_of_subset hqp hT hL' hI Finset.inter_subset_right).symm _ _).trans
        _ _ _ (he'.eqvGen_setPerm_leftSet hqp)))

end Connected

section Existence

variable (τ R q p)

/-- `u` precedes `v` and the pair may not cross in an exit. -/
def Prec (u v : Fin m) : Prop := u < v ∧ Bad τ R q p u v

open Classical in
/-- The smallest valid set: the strands from which a chain of bad pairs leads to `q` or `p`. -/
noncomputable def minSet : Finset (Fin m) :=
  Finset.univ.filter fun s => s ≠ q ∧ s ≠ p ∧
    (Relation.TransGen (Prec τ R q p) s q ∨ Relation.TransGen (Prec τ R q p) s p)

variable {τ R q p}

theorem lt_of_transGen_prec {u v : Fin m} (h : Relation.TransGen (Prec τ R q p) u v) : u < v := by
  induction h with
  | single h => exact h.1
  | tail _ h ih => exact ih.trans h.1

theorem not_transGen_prec (hT : (q, p) ∈ invSet m τ)
    (hcons : ∀ t ∈ R, q < t → t < p → False) : ¬ Relation.TransGen (Prec τ R q p) q p := by
  have key : ∀ {v}, Relation.TransGen (Prec τ R q p) q v → v ≤ p → τ q < τ v := by
    intro v h
    induction h with
    | single h =>
      intro hv
      rcases h.2.1 with h' | h'
      · rw [mem_invSet] at h'
        exact lt_of_le_of_ne (not_lt.1 fun h'' => h' ⟨h.1, h''⟩)
          (fun e => h.1.ne (τ.injective e))
      · rcases hv.lt_or_eq with hv | rfl
        · exact (hcons _ h'.2 h.1 hv).elim
        · exact (h.2.2 ⟨rfl, rfl⟩).elim
    | tail h₁ h ih =>
      intro hv
      have hw := lt_of_transGen_prec h₁
      have := ih (h.1.le.trans hv)
      rcases h.2.1 with h' | h'
      · rw [mem_invSet] at h'
        exact this.trans (lt_of_le_of_ne (not_lt.1 fun h'' => h' ⟨h.1, h''⟩)
          (fun e => h.1.ne (τ.injective e)))
      · exact (hcons _ h'.1 hw (h.1.trans_le hv)).elim
  intro h
  exact absurd (key h le_rfl) (not_lt.2 (mem_invSet.1 hT).2.le)

theorem isValid_minSet (hqp : q < p) (hT : (q, p) ∈ invSet m τ)
    (hcons : ∀ t ∈ R, q < t → t < p → False) : IsValid τ R q p (minSet τ R q p) := by
  classical
  refine ⟨by simp [minSet], by simp [minSet], fun u v huv hbad hv => ?_⟩
  have hP : Prec τ R q p u v := ⟨huv, hbad⟩
  have hchain : Relation.TransGen (Prec τ R q p) u q ∨ Relation.TransGen (Prec τ R q p) u p := by
    rcases hv with hv | rfl | rfl
    · simp only [minSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact hv.2.2.imp (Relation.TransGen.head hP) (Relation.TransGen.head hP)
    · exact Or.inl (Relation.TransGen.single hP)
    · exact Or.inr (Relation.TransGen.single hP)
  simp only [minSet, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun hu => ?_, fun hu => ?_, hchain⟩
  · subst hu
    rcases hchain with h | h
    · exact lt_irrefl _ (lt_of_transGen_prec h)
    · exact not_transGen_prec hT hcons h
  · subst hu
    rcases hchain with h | h
    · exact absurd hqp (not_lt.2 (lt_of_transGen_prec h).le)
    · exact lt_irrefl _ (lt_of_transGen_prec h)

/-- **Existence of exits.** -/
theorem exists_isExit (hqp : q < p) (hT : (q, p) ∈ invSet m τ)
    (hcons : ∀ t ∈ R, q < t → t < p → False) : ∃ e, IsExit τ R q p e :=
  ⟨_, isExit_setPerm hqp hT (isValid_minSet hqp hT hcons)⟩

end Existence

end Categorification.TypeA
