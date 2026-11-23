/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Exits

/-!
# Permutations below `τ` that cross exactly one red pair

Fix `τ`, a set `R` of red strands and two red strands `q < p`. A permutation `v` is *swap-below*
if `invSet v ⊆ invSet τ` and the only red pair inverted by `v` is `(q, p)`. These are the
permutations `v` of a factorization `τ = u v` with `ℓ(u) + ℓ(v) = ℓ(τ)` in which `v` performs the
red crossing of `q` and `p` (Webster, arXiv:1309.3796v2, proof of Lemma 6.5).

Two swap-below permutations are connected by steps `v ↦ s_c v` through swap-below
permutations (`isSwapBelow_connected`). The proof moves every swap-below permutation down to
`s_{e q} e` for an exit `e` (`TypeA.IsExit`), and lifts the square and hexagon moves between
exits (`TypeA.exitRel_connected`).
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

theorem mem_invSet_pair {w : Perm (Fin m)} {a b : Fin m} :
    (a, b) ∈ invSet m w ↔ a < b ∧ w b < w a := mem_invSet

/-- Inversions of `s_k w` in terms of the values of `w`. -/
theorem mem_invSet_sadj_mul {k : ℕ} (hk : k + 1 < m) (w : Perm (Fin m)) (a b : Fin m) :
    (a, b) ∈ invSet m (sadj m k * w) ↔
      (a : ℕ) < b ∧ ((w b : ℕ) < w a ∧ ¬ ((w b : ℕ) = k ∧ (w a : ℕ) = k + 1) ∨
        ((w b : ℕ) = k + 1 ∧ (w a : ℕ) = k)) := by
  rw [mem_invSet_pair, Perm.mul_apply, Perm.mul_apply, Fin.lt_def, Fin.lt_def, sadj_val_of_lt hk,
    sadj_val_of_lt hk]
  have := swapNat_cases k (w a)
  have := swapNat_cases k (w b)
  generalize swapNat k (w a) = x at *
  generalize swapNat k (w b) = y at *
  omega

/-- A value where a function on `ℕ` drops, between two points where it drops overall. -/
theorem exists_drop (f : ℕ → ℕ) :
    ∀ d lo : ℕ, f (lo + d) < f lo → ∃ c, lo ≤ c ∧ c < lo + d ∧ f (c + 1) < f c := by
  intro d
  induction d with
  | zero => intro lo h; simp at h
  | succ d ih =>
    intro lo h
    by_cases h1 : f (lo + 1) < f lo
    · exact ⟨lo, le_rfl, by omega, h1⟩
    · obtain ⟨c, h2, h3, h4⟩ := ih (lo + 1) (by rw [show lo + 1 + d = lo + (d + 1) by omega]; omega)
      exact ⟨c, by omega, by omega, h4⟩

variable (τ : Perm (Fin m)) (R : Finset (Fin m)) (q p : Fin m)

/-- `v` lies below `τ` in the left weak order and inverts exactly one red pair, `(q, p)`. -/
structure IsSwapBelow (v : Perm (Fin m)) : Prop where
  le : invSet m v ⊆ invSet m τ
  red : ∀ s t, s ∈ R → t ∈ R → ((s, t) ∈ invSet m v ↔ s = q ∧ t = p)

/-- A step `v ↦ s_c v` between swap-below permutations. -/
def SwapStep (v v' : Perm (Fin m)) : Prop :=
  IsSwapBelow τ R q p v ∧ IsSwapBelow τ R q p v' ∧ ∃ c, c + 1 < m ∧ v' = sadj m c * v

variable {τ R q p}

theorem SwapStep.symm {v v' : Perm (Fin m)} (h : SwapStep τ R q p v v') :
    SwapStep τ R q p v' v := by
  obtain ⟨h1, h2, c, hc, rfl⟩ := h
  exact ⟨h2, h1, c, hc, by rw [← mul_assoc, sadj_mul_self, one_mul]⟩

/-- For an exit `e`, the permutation `s_{e q} e` is swap-below. -/
theorem IsExit.isSwapBelow {e : Perm (Fin m)} (he : IsExit τ R q p e) (hqp : q < p)
    (hT : (q, p) ∈ invSet m τ) (hx : (e q : ℕ) + 1 < m) :
    IsSwapBelow τ R q p (sadj m (e q) * e) := by
  have hmem : ∀ a b, (a, b) ∈ invSet m (sadj m (e q) * e) ↔
      (a = q ∧ b = p) ∨ (a, b) ∈ invSet m e := by
    intro a b
    rw [mem_invSet_sadj_mul hx, mem_invSet_pair]
    have hp := he.adj
    have hi : ∀ s t : Fin m, (e s : ℕ) = e t → s = t := fun s t h => e.injective (Fin.ext h)
    constructor
    · rintro ⟨hab, h | ⟨h1, h2⟩⟩
      · exact Or.inr ⟨hab, h.1⟩
      · exact Or.inl ⟨hi _ _ h2, hi _ _ (by omega)⟩
    · rintro (⟨rfl, rfl⟩ | ⟨hab, h⟩)
      · exact ⟨hqp, Or.inr ⟨by omega, rfl⟩⟩
      · refine ⟨hab, Or.inl ⟨h, fun ⟨h1, h2⟩ => ?_⟩⟩
        have := hi b q h1
        have := hi a p (by omega)
        subst_vars
        exact absurd (lt_trans hab hqp) (lt_irrefl _)
  refine ⟨fun x hx' => ?_, fun s t hs ht => ?_⟩
  · obtain ⟨a, b⟩ := x
    rcases (hmem a b).1 hx' with ⟨rfl, rfl⟩ | h
    · exact hT
    · exact he.le h
  · rw [hmem]
    exact ⟨fun h => h.resolve_right fun h' => he.redFree s t h' ⟨hs, ht⟩, Or.inl⟩

/-- Every swap-below permutation is connected to `s_{e q} e` for some exit `e`. -/
theorem exists_exit_of_isSwapBelow (hqp : q < p) (hq : q ∈ R) (hp : p ∈ R) :
    ∀ n (v : Perm (Fin m)), invCount m v = n → IsSwapBelow τ R q p v →
      ∃ e, IsExit τ R q p e ∧
        Relation.EqvGen (SwapStep τ R q p) v (sadj m (e q) * e) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro v hn hv
  have hqpv : (q, p) ∈ invSet m v := (hv.red q p hq hp).2 ⟨rfl, rfl⟩
  have hvqp : (v p : ℕ) < v q := (mem_invSet_pair.1 hqpv).2
  have hi : ∀ s t : Fin m, (v s : ℕ) = v t → s = t := fun s t h => v.injective (Fin.ext h)
  by_cases hadj : (v q : ℕ) = v p + 1
  · -- `v = s_x e` with `x = v p`.
    have hx : (v p : ℕ) + 1 < m := by have := (v q).2; omega
    set e := sadj m (v p) * v with he_def
    have heq : (e q : ℕ) = v p := by
      rw [he_def, Perm.mul_apply, sadj_val_of_lt hx, hadj]; unfold swapNat; simp
    have hep : (e p : ℕ) = v p + 1 := by
      rw [he_def, Perm.mul_apply, sadj_val_of_lt hx]; unfold swapNat; simp
    have hmemE : ∀ a b, (a, b) ∈ invSet m e ↔ (a, b) ∈ invSet m v ∧ ¬ (a = q ∧ b = p) := by
      intro a b
      rw [he_def, mem_invSet_sadj_mul hx, mem_invSet_pair, Fin.lt_def, Fin.lt_def]
      constructor
      · rintro ⟨hab, h | ⟨h1, h2⟩⟩
        · refine ⟨⟨hab, h.1⟩, fun ⟨h1, h2⟩ => ?_⟩
          subst h1 h2; omega
        · have h3 := hi b q (by omega)
          have h4 := hi a p (by omega)
          rw [h3, h4] at hab
          exact absurd (Fin.lt_def.1 hqp) (by omega)
      · rintro ⟨⟨hab, h⟩, hne⟩
        refine ⟨hab, Or.inl ⟨h, fun ⟨h1, h2⟩ => hne ⟨hi _ _ (by omega), hi _ _ h1⟩⟩⟩
    have hE : IsExit τ R q p e := by
      refine ⟨fun a b h hr => ?_, by omega, fun x hx' => ?_⟩
      · rw [hmemE] at h
        exact h.2 ((hv.red a b hr.1 hr.2).1 h.1)
      · obtain ⟨a, b⟩ := x
        exact hv.le ((hmemE a b).1 hx').1
    refine ⟨e, hE, ?_⟩
    rw [show sadj m (e q : ℕ) * e = v by
      rw [heq, he_def, ← mul_assoc, sadj_mul_self, one_mul]]
    exact Relation.EqvGen.refl _
  · -- A descent `c` of `v⁻¹` between `v p` and `v q`.
    let f : ℕ → ℕ := fun n => if h : n < m then (v⁻¹ ⟨n, h⟩ : ℕ) else 0
    have hfp : f (v p) = p := by simp [f]
    have hfq : f (v q) = q := by simp [f]
    obtain ⟨c, hc1, hc2, hc3⟩ := exists_drop f ((v q : ℕ) - v p) (v p)
      (by rw [show (v p : ℕ) + ((v q : ℕ) - v p) = v q by omega, hfp, hfq]; exact hqp)
    have hcm : c + 1 < m := by have := (v q).2; omega
    have hf : ∀ n (h : n < m), f n = (v⁻¹ ⟨n, h⟩ : ℕ) := fun n h => by simp [f, h]
    rw [hf (c + 1) hcm, hf c (by omega)] at hc3
    set a := v⁻¹ ⟨c + 1, hcm⟩
    set b := v⁻¹ ⟨c, by omega⟩
    have hva : (v a : ℕ) = c + 1 := by simp [a]
    have hvb : (v b : ℕ) = c := by simp [b]
    set v' := sadj m c * v with hv'_def
    have hmem' : ∀ s t, (s, t) ∈ invSet m v' ↔ (s, t) ∈ invSet m v ∧ ¬ (s = a ∧ t = b) := by
      intro s t
      rw [hv'_def, mem_invSet_sadj_mul hcm, mem_invSet_pair, Fin.lt_def, Fin.lt_def]
      constructor
      · rintro ⟨hst, h | ⟨h1, h2⟩⟩
        · refine ⟨⟨hst, h.1⟩, fun ⟨h1, h2⟩ => ?_⟩
          subst h1 h2; exact h.2 ⟨hvb, hva⟩
        · have := hi t a (by omega)
          have := hi s b (by omega)
          subst_vars; exact absurd hc3 (by omega)
      · rintro ⟨⟨hst, h⟩, hne⟩
        refine ⟨hst, Or.inl ⟨h, fun ⟨h1, h2⟩ => hne ⟨hi _ _ (by omega), hi _ _ (by omega)⟩⟩⟩
    have hab : (a, b) ∈ invSet m v := mem_invSet_pair.2 ⟨Fin.lt_def.2 hc3, by
      rw [Fin.lt_def, hva, hvb]; omega⟩
    have hneq : ¬ (a = q ∧ b = p) := fun ⟨h1, h2⟩ => by
      rw [h1] at hva; rw [h2] at hvb; omega
    have hv' : IsSwapBelow τ R q p v' := by
      refine ⟨fun x hx' => ?_, fun s t hs ht => ?_⟩
      · obtain ⟨s, t⟩ := x
        exact hv.le ((hmem' s t).1 hx').1
      · rw [hmem', hv.red s t hs ht]
        constructor
        · exact fun h => h.1
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, h2⟩, fun h' => hneq ⟨h'.1.symm.trans h1, h'.2.symm.trans h2⟩⟩
    have hlt : invCount m v' < n := by
      rw [← hn, invCount, invCount]
      apply Finset.card_lt_card
      refine ⟨fun x hx' => ?_, fun h => ?_⟩
      · obtain ⟨s, t⟩ := x
        exact ((hmem' s t).1 hx').1
      · exact ((hmem' a b).1 (h hab)).2 ⟨rfl, rfl⟩
    obtain ⟨e, hE, hrel⟩ := ih _ hlt v' rfl hv'
    refine ⟨e, hE, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ?_) hrel⟩
    exact ⟨hv, hv', c, hcm, rfl⟩

private theorem g_val (x α : ℕ) : swapNat (x + 1) (swapNat x α) =
    if α = x then x + 2 else if α = x + 1 then x else if α = x + 2 then x + 1 else α := by
  unfold swapNat; split_ifs <;> omega

private theorem s_val (x α : ℕ) :
    swapNat x α = if α = x then x + 1 else if α = x + 1 then x else α := rfl

private theorem h_val (x α : ℕ) : swapNat (x + 1) (swapNat x (swapNat (x + 1) α)) =
    if α = x then x + 2 else if α = x + 2 then x else α := by
  unfold swapNat; split_ifs <;> omega

/-- Values of `s_{x+1} s_x` against `s_x` and `s_{x+1} s_x s_{x+1}`. -/
private theorem hex_values (x α β : ℕ)
    (h : swapNat (x + 1) (swapNat x β) < swapNat (x + 1) (swapNat x α)) :
    swapNat x β < swapNat x α ∨
      swapNat (x + 1) (swapNat x (swapNat (x + 1) β)) <
        swapNat (x + 1) (swapNat x (swapNat (x + 1) α)) := by
  rw [g_val, g_val] at h
  rw [s_val, s_val, h_val, h_val]
  split_ifs at h ⊢ <;> omega

/-- A move between exits lifts to steps between the associated swap-below permutations. -/
theorem ExitRel.eqvGen (hqp : q < p) (hT : (q, p) ∈ invSet m τ) {e e' : Perm (Fin m)}
    (h : ExitRel τ R q p e e') :
    Relation.EqvGen (SwapStep τ R q p) (sadj m (e q) * e) (sadj m (e' q) * e') := by
  obtain ⟨he, he', hmove⟩ := h
  have hx : (e q : ℕ) + 1 < m := by have := he.adj; have := (e p).2; omega
  have hx' : (e' q : ℕ) + 1 < m := by have := he'.adj; have := (e' p).2; omega
  have hS := he.isSwapBelow hqp hT hx
  have hS' := he'.isSwapBelow hqp hT hx'
  cases hmove with
  | square j hj hfar hlt =>
    have hq' : ((sadj m j * e) q : ℕ) = e q := by
      rw [Perm.mul_apply, sadj_val_of_lt hj]; unfold swapNat; split_ifs <;> omega
    rw [hq'] at hS' ⊢
    refine Relation.EqvGen.rel _ _ ⟨hS, hS', j, hj, ?_⟩
    rw [← mul_assoc, ← mul_assoc, sadj_comm m (by omega)]
  | hexagon hx2 =>
    generalize hxdef : (e q : ℕ) = x at *
    have hq' : ((sadj m x * sadj m (x + 1) * e) q : ℕ) = x + 1 := by
      rw [Perm.mul_apply, Perm.mul_apply, sadj_val_of_lt (by omega), sadj_val_of_lt hx2, hxdef]
      unfold swapNat; split_ifs <;> omega
    rw [hq'] at hS' ⊢
    set w := sadj m (x + 1) * (sadj m x * e) with hw
    have hwv : ∀ a, (w a : ℕ) = swapNat (x + 1) (swapNat x (e a)) := fun a => by
      rw [hw, Perm.mul_apply, Perm.mul_apply, sadj_val_of_lt hx2, sadj_val_of_lt (by omega)]
    have hv : ∀ a, ((sadj m x * e) a : ℕ) = swapNat x (e a) := fun a => by
      rw [Perm.mul_apply, sadj_val_of_lt (by omega)]
    have hv' : ∀ a, ((sadj m (x + 1) * (sadj m x * sadj m (x + 1) * e)) a : ℕ) =
        swapNat (x + 1) (swapNat x (swapNat (x + 1) (e a))) := fun a => by
      rw [Perm.mul_apply, Perm.mul_apply, Perm.mul_apply, sadj_val_of_lt hx2,
        sadj_val_of_lt (by omega), sadj_val_of_lt hx2]
    have hsub : ∀ a b, (a, b) ∈ invSet m w →
        (a, b) ∈ invSet m (sadj m x * e) ∨
          (a, b) ∈ invSet m (sadj m (x + 1) * (sadj m x * sadj m (x + 1) * e)) := by
      intro a b hab
      rw [mem_invSet_pair, Fin.lt_def, Fin.lt_def, hwv, hwv] at hab
      rw [mem_invSet_pair, mem_invSet, Fin.lt_def, Fin.lt_def, Fin.lt_def, hv, hv, hv', hv']
      rcases hex_values x _ _ hab.2 with h | h
      · exact Or.inl ⟨hab.1, h⟩
      · exact Or.inr ⟨hab.1, h⟩
    have hW : IsSwapBelow τ R q p w := by
      refine ⟨fun y hy => ?_, fun s t hs ht => ⟨fun h' => ?_, ?_⟩⟩
      · obtain ⟨a, b⟩ := y
        rcases hsub a b hy with h' | h'
        · exact hS.le h'
        · exact hS'.le h'
      · rcases hsub s t h' with h'' | h''
        · exact (hS.red s t hs ht).1 h''
        · exact (hS'.red s t hs ht).1 h''
      · rintro ⟨rfl, rfl⟩
        rw [mem_invSet_pair, Fin.lt_def, Fin.lt_def, hwv, hwv, he.adj]
        refine ⟨hqp, ?_⟩
        unfold swapNat; split_ifs <;> omega
    refine Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨hS, hW, x + 1, hx2, rfl⟩)
      (Relation.EqvGen.rel _ _ ⟨hW, hS', x, by omega, ?_⟩)
    rw [hw, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, sadj_braid hx2]

/-- Any two swap-below permutations are connected by steps `v ↦ s_c v`. -/
theorem isSwapBelow_connected (hqp : q < p) (hq : q ∈ R) (hp : p ∈ R) {v v' : Perm (Fin m)}
    (hv : IsSwapBelow τ R q p v) (hv' : IsSwapBelow τ R q p v') :
    Relation.EqvGen (SwapStep τ R q p) v v' := by
  have hT : (q, p) ∈ invSet m τ := hv.le ((hv.red q p hq hp).2 ⟨rfl, rfl⟩)
  obtain ⟨e, he, h1⟩ := exists_exit_of_isSwapBelow hqp hq hp _ v rfl hv
  obtain ⟨e', he', h2⟩ := exists_exit_of_isSwapBelow hqp hq hp _ v' rfl hv'
  have key : ∀ e e', Relation.EqvGen (ExitRel τ R q p) e e' →
      Relation.EqvGen (SwapStep τ R q p) (sadj m (e q) * e) (sadj m (e' q) * e') := by
    intro e e' hr
    induction hr with
    | rel a b hab => exact hab.eqvGen hqp hT
    | refl a => exact Relation.EqvGen.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans _ _ _ ih2
  exact h1.trans _ _ _ ((key e e' (exitRel_connected hqp hT he he')).trans _ _ _ h2.symm)

end Categorification.TypeA
