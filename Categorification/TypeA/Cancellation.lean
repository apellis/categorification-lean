/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.WeakOrder

/-!
# Cancelling a non-additive product by moving simple transpositions

Let `u, v ∈ S_m` with `length (u * v) < length u + length v`. Then some simple transposition
can be moved between `u` and `v` (from the right of `u` to the left of `v` or back) without
changing the total length, until `u` has a right descent which is also a left descent of `v`.
We record this as an induction principle, `TypeA.cancel_induction`, in which the moves avoid
a prescribed set of strands: if the strands of `v` are coloured, and every inversion of `v`
between two coloured strands is also an inversion of `u * v`, the moves can be chosen never to
swap two coloured strands.

This is the combinatorial input to the proof of Webster's Lemma 6.5 (arXiv:1309.3796v2):
coloured strands are the red strands, and a crossing of two red strands cannot be moved across
the tensor product of bimodules.

## Main results

* `TypeA.exists_cancelPair` : a non-additive product has a pair of positions inverted by `u`
  and by `v⁻¹`.
* `TypeA.ColourAdditive.move`, `TypeA.ColourAdditive.not_red`.
* `TypeA.cancel_induction` : the induction principle.
-/

namespace Categorification.TypeA

open Equiv

variable {m : ℕ}

/-- A non-additive product `u * v` has positions `c < d` inverted by both `u` and `v⁻¹`. -/
theorem exists_cancelPair {u v : Perm (Fin m)} (h : length m (u * v) < length m u + length m v) :
    ∃ c d : Fin m, c < d ∧ u d < u c ∧ v⁻¹ d < v⁻¹ c := by
  by_contra hne
  push Not at hne
  have hsub : invSet m v ⊆ invSet m (u * v) := by
    rintro ⟨a, b⟩ hab
    rw [mem_invSet] at hab ⊢
    refine ⟨hab.1, ?_⟩
    rcases lt_or_gt_of_ne ((u * v).injective.ne hab.1.ne) with h1 | h1
    · have := hne (v b) (v a) hab.2 (by simpa using h1)
      simp only [Perm.coe_inv, symm_apply_apply] at this
      exact absurd hab.1 (not_lt.2 this)
    · exact h1
  have := length_add_of_invSet_subset hsub
  rw [mul_inv_cancel_right] at this
  omega

private theorem sadj_lt_sadj_iff' {k : ℕ} (hk : k + 1 < m) (x y : Fin m) :
    sadj m k y < sadj m k x ↔
      (y < x ∧ ¬ ((y : ℕ) = k ∧ (x : ℕ) = k + 1)) ∨
        ((y : ℕ) = k + 1 ∧ (x : ℕ) = k) := by
  rw [Fin.lt_def, Fin.lt_def, sadj_val_of_lt hk, sadj_val_of_lt hk]
  have := swapNat_cases k x
  have := swapNat_cases k y
  generalize swapNat k x = x' at *
  generalize swapNat k y = y' at *
  omega

/-- The hypothesis of `cancel_induction`: every inversion of `v` between two coloured strands
is an inversion of `u * v`. -/
def ColourAdditive (Red : Fin m → Prop) (u v : Perm (Fin m)) : Prop :=
  ∀ a b, Red a → Red b → (a, b) ∈ invSet m v → (a, b) ∈ invSet m (u * v)

/-- Moving `s_c` between `u` and `v` keeps `ColourAdditive` when the strands at positions
`c, g = c + 1` above `v` are not both coloured. -/
theorem ColourAdditive.move {Red : Fin m → Prop} {u v : Perm (Fin m)}
    (h : ColourAdditive Red u v) {c g : Fin m} (hg : g.val = c.val + 1)
    (hnr : ¬ (Red (v⁻¹ c) ∧ Red (v⁻¹ g))) :
    ColourAdditive Red (u * sadj m c) (sadj m c * v) := by
  have hc : c.val + 1 < m := hg ▸ g.2
  intro a b ha hb hab
  have e : u * sadj m c * (sadj m c * v) = u * v := by
    rw [mul_assoc, ← mul_assoc (sadj m c), sadj_mul_self, one_mul]
  rw [e]
  rw [mem_invSet, Perm.mul_apply, Perm.mul_apply, sadj_lt_sadj_iff' hc] at hab
  rcases hab with ⟨hlt, (⟨hl, -⟩ | ⟨hb', ha'⟩)⟩
  · exact h a b ha hb (mem_invSet.2 ⟨hlt, hl⟩)
  · exfalso
    apply hnr
    have hva : v a = c := Fin.ext ha'
    have hvb : v b = g := Fin.ext (by simp only at hb'; omega)
    have e1 : v⁻¹ c = a := by rw [← hva]; simp
    have e2 : v⁻¹ g = b := by rw [← hvb]; simp
    rw [e1, e2]
    exact ⟨ha, hb⟩

/-- A cancelling pair is not a pair of coloured strands. -/
theorem ColourAdditive.not_red {Red : Fin m → Prop} {u v : Perm (Fin m)}
    (h : ColourAdditive Red u v) {c d : Fin m} (hcd : c < d) (hud : u d < u c)
    (hvd : v⁻¹ d < v⁻¹ c) (hr : Red (v⁻¹ c)) (hs : Red (v⁻¹ d)) : False := by
  have := h _ _ hs hr (mem_invSet.2 ⟨hvd, by simpa using hcd⟩)
  rw [mem_invSet] at this
  simp only [Perm.mul_apply, Perm.coe_inv, apply_symm_apply] at this
  exact lt_asymm this.2 hud

private theorem sadj_self_eq {c g : Fin m} (hg : g.val = c.val + 1) : sadj m c c = g :=
  Fin.ext (by rw [sadj_val_of_lt (hg ▸ g.2)]; simp [swapNat, hg])

private theorem sadj_succ_eq {c g : Fin m} (hg : g.val = c.val + 1) : sadj m c g = c :=
  Fin.ext (by rw [sadj_val_of_lt (hg ▸ g.2)]; simp [swapNat, hg])

private theorem sadj_fix {c x : Fin m} (h1 : x.val ≠ c.val) (h2 : x.val ≠ c.val + 1) :
    sadj m c x = x :=
  sadj_apply_of_ne x h1 h2

/-- **Cancellation by moves.** Let `u * v` be non-additive, and suppose that every inversion of
`v` between coloured strands is an inversion of `u * v`. To prove `P u v`, it suffices to treat
a common descent `s_c` (a right descent of `u` and a left descent of `v`) and to reduce
`P u v` to `P (u * s_c) (s_c * v)` for moves of `s_c` from `u` to `v` (`hdown`) or from `v` to
`u` (`hup`), which keep the total length. In all three cases, the strands at positions
`c, c + 1` between `u` and `v` are not both coloured. -/
theorem cancel_induction (Red : Fin m → Prop) {P : Perm (Fin m) → Perm (Fin m) → Prop}
    (hbase : ∀ (u v : Perm (Fin m)) (c g : Fin m), g.val = c.val + 1 →
      u g < u c → v⁻¹ g < v⁻¹ c → ¬ (Red (v⁻¹ c) ∧ Red (v⁻¹ g)) → P u v)
    (hdown : ∀ (u v : Perm (Fin m)) (c g : Fin m), g.val = c.val + 1 →
      u g < u c → v⁻¹ c < v⁻¹ g → ¬ (Red (v⁻¹ c) ∧ Red (v⁻¹ g)) →
      P (u * sadj m c) (sadj m c * v) → P u v)
    (hup : ∀ (u v : Perm (Fin m)) (c g : Fin m), g.val = c.val + 1 →
      u c < u g → v⁻¹ g < v⁻¹ c → ¬ (Red (v⁻¹ c) ∧ Red (v⁻¹ g)) →
      P (u * sadj m c) (sadj m c * v) → P u v)
    {u v : Perm (Fin m)} (hred : ColourAdditive Red u v)
    (h : length m (u * v) < length m u + length m v) : P u v := by
  obtain ⟨c, d, hcd, hud, hvd⟩ := exists_cancelPair h
  suffices H : ∀ n, ∀ (u v : Perm (Fin m)) (c d : Fin m), d.val - c.val = n → c < d →
      u d < u c → v⁻¹ d < v⁻¹ c → ColourAdditive Red u v → P u v from
    H _ u v c d rfl hcd hud hvd hred
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro u v c d hn hcd hud hvd hred
  have hcd₀ := Fin.lt_def.1 hcd
  by_cases hw : d.val = c.val + 1
  · exact hbase u v c d hw hud hvd fun hr => hred.not_red hcd hud hvd hr.1 hr.2
  have hcd' : c.val + 1 < d.val := by omega
  obtain ⟨g, hg⟩ : ∃ g : Fin m, g.val = c.val + 1 := ⟨⟨c.val + 1, by omega⟩, rfl⟩
  obtain ⟨h', hh⟩ : ∃ h' : Fin m, h'.val + 1 = d.val :=
    ⟨⟨d.val - 1, by omega⟩, by simp; omega⟩
  have hcg : c < g := Fin.lt_def.2 (by omega)
  have hgd : g < d := Fin.lt_def.2 (by omega)
  have hch : c < h' := Fin.lt_def.2 (by omega)
  have hhd : h' < d := Fin.lt_def.2 (by omega)
  -- a smaller cancelling pair for the same `u, v`
  by_cases w1 : u g < u c ∧ v⁻¹ g < v⁻¹ c
  · exact ih (g.val - c.val) (by omega) u v c g rfl hcg w1.1 w1.2 hred
  by_cases w2 : u d < u g ∧ v⁻¹ d < v⁻¹ g
  · exact ih (d.val - g.val) (by omega) u v g d rfl hgd w2.1 w2.2 hred
  by_cases w3 : u h' < u c ∧ v⁻¹ h' < v⁻¹ c
  · exact ih (h'.val - c.val) (by omega) u v c h' rfl hch w3.1 w3.2 hred
  by_cases w4 : u d < u h' ∧ v⁻¹ d < v⁻¹ h'
  · exact ih (d.val - h'.val) (by omega) u v h' d rfl hhd w4.1 w4.2 hred
  have hvi : ∀ x y : Fin m, x ≠ y → v⁻¹ x ≠ v⁻¹ y :=
    fun x y hxy => v⁻¹.injective.ne hxy
  have hui : ∀ x y : Fin m, x ≠ y → u x ≠ u y := fun x y hxy => u.injective.ne hxy
  by_cases hr1 : Red (v⁻¹ c) ∧ Red (v⁻¹ g)
  · -- move at `h'`, `d`
    have hr2 : ¬ (Red (v⁻¹ h') ∧ Red (v⁻¹ d)) := fun hr =>
      hred.not_red hcd hud hvd hr1.1 hr.2
    have hu1 : (u * sadj m h') h' = u d := by
      rw [Perm.mul_apply, sadj_self_eq hh.symm]
    have hu2 : (u * sadj m h') c = u c := by
      rw [Perm.mul_apply, sadj_fix (by omega) (by omega)]
    have hv1 : (sadj m h' * v)⁻¹ h' = v⁻¹ d := by
      rw [mul_inv_rev, sadj_inv, Perm.mul_apply, sadj_self_eq hh.symm]
    have hv2 : (sadj m h' * v)⁻¹ c = v⁻¹ c := by
      rw [mul_inv_rev, sadj_inv, Perm.mul_apply, sadj_fix (by omega) (by omega)]
    have key := ih (h'.val - c.val) (by omega) _ _ c h' rfl hch (by rw [hu1, hu2]; exact hud)
      (by rw [hv1, hv2]; exact hvd) (hred.move hh.symm hr2)
    rcases lt_or_gt_of_ne (hui d h' (Fin.ne_of_gt hhd)) with hlt | hlt
    · have hv : v⁻¹ h' < v⁻¹ d := by
        rcases lt_or_gt_of_ne (hvi h' d (Fin.ne_of_lt hhd)) with h₁ | h₁
        · exact h₁
        · exact absurd ⟨hlt, h₁⟩ w4
      exact hdown u v h' d hh.symm hlt hv hr2 key
    · have hv : v⁻¹ d < v⁻¹ h' := by
        rcases lt_or_gt_of_ne (hvi h' c (Fin.ne_of_gt hch)) with h₁ | h₁
        · exact absurd ⟨lt_trans hlt hud, h₁⟩ w3
        · exact lt_trans hvd h₁
      exact hup u v h' d hh.symm hlt hv hr2 key
  · -- move at `c`, `g`
    have hu1 : (u * sadj m c) g = u c := by
      rw [Perm.mul_apply, sadj_succ_eq hg]
    have hu2 : (u * sadj m c) d = u d := by
      rw [Perm.mul_apply, sadj_fix (by omega) (by omega)]
    have hv1 : (sadj m c * v)⁻¹ g = v⁻¹ c := by
      rw [mul_inv_rev, sadj_inv, Perm.mul_apply, sadj_succ_eq hg]
    have hv2 : (sadj m c * v)⁻¹ d = v⁻¹ d := by
      rw [mul_inv_rev, sadj_inv, Perm.mul_apply, sadj_fix (by omega) (by omega)]
    have key := ih (d.val - g.val) (by omega) _ _ g d rfl hgd (by rw [hu1, hu2]; exact hud)
      (by rw [hv1, hv2]; exact hvd) (hred.move hg hr1)
    rcases lt_or_gt_of_ne (hui g c (Fin.ne_of_gt hcg)) with hlt | hlt
    · have hv : v⁻¹ c < v⁻¹ g := by
        rcases lt_or_gt_of_ne (hvi g c (Fin.ne_of_gt hcg)) with h₁ | h₁
        · exact absurd ⟨hlt, h₁⟩ w1
        · exact h₁
      exact hdown u v c g hg hlt hv hr1 key
    · have hv : v⁻¹ g < v⁻¹ c := by
        rcases lt_or_gt_of_ne (hvi g d (Fin.ne_of_lt hgd)) with h₁ | h₁
        · exact lt_trans h₁ hvd
        · exact absurd ⟨lt_trans hud hlt, h₁⟩ w2
      exact hup u v c g hg hlt hv hr1 key

end Categorification.TypeA
