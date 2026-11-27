/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.TypeA.Parabolic

/-!
# The parabolic subgroup of a window `[c, c + N)` of `S_M`

Webster, arXiv:1309.3796v3, §7.3, proof of Lemma 7.17: below a cap after the red strand `λ_j`,
the strands at the maximum occupy a window `[c, c + N)` in the middle of the strands of `λ⁺`.
The permutations of the window form a parabolic subgroup `S_N ⊆ S_M` (`winPerm`), and every
`w ∈ S_M` factors uniquely as `w = b u` with `b` a permutation of the window and `u` a
*window shuffle*: `u⁻¹` is increasing on the window (`winEquiv`). Lengths add
(`length_winPerm_mul`), so a reduced word of `b`, shifted to the window, followed by a reduced
word of `u` is a reduced word of `w` (`IsReduced.window`).

The window subgroup is `1 × (S_N × 1)` inside the nested Young subgroups
`S_c × S_{M - c}` and `S_N × S_{M - c - N}`; the proofs reduce to those of `Parabolic`.

## Main definitions

* `TypeA.winPos`, `TypeA.winPerm`: the window and its permutations.
* `TypeA.IsWinShuffle`, `TypeA.WinShuffle`: the minimal coset representatives.
* `TypeA.winEquiv`: `S_N × {window shuffles} ≃ S_M`.

## Main results

* `TypeA.length_winPerm_mul`: `ℓ(b u) = ℓ(b) + ℓ(u)` for a window shuffle `u`.
* `TypeA.IsReduced.window`: concatenation of reduced words.
-/

namespace Categorification.TypeA

open Equiv

variable {M N c : ℕ} (hc : c + N ≤ M)

include hc in
theorem win_h₁ : c + (M - c) = M := by omega

include hc in
theorem win_h₂ : N + (M - c - N) = M - c := by omega

/-- The position `c + x` of the window `[c, c + N)`. -/
def winPos (x : Fin N) : Fin M := ⟨c + x.val, by omega⟩

@[simp] theorem winPos_val (x : Fin N) : (winPos hc x).val = c + x.val := rfl

theorem winPos_injective : Function.Injective (winPos hc) :=
  fun x x' h => Fin.ext (by simpa using congrArg Fin.val h)

theorem winPos_lt_winPos {x x' : Fin N} : winPos hc x < winPos hc x' ↔ x < x' := by
  rw [Fin.lt_def, Fin.lt_def, winPos_val, winPos_val]; omega

theorem blockEquiv_winPos (x : Fin N) :
    blockEquiv (win_h₁ hc) (Sum.inr (blockEquiv (win_h₂ hc) (Sum.inl x))) = winPos hc x :=
  Fin.ext (by simp)

/-- The permutation acting by `b` on the window `[c, c + N)` and trivially elsewhere. -/
def winPerm (b : Perm (Fin N)) : Perm (Fin M) :=
  blockPerm (win_h₁ hc) 1 (blockPerm (win_h₂ hc) b 1)

@[simp] theorem winPerm_winPos (b : Perm (Fin N)) (x : Fin N) :
    winPerm hc b (winPos hc x) = winPos hc (b x) := by
  rw [← blockEquiv_winPos, winPerm, blockPerm_inr, blockPerm_inl, blockEquiv_winPos]

theorem winPerm_mul (b b' : Perm (Fin N)) :
    winPerm hc b * winPerm hc b' = winPerm hc (b * b') := by
  rw [winPerm, winPerm, winPerm, blockPerm_mul, blockPerm_mul, one_mul, one_mul]

@[simp] theorem winPerm_one : winPerm hc (1 : Perm (Fin N)) = 1 := by
  rw [winPerm, blockPerm_one, blockPerm_one]

theorem winPerm_inv (b : Perm (Fin N)) : (winPerm hc b)⁻¹ = winPerm hc b⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, winPerm_mul]; simp

/-- A shifted word of the window represents a permutation of the window. -/
theorem wordProd_shiftWord_window {β : List ℕ} (hβ : ValidWord N β) :
    wordProd M (shiftWord c β) = winPerm hc (wordProd N β) := by
  rw [wordProd_shiftWord (win_h₁ hc) (hβ.of_le (by omega)),
    wordProd_eq_blockPerm_left (win_h₂ hc) hβ, winPerm]

/-! ### Window shuffles -/

/-- `u` is a *window shuffle*: `u⁻¹` is increasing on the window. Equivalently, `u` is the
minimal length element of its coset `S_N u` (see `length_winPerm_mul`). -/
def IsWinShuffle (u : Perm (Fin M)) : Prop := StrictMono fun x : Fin N => u⁻¹ (winPos hc x)

/-- The window shuffles. -/
abbrev WinShuffle : Type := {u : Perm (Fin M) // IsWinShuffle hc u}

theorem isWinShuffle_one : IsWinShuffle hc (1 : Perm (Fin M)) :=
  fun x x' hx => by simpa [winPos_lt_winPos] using hx

private theorem eq_one_of_strictMono' {n : ℕ} {a : Perm (Fin n)} (ha : StrictMono a) :
    a = 1 := by
  have := Subsingleton.elim (ha.orderIsoOfSurjective a a.surjective) (OrderIso.refl _)
  ext x
  exact congrArg Fin.val (congrArg (fun φ : Fin n ≃o Fin n => φ x) this)

/-- **Length additivity**: `ℓ(b u) = ℓ(b) + ℓ(u)` for a permutation `b` of the window and a
window shuffle `u`. -/
theorem length_winPerm_mul (b : Perm (Fin N)) {u : Perm (Fin M)} (hu : IsWinShuffle hc u) :
    length M (winPerm hc b * u) = length N b + length M u := by
  obtain ⟨a, v, u₁, hu₁, rfl⟩ := exists_blockPerm_mul (win_h₁ hc) u
  have hv : StrictMono fun x : Fin N => v⁻¹ (blockEquiv (win_h₂ hc) (Sum.inl x)) := by
    intro x x' hx
    have h := hu hx
    simp only [mul_inv_rev, Perm.mul_apply, ← blockEquiv_winPos, blockPerm_inv,
      blockPerm_inr] at h
    exact hu₁.2.lt_iff_lt.1 h
  obtain ⟨a₂, a₃, u₂, hu₂, rfl⟩ := exists_blockPerm_mul (win_h₂ hc) v
  have ha₂ : a₂ = 1 := by
    have hs : StrictMono (⇑(a₂⁻¹ : Perm (Fin N))) := by
      intro x x' hx
      have h := hv hx
      simp only [mul_inv_rev, Perm.mul_apply, blockPerm_inv, blockPerm_inl] at h
      exact hu₂.1.lt_iff_lt.1 h
    rw [← inv_eq_one]
    exact eq_one_of_strictMono' hs
  subst ha₂
  have he : winPerm hc b * (blockPerm (win_h₁ hc) a (blockPerm (win_h₂ hc) 1 a₃ * u₂) * u₁) =
      blockPerm (win_h₁ hc) a (blockPerm (win_h₂ hc) b a₃ * u₂) * u₁ := by
    rw [winPerm, ← mul_assoc, blockPerm_mul, ← mul_assoc, blockPerm_mul, one_mul, mul_one,
      one_mul]
  rw [he, length_blockPerm_mul _ _ _ hu₁, length_blockPerm_mul _ _ _ hu₁,
    length_blockPerm_mul _ _ _ hu₂, length_blockPerm_mul _ _ _ hu₂, length_one]
  omega

/-- Existence of the factorisation `w = b u` with `u` a window shuffle. -/
theorem exists_winPerm_mul (w : Perm (Fin M)) :
    ∃ (b : Perm (Fin N)) (u : Perm (Fin M)), IsWinShuffle hc u ∧ winPerm hc b * u = w := by
  let f : Fin N → Fin M := fun x => w⁻¹ (winPos hc x)
  refine ⟨Tuple.sort f, (winPerm hc (Tuple.sort f))⁻¹ * w, ?_, by rw [mul_inv_cancel_left]⟩
  have hs := (Tuple.monotone_sort f).strictMono_of_injective
    ((w⁻¹.injective.comp (winPos_injective hc)).comp (Tuple.sort f).injective)
  intro x x' hx
  have h := hs hx
  simp only [mul_inv_rev, inv_inv, Perm.mul_apply, winPerm_winPos]
  exact h

/-- Uniqueness of the factorisation. -/
theorem winPerm_mul_injective {b b' : Perm (Fin N)} {u u' : Perm (Fin M)}
    (hu : IsWinShuffle hc u) (hu' : IsWinShuffle hc u')
    (he : winPerm hc b * u = winPerm hc b' * u') : b = b' ∧ u = u' := by
  have hinv : u⁻¹ = u'⁻¹ * winPerm hc (b'⁻¹ * b) := by
    rw [← winPerm_mul, ← winPerm_inv, ← mul_assoc, ← mul_inv_rev, ← he, mul_inv_rev,
      inv_mul_cancel_right]
  have hs : StrictMono (⇑(b'⁻¹ * b : Perm (Fin N))) := by
    intro x x' hx
    have h := hu hx
    simp only [hinv, Perm.mul_apply, winPerm_winPos] at h
    exact hu'.lt_iff_lt.1 h
  have hb : b = b' := by
    have := eq_one_of_strictMono' hs
    rwa [inv_mul_eq_one, eq_comm] at this
  subst hb
  exact ⟨rfl, mul_left_cancel he⟩

/-- **The window factorisation**: `S_N × {window shuffles} ≃ S_M`, `(b, u) ↦ b u`. -/
noncomputable def winEquiv : Perm (Fin N) × WinShuffle hc ≃ Perm (Fin M) :=
  Equiv.ofBijective (fun p => winPerm hc p.1 * p.2.1)
    ⟨fun p q he => by
      obtain ⟨b, u, hu⟩ := p
      obtain ⟨b', u', hu'⟩ := q
      obtain ⟨rfl, rfl⟩ := winPerm_mul_injective hc hu hu' he
      rfl,
     fun w => by
      obtain ⟨b, u, hu, rfl⟩ := exists_winPerm_mul hc w
      exact ⟨(b, ⟨u, hu⟩), rfl⟩⟩

@[simp] theorem winEquiv_apply (p : Perm (Fin N) × WinShuffle hc) :
    winEquiv hc p = winPerm hc p.1 * p.2.1 := rfl

theorem winEquiv_symm_spec (w : Perm (Fin M)) :
    winPerm hc ((winEquiv hc).symm w).1 * ((winEquiv hc).symm w).2.1 = w :=
  (winEquiv hc).apply_symm_apply w

/-- A reduced word of a permutation of the window, shifted to the window, followed by a reduced
word of a window shuffle `u`, is a reduced word of `b u`. -/
theorem IsReduced.window {β σ : List ℕ} (hβ : IsReduced N β) (hσ : IsReduced M σ)
    (hu : IsWinShuffle hc (wordProd M σ)) :
    IsReduced M (shiftWord c β ++ σ) ∧
      wordProd M (shiftWord c β ++ σ) = winPerm hc (wordProd N β) * wordProd M σ := by
  have hw : wordProd M (shiftWord c β ++ σ) = winPerm hc (wordProd N β) * wordProd M σ := by
    rw [wordProd_append, wordProd_shiftWord_window hc hβ.1]
  refine ⟨⟨validWord_append.2 ⟨(hβ.1.of_le (by omega)).shiftWord (win_h₁ hc), hσ.1⟩, ?_⟩, hw⟩
  rw [hw, length_winPerm_mul hc _ hu, List.length_append, length_shiftWord, hβ.2, hσ.2]

end Categorification.TypeA
