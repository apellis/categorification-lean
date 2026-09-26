/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.DividedPowerIdempotents

/-!
# Computations in the nilHecke ring (KL II)

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups II*,
arXiv:0804.2080v1, §3, "Computations in the nilHecke ring" (TeX lines ~480–660): the lemma
(**Lemma 5**, `∂(n) e_n = ∂(n)`) and the graphical identities (10)–(13)
(`eq-boxes-1`, `eq-boxes-2`, `eq-boxes_undercross1`, `eq-boxes_undercross2`).

We prove these identities for an arbitrary *nilHecke family* `(X, D)` in a ring `B`
(`NilHecke.IsNilHeckeFamily`: elements satisfying the defining relations of the nilHecke
ring `NH_n` of KL I §2.2, Example 3). In `Categorification.KLR.KL2.NilHeckeBlocks` they are
transported to blocks of strands with equal labels in `R(ν)`.

Positions are zero-indexed. For a block `[s, s + n)` of strands:

* `chL D p l = D_p D_{p+1} ⋯ D_{p+l-1}`: the strand at the bottom position `p + l` moves to the
  top position `p`, crossing the strands in between;
* `chR D p l = D_{p+l-1} ⋯ D_{p+1} D_p`: the strand at the bottom position `p` moves to the top
  position `p + l`;
* `Wb D s n = ∂(n)`: the longest divided difference `∂_{w_0}` of the block, along the reduced word
  `w0Word n` (shifted by `s`);
* `Δb X s n = x_s^{n-1} x_{s+1}^{n-2} ⋯ x_{s+n-2}` and `Eb X D s n = Δb X s n * Wb D s n = e_n`,
  the idempotent `e_{i,n}` of the block.

## Main results

* `wb_succ_eq_wb_mul_chL`, `wb_succ_eq_chR_mul_wb`, `wb_succ_eq_wb_mul_chR` : the reduced
  factorisations `∂(n+1) = ∂'(n) ∂_{c}` of the longest element (`∂'(n)` on the last `n`
  strands), `∂(n+1) = ∂_{c'} ∂'(n)`, `∂(n+1) = ∂(n) ∂_{c'}`.
* `d_mul_wb`, `wb_mul_d` : `∂_j ∂(n) = ∂(n) ∂_j = 0`.
* `wb_mul_Δb_mul_wb` : **KL II, Lemma 5** in the form `∂(n) x^δ ∂(n) = ∂(n)`, for every block.
* `eb_mul_eb_left`, `eb_mul_eb_right` : **KL II (10)**, `e_n (e_{n-1} ⊗ 1) = e_n` and
  `e_n (1 ⊗ e_{n-1}) = e_n`.
* `eb_mul_chR_mul_eb`, `eb_mul_chL_mul_eb` : **KL II (11)**.
* `eb_mul_x_pow_mul_chL` : **KL II (12)**, `e_n x_1^a D_1 ⋯ D_{n-1} = 0` for `a < n - 1` and
  `= e_n` for `a = n - 1`.
* `eb_mul_x_pow_mul_chR` : **KL II (13)**, `e_n x_n^a D_{n-1} ⋯ D_1 = 0` for `a < n - 1` and
  `= (-1)^{n-1} e_n` for `a = n - 1` (via the mirror family `mirror`).
-/

namespace Categorification.KLR.KL2.NH

open Categorification.NilHecke Categorification.KLR.NilHecke

variable {B : Type*} [Ring B]

/-! ### Words of divided differences -/

section words

variable (D : ℕ → B)

/-- The product `D_{ρ₀} D_{ρ₁} ⋯` along a word `ρ`. -/
def wp (ρ : List ℕ) : B := (ρ.map D).prod

/-- `D_p D_{p+1} ⋯ D_{p+l-1}`: the strand at bottom position `p + l` moves to top position `p`. -/
def chL (p l : ℕ) : B := wp D (List.range' p l)

/-- `D_{p+l-1} ⋯ D_{p+1} D_p`: the strand at bottom position `p` moves to top position `p + l`. -/
def chR (p l : ℕ) : B := wp D (List.range' p l).reverse

/-- The longest divided difference `∂(n) = ∂_{w_0}` of the block `[s, s + n)`. -/
def Wb (s n : ℕ) : B := wp D ((w0Word n).map (s + ·))

variable {D}

@[simp] theorem wp_nil : wp D [] = 1 := rfl

theorem wp_cons (j : ℕ) (ρ : List ℕ) : wp D (j :: ρ) = D j * wp D ρ := by simp [wp]

theorem wp_append (ρ σ : List ℕ) : wp D (ρ ++ σ) = wp D ρ * wp D σ := by simp [wp]

@[simp] theorem chL_zero (p : ℕ) : chL D p 0 = 1 := by simp [chL]

@[simp] theorem chR_zero (p : ℕ) : chR D p 0 = 1 := by simp [chR]

theorem chL_succ (p l : ℕ) : chL D p (l + 1) = D p * chL D (p + 1) l := by
  rw [chL, List.range'_succ, wp_cons]; rfl

theorem chL_succ' (p l : ℕ) : chL D p (l + 1) = chL D p l * D (p + l) := by
  rw [chL, List.range'_concat, wp_append, wp_cons, wp_nil, mul_one, one_mul]; rfl

theorem chR_succ (p l : ℕ) : chR D p (l + 1) = chR D (p + 1) l * D p := by
  rw [chR, List.range'_succ, List.reverse_cons, wp_append, wp_cons, wp_nil, mul_one]; rfl

theorem chR_succ' (p l : ℕ) : chR D p (l + 1) = D (p + l) * chR D p l := by
  rw [chR, List.range'_concat, List.reverse_append, wp_append, List.reverse_singleton, wp_cons,
    wp_nil, mul_one, one_mul]; rfl

theorem wb_zero (s : ℕ) : Wb D s 0 = 1 := rfl

theorem wb_one (s : ℕ) : Wb D s 1 = 1 := rfl

/-- `∂(n+1) = D_s ⋯ D_{s+n-1} ∂(n)` (the definition of `w0Word`). -/
theorem wb_succ (s n : ℕ) : Wb D s (n + 1) = chL D s n * Wb D s n := by
  rw [Wb, w0Word_succ, List.map_append, wp_append, List.range_eq_range', List.map_add_range',
    add_zero]; rfl

end words

/-! ### Relations for the divided differences -/

section relations

variable {n : ℕ} {X : Fin n → B} {D : ℕ → B} (hF : IsNilHeckeFamily n X D)
include hF

theorem d_comm' {j l : ℕ} (h : j + 1 < l ∨ l + 1 < j) : D j * D l = D l * D j := by
  rcases h with h | h
  · exact hF.d_comm j l h
  · exact (hF.d_comm l j h).symm

theorem d_commute {j l : ℕ} (h : j + 1 < l ∨ l + 1 < j) : Commute (D j) (D l) :=
  d_comm' hF h

/-- The braid relation, right-associated. -/
theorem braid_assoc (j : ℕ) (r : B) :
    D j * (D (j + 1) * (D j * r)) = D (j + 1) * (D j * (D (j + 1) * r)) := by
  simp only [← mul_assoc, hF.braid]

theorem braid_assoc' (j : ℕ) :
    D j * (D (j + 1) * D j) = D (j + 1) * (D j * D (j + 1)) := by
  simp only [← mul_assoc, hF.braid]

theorem d_commute_wp {j : ℕ} {ρ : List ℕ} (h : ∀ l ∈ ρ, j + 1 < l ∨ l + 1 < j) :
    Commute (D j) (wp D ρ) := by
  induction ρ with
  | nil => exact Commute.one_right _
  | cons l ρ ih =>
    rw [wp_cons]
    exact (d_commute hF (h l List.mem_cons_self)).mul_right
      (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))

theorem d_commute_chL {j p l : ℕ} (h : j + 1 < p ∨ p + l < j) : Commute (D j) (chL D p l) :=
  d_commute_wp hF fun l' hl' => by
    rw [List.mem_range'_1] at hl'; omega

theorem d_commute_chR {j p l : ℕ} (h : j + 1 < p ∨ p + l < j) : Commute (D j) (chR D p l) :=
  d_commute_wp hF fun l' hl' => by
    rw [List.mem_reverse, List.mem_range'_1] at hl'; omega

/-- Sliding a crossing through `chL`: `chL p l · D_j = D_{j+1} · chL p l` for
`p ≤ j`, `j + 2 ≤ p + l`. -/
theorem chL_mul_d {p l j : ℕ} (h₁ : p ≤ j) (h₂ : j + 2 ≤ p + l) :
    chL D p l * D j = D (j + 1) * chL D p l := by
  induction l generalizing p with
  | zero => omega
  | succ l ih =>
    rw [chL_succ]
    rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
    · obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hc := d_commute_chL hF (j := p) (p := p + 1 + 1) (l := l) (by omega)
      rw [chL_succ]
      simp only [mul_assoc]
      rw [← hc.eq, braid_assoc hF]
    · rw [mul_assoc, ih (by omega) (by omega), ← mul_assoc, ← mul_assoc,
        d_comm' hF (by omega)]

/-- Sliding a word through `chL`. -/
theorem chL_mul_wp {p l : ℕ} {ρ : List ℕ} (h : ∀ j ∈ ρ, p ≤ j ∧ j + 2 ≤ p + l) :
    chL D p l * wp D ρ = wp D (ρ.map (· + 1)) * chL D p l := by
  induction ρ with
  | nil => simp
  | cons j ρ ih =>
    rw [wp_cons, List.map_cons, wp_cons, ← mul_assoc, chL_mul_d hF (h j List.mem_cons_self).1
      (h j List.mem_cons_self).2, mul_assoc, ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj'),
      mul_assoc]

/-- Sliding a crossing through `chR`: `D_j · chR p l = chR p l · D_{j+1}` for
`p ≤ j`, `j + 2 ≤ p + l`. -/
theorem d_mul_chR {p l j : ℕ} (h₁ : p ≤ j) (h₂ : j + 2 ≤ p + l) :
    D j * chR D p l = chR D p l * D (j + 1) := by
  induction l generalizing p with
  | zero => omega
  | succ l ih =>
    rw [chR_succ]
    rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
    · obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hc := d_commute_chR hF (j := p) (p := p + 1 + 1) (l := l) (by omega)
      rw [chR_succ]
      simp only [mul_assoc]
      rw [hc.left_comm, braid_assoc' hF]
    · rw [← mul_assoc, ih (by omega) (by omega), mul_assoc, mul_assoc,
        d_comm' hF (by omega)]

/-- Sliding a word through `chR`. -/
theorem wp_mul_chR {p l : ℕ} {ρ : List ℕ} (h : ∀ j ∈ ρ, p ≤ j ∧ j + 2 ≤ p + l) :
    wp D ρ * chR D p l = chR D p l * wp D (ρ.map (· + 1)) := by
  induction ρ with
  | nil => simp
  | cons j ρ ih =>
    rw [wp_cons, List.map_cons, wp_cons, mul_assoc,
      ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj'), ← mul_assoc,
      d_mul_chR hF (h j List.mem_cons_self).1 (h j List.mem_cons_self).2, mul_assoc]

/-- `L(p, q) L(p, q - 1) = L(p + 1, q) L(p, q)`. -/
theorem chL_mul_chL (p l : ℕ) :
    chL D p (l + 1) * chL D p l = chL D (p + 1) l * chL D p (l + 1) := by
  induction l generalizing p with
  | zero => simp
  | succ l ih =>
    have hc := d_commute_chL hF (j := p) (p := p + 1 + 1) (l := l) (by omega)
    have ih' := ih (p + 1)
    rw [chL_succ (p + 1) l] at ih'
    rw [chL_succ p (l + 1), chL_succ (p + 1) l, chL_succ p l]
    simp only [mul_assoc] at ih' ⊢
    rw [← hc.left_comm, braid_assoc hF, ih', ← hc.left_comm]

/-- `R(p, q - 1) R(p, q) = R(p, q) R(p + 1, q)`. -/
theorem chR_mul_chR (p l : ℕ) :
    chR D p l * chR D p (l + 1) = chR D p (l + 1) * chR D (p + 1) l := by
  induction l generalizing p with
  | zero => simp
  | succ l ih =>
    have hc := d_commute_chR hF (j := p) (p := p + 1 + 1) (l := l) (by omega)
    have ih' := ih (p + 1)
    rw [chR_succ (p + 1) l] at ih'
    rw [chR_succ p (l + 1), chR_succ (p + 1) l, chR_succ p l]
    calc chR D (p + 1) l * D p * (chR D (p + 1 + 1) l * D (p + 1) * D p)
        = chR D (p + 1) l * (chR D (p + 1 + 1) l * D (p + 1)) * (D p * D (p + 1)) := by
          simp only [mul_assoc]
          rw [hc.left_comm, braid_assoc' hF]
      _ = chR D (p + 1 + 1) l * D (p + 1) * D p * (chR D (p + 1 + 1) l * D (p + 1)) := by
          rw [ih']
          simp only [mul_assoc]
          rw [hc.left_comm]

/-! ### Factorisations of the longest element -/

omit hF in
theorem map_w0Word_add_one (a n : ℕ) :
    ((w0Word n).map (a + ·)).map (· + 1) = (w0Word n).map ((a + 1) + ·) := by
  rw [List.map_map]; congr 1; funext j; simp only [Function.comp_apply]; omega

omit hF in
theorem mem_w0Word_map {a n j : ℕ} (h : j ∈ (w0Word n).map (a + ·)) : a ≤ j ∧ j + 1 < a + n := by
  obtain ⟨j', hj', rfl⟩ := List.mem_map.1 h
  have := lt_of_mem_w0Word hj'; omega

/-- `∂(n+1) = ∂'(n) · D_s ⋯ D_{s+n-1}`, where `∂'(n)` is the longest divided difference of the
last `n` strands `[s + 1, s + n + 1)`. -/
theorem wb_succ_eq_wb_mul_chL (s n : ℕ) : Wb D s (n + 1) = Wb D (s + 1) n * chL D s n := by
  induction n generalizing s with
  | zero => simp [wb_one, wb_zero]
  | succ n ih =>
    rw [wb_succ, ih s, ← mul_assoc, Wb, chL_mul_wp hF (fun j hj => by
      have := mem_w0Word_map hj; omega), map_w0Word_add_one, ← Wb, mul_assoc,
      chL_mul_chL hF s n, ← mul_assoc, ← ih (s + 1)]

/-- `∂(n+1) = D_{s+n-1} ⋯ D_s · ∂'(n)`. -/
theorem wb_succ_eq_chR_mul_wb (s n : ℕ) : Wb D s (n + 1) = chR D s n * Wb D (s + 1) n := by
  induction n generalizing s with
  | zero => simp [wb_one, wb_zero]
  | succ n ih =>
    have hs := chL_mul_wp hF (D := D) (p := s) (l := n + 1)
      (ρ := (w0Word n).map ((s + 1) + ·)) (fun j hj => by have := mem_w0Word_map hj; omega)
    rw [map_w0Word_add_one, ← Wb, ← Wb] at hs
    calc Wb D s (n + 1 + 1) = Wb D (s + 1) (n + 1) * chL D s (n + 1) :=
          wb_succ_eq_wb_mul_chL hF s (n + 1)
      _ = chR D (s + 1) n * (Wb D (s + 1 + 1) n * chL D s (n + 1)) := by rw [ih (s + 1), mul_assoc]
      _ = chR D (s + 1) n * (chL D s (n + 1) * Wb D (s + 1) n) := by rw [hs]
      _ = chR D s (n + 1) * (chL D (s + 1) n * Wb D (s + 1) n) := by
          rw [chR_succ, chL_succ]; simp only [mul_assoc]
      _ = chR D s (n + 1) * Wb D (s + 1) (n + 1) := by rw [wb_succ]

/-- `∂(n+1) = ∂(n) · D_{s+n-1} ⋯ D_s`. -/
theorem wb_succ_eq_wb_mul_chR (s n : ℕ) : Wb D s (n + 1) = Wb D s n * chR D s n := by
  rcases n with _ | n
  · simp [wb_one, wb_zero]
  have hs := wp_mul_chR hF (D := D) (p := s) (l := n + 1)
    (ρ := (w0Word n).map ((s + 1) + ·)) (fun j hj => by have := mem_w0Word_map hj; omega)
  rw [map_w0Word_add_one, ← Wb, ← Wb] at hs
  calc Wb D s (n + 1 + 1) = chR D s (n + 1) * (chR D (s + 1) n * Wb D (s + 1 + 1) n) := by
        rw [wb_succ_eq_chR_mul_wb hF s (n + 1), wb_succ_eq_chR_mul_wb hF (s + 1) n]
    _ = chR D s n * (Wb D (s + 1) n * chR D s (n + 1)) := by
        rw [hs, ← mul_assoc, ← mul_assoc, chR_mul_chR hF s n]
    _ = Wb D s (n + 1) * chR D s (n + 1) := by
        rw [wb_succ_eq_chR_mul_wb hF s n, mul_assoc]

/-- `∂(n) D_j = 0` for a crossing `D_j` of the block. -/
theorem wb_mul_d {s n j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) : Wb D s n * D j = 0 := by
  induction n generalizing s with
  | zero => omega
  | succ n ih =>
    by_cases hj : j + 1 < s + n
    · rw [wb_succ, mul_assoc, ih h₁ hj, mul_zero]
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain rfl : j = s + n := by omega
      rw [wb_succ_eq_wb_mul_chL hF, chL_succ', mul_assoc, mul_assoc, hF.d_sq, mul_zero,
        mul_zero]

/-- `D_j ∂(n) = 0` for a crossing `D_j` of the block. -/
theorem d_mul_wb {s n j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) : D j * Wb D s n = 0 := by
  induction n generalizing s j with
  | zero => omega
  | succ n ih =>
    rw [wb_succ_eq_chR_mul_wb hF]
    by_cases hj : j + 2 ≤ s + n
    · rw [← mul_assoc, d_mul_chR hF h₁ hj, mul_assoc, ih (by omega) (by omega), mul_zero]
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain rfl : j = s + n := by omega
      rw [chR_succ', ← mul_assoc, ← mul_assoc, hF.d_sq, zero_mul, zero_mul]

omit hF in
theorem map_range_eq_reverse_range' (s n : ℕ) :
    (List.range n).map (fun j => s + n - 1 - j) = (List.range' s n).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.range'_concat,
      List.reverse_append, List.reverse_singleton, List.singleton_append, ← ih]
    congr 1
    · omega
    · congr 1; funext j; simp only [Function.comp_apply]; omega

/-- The mirror image of the reduced word of `∂(n)` is again a reduced word of `∂(n)`. -/
theorem wp_w0Word_mirror (s n : ℕ) :
    wp D ((w0Word n).map fun j => s + n - 2 - j) = Wb D s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [w0Word_succ, List.map_append, wp_append, wb_succ_eq_chR_mul_wb hF, ← ih (s + 1)]
    congr 1
    · rw [chR, ← map_range_eq_reverse_range']
      congr 2
    · congr 2
      try (funext j; omega)

end relations

/-! ### Subfamilies and the mirror family -/

section families

variable {n : ℕ} {X : Fin n → B} {D : ℕ → B} (hF : IsNilHeckeFamily n X D)

/-- The dots of the block `[s, s + n')`. -/
def resX (X : Fin n → B) (s n' : ℕ) (h : s + n' ≤ n) : Fin n' → B :=
  fun a => X ⟨s + a, by omega⟩

/-- The crossings of the block `[s, s + n')` (zero outside the block). -/
def resD (D : ℕ → B) (s n' : ℕ) : ℕ → B := fun j => if j + 1 < n' then D (s + j) else 0

include hF in
/-- The dots and crossings of a block form a nilHecke family. -/
theorem isNilHeckeFamily_res (s n' : ℕ) (h : s + n' ≤ n) :
    IsNilHeckeFamily n' (resX X s n' h) (resD D s n') where
  x_comm a b := hF.x_comm _ _
  d_x_comm j a h₁ h₂ := by
    unfold resD resX
    split_ifs
    · exact hF.d_x_comm _ _ (by simp only; omega) (by simp only; omega)
    · simp
  d_comm j l hjl := by
    unfold resD
    split_ifs <;> first | exact hF.d_comm _ _ (by omega) | simp
  d_sq j := by
    unfold resD
    split_ifs
    · exact hF.d_sq _
    · simp
  braid j := by
    unfold resD
    split_ifs <;> first | (rw [show s + (j + 1) = s + j + 1 by omega]; exact hF.braid _) | simp
  x_d_sub j hj := by
    unfold resD resX
    rw [if_pos hj]
    have := hF.x_d_sub (s + j) (by omega)
    convert this using 4
  d_x_sub j hj := by
    unfold resD resX
    rw [if_pos hj]
    have := hF.d_x_sub (s + j) (by omega)
    convert this using 4
  d_zero j hj := by unfold resD; rw [if_neg (by omega)]

/-- The mirror image of the dots: `x_a ↦ x_{n-1-a}`. -/
def mirX (X : Fin n → B) : Fin n → B := fun a => X a.rev

/-- The mirror image of the crossings: `D_j ↦ -D_{n-2-j}`. -/
def mirD (n : ℕ) (D : ℕ → B) : ℕ → B := fun j => if j + 1 < n then -D (n - 2 - j) else 0

include hF in
/-- The mirror image of a nilHecke family is a nilHecke family. -/
theorem isNilHeckeFamily_mir : IsNilHeckeFamily n (mirX X) (mirD n D) where
  x_comm a b := hF.x_comm _ _
  d_x_comm j a h₁ h₂ := by
    unfold mirD mirX
    split_ifs
    · rw [neg_mul, mul_neg, hF.d_x_comm _ _ (by simp only [Fin.val_rev]; omega)
        (by simp only [Fin.val_rev]; omega)]
    · simp
  d_comm j l hjl := by
    unfold mirD
    split_ifs
    · rw [neg_mul_neg, neg_mul_neg]; exact (hF.d_comm _ _ (by omega)).symm
    all_goals simp
  d_sq j := by
    unfold mirD
    split_ifs
    · rw [neg_mul_neg, hF.d_sq]
    · simp
  braid j := by
    unfold mirD
    split_ifs
    · have := hF.braid (n - 2 - (j + 1))
      rw [show n - 2 - (j + 1) + 1 = n - 2 - j by omega] at this
      simp only [neg_mul, mul_neg, neg_neg, this]
    all_goals simp
  x_d_sub j hj := by
    unfold mirD mirX
    rw [if_pos hj]
    have := hF.d_x_sub (n - 2 - j) (by omega)
    rw [mul_neg, neg_mul, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
    convert this using 3 <;> (apply congrArg; ext; simp only [Fin.val_rev]; omega)
  d_x_sub j hj := by
    unfold mirD mirX
    rw [if_pos hj]
    have := hF.x_d_sub (n - 2 - j) (by omega)
    rw [mul_neg, neg_mul, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
    convert this using 3 <;> (apply congrArg; ext; simp only [Fin.val_rev]; omega)
  d_zero j hj := by unfold mirD; rw [if_neg (by omega)]

end families

/-! ### The idempotents `e_n` of blocks -/

section idempotents

variable {N : ℕ} {X : Fin N → B} {D : ℕ → B} (hF : IsNilHeckeFamily N X D)

/-- The dot `x_a` (and `1` outside the range). -/
def xN (X : Fin N → B) (a : ℕ) : B := if h : a < N then X ⟨a, h⟩ else 1

/-- `x^δ = x_s^{n-1} x_{s+1}^{n-2} ⋯ x_{s+n-2}` on the block `[s, s + n)`. -/
def Δb (X : Fin N → B) (s n : ℕ) : B :=
  (List.ofFn fun a : Fin n => xN X (s + a) ^ (n - 1 - a)).prod

/-- The idempotent `e_n = x^δ ∂(n)` of the block `[s, s + n)` (KL II: `e_{i,n}`). -/
def Eb (X : Fin N → B) (D : ℕ → B) (s n : ℕ) : B := Δb X s n * Wb D s n

theorem Δb_succ (s n : ℕ) : Δb X s (n + 1) = xN X s ^ n * Δb X (s + 1) n := by
  rw [Δb, List.ofFn_succ, List.prod_cons, Δb]
  congr 2
  refine congrArg List.ofFn (funext fun a => ?_)
  simp only [Fin.val_succ]
  rw [show s + ((a : ℕ) + 1) = s + 1 + a by omega, show n + 1 - 1 - ((a : ℕ) + 1) = n - 1 - a by
    omega]

include hF

theorem xN_commute (a b : ℕ) : Commute (xN X a) (xN X b) := by
  unfold xN; split_ifs
  · exact hF.x_comm _ _
  all_goals simp

theorem xN_commute_d {a j : ℕ} (h₁ : a ≠ j) (h₂ : a ≠ j + 1) : Commute (xN X a) (D j) := by
  unfold xN; split_ifs
  · exact (hF.d_x_comm j _ h₁ h₂).symm
  · exact Commute.one_left _

theorem xN_commute_wp {a : ℕ} {ρ : List ℕ} (h : ∀ j ∈ ρ, a ≠ j ∧ a ≠ j + 1) :
    Commute (xN X a) (wp D ρ) := by
  induction ρ with
  | nil => exact Commute.one_right _
  | cons j ρ ih =>
    rw [wp_cons]
    exact (xN_commute_d hF (h j List.mem_cons_self).1 (h j List.mem_cons_self).2).mul_right
      (ih fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))

theorem xN_commute_Δb (a s n : ℕ) : Commute (xN X a) (Δb X s n) := by
  rw [Δb]
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨b, rfl⟩ := List.mem_ofFn.1 hy
  exact (xN_commute hF a _).pow_right _

/-- **KL II, Lemma 5** (`∂(n) e_{i,n} = ∂(n)`), in the form `∂(n) x^δ ∂(n) = ∂(n)`, for every
block `[s, s + n)` of the family. -/
theorem wb_mul_Δb_mul_wb {s n : ℕ} (h : s + n ≤ N) :
    Wb D s n * Δb X s n * Wb D s n = Wb D s n := by
  have key := (isNilHeckeFamily_res hF s n h).key
  have hW : ((w0Word n).map (resD D s n)).prod = Wb D s n := by
    rw [Wb, wp, List.map_map]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    simp only [resD, Function.comp_apply, if_pos (lt_of_mem_w0Word hj)]
  have hΔ : (List.ofFn fun a : Fin n => resX X s n h a ^ (n - 1 - a)).prod = Δb X s n := by
    rw [Δb]; congr 2; funext a
    simp only [resX, xN, dif_pos (show s + (a : ℕ) < N by omega)]
  rwa [hW, hΔ] at key

theorem wb_mul_Δb_mul_wb_mul {s n : ℕ} (h : s + n ≤ N) (r : B) :
    Wb D s n * (Δb X s n * (Wb D s n * r)) = Wb D s n * r := by
  rw [← mul_assoc, ← mul_assoc, wb_mul_Δb_mul_wb hF h]

theorem eb_mul_eb {s n : ℕ} (h : s + n ≤ N) : Eb X D s n * Eb X D s n = Eb X D s n := by
  simp only [Eb, mul_assoc]
  rw [← mul_assoc (Wb D s n), wb_mul_Δb_mul_wb hF h]

/-- **KL II (10)**, left: `e_{n+1} (e_n ⊗ 1) = e_{n+1}`. -/
theorem eb_mul_eb_left {s n : ℕ} (h : s + n + 1 ≤ N) :
    Eb X D s (n + 1) * Eb X D s n = Eb X D s (n + 1) := by
  simp only [Eb, wb_succ, mul_assoc]
  rw [← mul_assoc (Wb D s n), wb_mul_Δb_mul_wb hF (s := s) (n := n) (by omega)]

/-- **KL II (10)**, right: `e_{n+1} (1 ⊗ e_n) = e_{n+1}`. -/
theorem eb_mul_eb_right {s n : ℕ} (h : s + n + 1 ≤ N) :
    Eb X D s (n + 1) * Eb X D (s + 1) n = Eb X D s (n + 1) := by
  simp only [Eb, wb_succ_eq_chR_mul_wb hF s n, mul_assoc]
  rw [← mul_assoc (Wb D (s + 1) n), wb_mul_Δb_mul_wb hF (s := s + 1) (n := n) (by omega)]

/-- **KL II (11)**, left: `(e_n ⊗ 1) D_{n} ⋯ D_1 e_{n+1} = (e_n ⊗ 1) D_{n} ⋯ D_1`
(the strand at the bottom position `s` moves to the top position `s + n`). -/
theorem eb_mul_chR_mul_eb {s n : ℕ} (h : s + n + 1 ≤ N) :
    Eb X D s n * chR D s n * Eb X D s (n + 1) = Eb X D s n * chR D s n := by
  have e1 : Eb X D s n * chR D s n = Δb X s n * Wb D s (n + 1) := by
    rw [Eb, mul_assoc, ← wb_succ_eq_wb_mul_chR hF]
  rw [e1, Eb, mul_assoc, ← mul_assoc (Wb D s (n + 1)),
    wb_mul_Δb_mul_wb hF (s := s) (n := n + 1) h]

/-- **KL II (11)**, right: `(1 ⊗ e_n) D_1 ⋯ D_n e_{n+1} = (1 ⊗ e_n) D_1 ⋯ D_n`
(the strand at the bottom position `s + n` moves to the top position `s`). -/
theorem eb_mul_chL_mul_eb {s n : ℕ} (h : s + n + 1 ≤ N) :
    Eb X D (s + 1) n * chL D s n * Eb X D s (n + 1) = Eb X D (s + 1) n * chL D s n := by
  have e1 : Eb X D (s + 1) n * chL D s n = Δb X (s + 1) n * Wb D s (n + 1) := by
    rw [Eb, mul_assoc, ← wb_succ_eq_wb_mul_chL hF]
  rw [e1, Eb, mul_assoc, ← mul_assoc (Wb D s (n + 1)),
    wb_mul_Δb_mul_wb hF (s := s) (n := n + 1) h]

/-- `e_n D_j = 0` for a crossing `D_j` of the block. -/
theorem eb_mul_d {s n j : ℕ} (h₁ : s ≤ j) (h₂ : j + 1 < s + n) : Eb X D s n * D j = 0 := by
  rw [Eb, mul_assoc, wb_mul_d hF h₁ h₂, mul_zero]

/-- `e_{n+1} = x_s^n (1 ⊗ e_n) D_s ⋯ D_{s+n-1}`. -/
theorem eb_succ_eq {s n : ℕ} : Eb X D s (n + 1) = xN X s ^ n * Eb X D (s + 1) n * chL D s n := by
  rw [Eb, Δb_succ, wb_succ_eq_wb_mul_chL hF, Eb]; simp only [mul_assoc]

theorem xN_commute_eb {a s n : ℕ} (h : a < s ∨ s + n ≤ a) : Commute (xN X a) (Eb X D s n) :=
  (xN_commute_Δb hF a s n).mul_right (xN_commute_wp hF fun j hj => by
    have := mem_w0Word_map hj; omega)

/-- **KL II (12)**: `e_{n+1} x_s^a D_s ⋯ D_{s+n-1} = 0` for `a < n` and `= e_{n+1}` for `a = n`
(the strand at the bottom position `s + n`, carrying `a` dots at its top, moves to the top
position `s`). -/
theorem eb_mul_x_pow_mul_chL {s n a : ℕ} (h : s + n + 1 ≤ N) (ha : a ≤ n) :
    Eb X D s (n + 1) * xN X s ^ a * chL D s n = if a = n then Eb X D s (n + 1) else 0 := by
  induction n generalizing a with
  | zero =>
    obtain rfl : a = 0 := by omega
    simp
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with ha' | ha'
    · rw [if_neg (by omega), ← eb_mul_eb_left hF h, chL_succ']
      calc Eb X D s (n + 1 + 1) * Eb X D s (n + 1) * xN X s ^ a * (chL D s n * D (s + n))
          = Eb X D s (n + 1 + 1) * (Eb X D s (n + 1) * xN X s ^ a * chL D s n) * D (s + n) := by
            simp only [mul_assoc]
        _ = 0 := by
            rw [ih (by omega) (by omega)]
            split_ifs
            · rw [eb_mul_eb_left hF h, eb_mul_d hF (by omega) (by omega)]
            · simp
    · obtain rfl : a = n + 1 := by omega
      rw [if_pos rfl]
      calc Eb X D s (n + 1 + 1) * xN X s ^ (n + 1) * chL D s (n + 1)
          = Eb X D s (n + 1 + 1) * Eb X D (s + 1) (n + 1) * xN X s ^ (n + 1) *
              chL D s (n + 1) := by rw [eb_mul_eb_right hF h]
        _ = Eb X D s (n + 1 + 1) * (xN X s ^ (n + 1) * Eb X D (s + 1) (n + 1) *
              chL D s (n + 1)) := by
            rw [((xN_commute_eb hF (Or.inl (Nat.lt_succ_self s))).pow_left (n + 1)).eq]
            simp only [mul_assoc]
        _ = Eb X D s (n + 1 + 1) := by
            rw [← eb_succ_eq hF, eb_mul_eb hF (s := s) (n := n + 1 + 1) (by omega)]

omit hF in
theorem prod_map_neg (f : ℕ → B) (ρ : List ℕ) :
    (ρ.map fun j => -f j).prod = (-1) ^ ρ.length * (ρ.map f).prod := by
  induction ρ with
  | nil => simp
  | cons j ρ ih =>
    have hc := (Commute.neg_one_left (f j)).pow_left ρ.length
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.length_cons,
      pow_succ, mul_neg_one, neg_mul, neg_mul]
    congr 1
    rw [← mul_assoc, ← mul_assoc, hc.eq]

omit hF in
theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : B) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- **KL II (13)**: `e_{n+1} x_{s+n}^a D_{s+n-1} ⋯ D_s = 0` for `a < n` and
`= (-1)^n e_{n+1}` for `a = n` (the strand at the bottom position `s`, carrying `a` dots at its
top, moves to the top position `s + n`). Proved from (12) for the mirror family. -/
theorem eb_mul_x_pow_mul_chR {s n a : ℕ} (h : s + n + 1 ≤ N) (ha : a ≤ n) :
    Eb X D s (n + 1) * xN X (s + n) ^ a * chR D s n =
      if a = n then (-1) ^ n * Eb X D s (n + 1) else 0 := by
  have hR := isNilHeckeFamily_res hF s (n + 1) h
  have hM := isNilHeckeFamily_mir hR
  set XM := mirX (resX X s (n + 1) h)
  set DM := mirD (n + 1) (resD D s (n + 1))
  have hDM : ∀ j, j + 1 < n + 1 → DM j = -D (s + n - 1 - j) := by
    intro j hj
    simp only [DM, mirD, resD, if_pos hj, if_pos (show n + 1 - 2 - j + 1 < n + 1 by omega)]
    congr 2; omega
  have m1 : xN XM 0 = xN X (s + n) := by
    simp only [xN, dif_pos (show 0 < n + 1 by omega), dif_pos (show s + n < N by omega), XM,
      mirX, resX]
    congr 2
  have m2 : chL DM 0 n = (-1) ^ n * chR D s n := by
    rw [chL, wp, List.map_congr_left (g := fun j => -D (s + n - 1 - j)) (fun j hj => by
      rw [List.mem_range'_1] at hj; exact hDM j (by omega)), prod_map_neg,
      List.length_range', chR, wp, ← map_range_eq_reverse_range', List.map_map,
      List.range_eq_range']
    rfl
  set ε : B := (-1) ^ (n + 1).choose 2
  have hε : ε * ε = 1 := neg_one_pow_mul_self _
  have hεc : ∀ y : B, Commute ε y := fun y => (Commute.neg_one_left y).pow_left _
  have m3 : Wb DM 0 (n + 1) = ε * Wb D s (n + 1) := by
    rw [Wb, wp, List.map_map, List.map_congr_left (g := fun j => -D (s + (n + 1) - 2 - j))
      (fun j hj => by
        simp only [Function.comp_apply, zero_add]
        rw [hDM j (lt_of_mem_w0Word hj), show s + (n + 1) - 2 - j = s + n - 1 - j by omega]),
      prod_map_neg, length_w0Word, ← wp_w0Word_mirror hF s (n + 1), wp, List.map_map]
    rfl
  have key := wb_mul_Δb_mul_wb hM (s := 0) (n := n + 1) (by omega)
  rw [m3] at key
  have hW : Wb D s (n + 1) * Δb XM 0 (n + 1) * Wb D s (n + 1) = ε * Wb D s (n + 1) := by
    rw [← key]
    simp only [mul_assoc]
    rw [← (hεc (Δb XM 0 (n + 1))).left_comm, ← (hεc (Wb D s (n + 1))).left_comm,
      ← mul_assoc ε ε, hε, one_mul]
  have hEE : Eb X D s (n + 1) * Eb XM DM 0 (n + 1) = Eb X D s (n + 1) := by
    rw [Eb, Eb, m3]
    simp only [mul_assoc]
    rw [← (hεc (Δb XM 0 (n + 1))).left_comm, ← (hεc (Wb D s (n + 1))).left_comm,
      ← mul_assoc (Wb D s (n + 1)) (Δb XM 0 (n + 1)), hW, ← mul_assoc ε ε, hε, one_mul]
  have i6 := eb_mul_x_pow_mul_chL hM (s := 0) (n := n) (a := a) (by omega) ha
  rw [m1, m2] at i6
  have hP : ∀ y : B, Commute ((-1 : B) ^ n) y := fun y => (Commute.neg_one_left y).pow_left n
  have e2 : Eb XM DM 0 (n + 1) * xN X (s + n) ^ a * chR D s n =
      (-1) ^ n * (Eb XM DM 0 (n + 1) * xN X (s + n) ^ a * ((-1) ^ n * chR D s n)) := by
    rw [← mul_assoc (Eb XM DM 0 (n + 1) * xN X (s + n) ^ a), ← (hP _).eq, ← mul_assoc,
      ← mul_assoc, neg_one_pow_mul_self, one_mul]
  calc Eb X D s (n + 1) * xN X (s + n) ^ a * chR D s n
      = Eb X D s (n + 1) * (Eb XM DM 0 (n + 1) * xN X (s + n) ^ a * chR D s n) := by
        conv_lhs => rw [← hEE]
        simp only [mul_assoc]
    _ = Eb X D s (n + 1) * ((-1) ^ n * (if a = n then Eb XM DM 0 (n + 1) else 0)) := by
        rw [e2, i6]
    _ = if a = n then (-1) ^ n * Eb X D s (n + 1) else 0 := by
        split_ifs
        · rw [← mul_assoc, ← (hP _).eq, mul_assoc, hEE]
        · simp

end idempotents

/-! ### Images under ring homomorphisms -/

section map

variable {B' : Type*} [Ring B'] (f : B →+* B') {N : ℕ} (X : Fin N → B) (D : ℕ → B)

theorem wp_map (ρ : List ℕ) : wp (f ∘ D) ρ = f (wp D ρ) := by
  simp [wp, map_list_prod, List.map_map]

theorem chL_map (p l : ℕ) : chL (f ∘ D) p l = f (chL D p l) := wp_map f D _

theorem chR_map (p l : ℕ) : chR (f ∘ D) p l = f (chR D p l) := wp_map f D _

theorem wb_map (s n : ℕ) : Wb (f ∘ D) s n = f (Wb D s n) := wp_map f D _

theorem xN_map (a : ℕ) : xN (f ∘ X) a = f (xN X a) := by
  unfold xN; split_ifs <;> simp

theorem Δb_map (s n : ℕ) : Δb (f ∘ X) s n = f (Δb X s n) := by
  simp only [Δb, xN_map, map_list_prod, List.map_ofFn, Function.comp_def, map_pow]
  congr 2; funext a; rw [← xN_map]; rfl

theorem eb_map (s n : ℕ) : Eb (f ∘ X) (f ∘ D) s n = f (Eb X D s n) := by
  rw [Eb, Eb, Δb_map, wb_map, map_mul]

end map

end Categorification.KLR.KL2.NH
