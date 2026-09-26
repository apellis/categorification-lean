/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.MackeyIntertwine

/-!
# The refined Mackey factorisation of a permutation

Combinatorics for Khovanov–Lauda I (arXiv:0803.4121v2), §2.6, **Proposition 2.18**. Let `d` be
the minimal double coset representative of `(S_n × S_{n'}) \ S_m / (S_{n''} × S_{n'''})` with
`c = crossCount n n'' d` crossing strands, and write `n = a + c`, `n' = g + e`, `n'' = a + g`,
`n''' = c + e` (the four blocks of strands of `d`: the paper's `ν - λ`, `λ`, `ν' + λ - ν'''`,
`ν''' - λ`). Then every permutation `w` in the double coset of `d` factors **uniquely** as

`w = (u₁ × u₂) · d · (Y × Y')`,

with `u₁ ∈ S_n` a minimal left coset representative for `S_a × S_c` (`IsShuffle hA u₁⁻¹`),
`u₂ ∈ S_{n'}` a minimal left coset representative for `S_g × S_e`, and `Y ∈ S_{n''}`,
`Y' ∈ S_{n'''}` arbitrary; moreover lengths add up. This is the factorisation underlying the
isomorphism of the Mackey subquotients with the balanced tensor products
`(R(ν) 1_{ν-λ,λ} ⊗ R(ν') 1_{…}) ⊗_{R'} (1_{…} R(ν'') ⊗ 1_{λ,…} R(ν'''))`.

## Main results

* `TypeA.blockPerm_val` : the values of a block permutation.
* `TypeA.IsDoubleShuffle.blockPerm_mul_eq` : `((a₁ × a₂) × (b₁ × b₂)) · d = d · ((a₁ × b₁) × (a₂ × b₂))`.
* `TypeA.IsDoubleShuffle.isShuffle_inv_mul` : for minimal coset representatives `u₁`, `u₂`,
  `d⁻¹ (u₁ × u₂)⁻¹` is a shuffle for the bottom blocks.
* `TypeA.IsDoubleShuffle.exists_refinedFactor` (existence, with lengths adding up) and
  `TypeA.IsDoubleShuffle.refinedFactor_unique` (uniqueness).
-/

namespace Categorification.TypeA

open Equiv

section BlockVal

variable {n n' m : ℕ} (h : n + n' = m)

theorem blockPerm_val (a : Perm (Fin n)) (b : Perm (Fin n')) (p : Fin m) :
    (blockPerm h a b p).val = if hp : p.val < n then (a ⟨p.val, hp⟩).val
      else n + (b ⟨p.val - n, by have := p.2; omega⟩).val := by
  obtain ⟨s, rfl⟩ := (blockEquiv h).surjective p
  cases s with
  | inl x =>
    rw [blockPerm_inl, blockEquiv_inl_val, dif_pos (by simp)]
    rfl
  | inr y =>
    rw [blockPerm_inr, blockEquiv_inr_val, dif_neg (by simp)]
    congr 3
    ext; simp

end BlockVal

/-- `IsShuffle hA u⁻¹`: `u` is increasing on the first `a` and on the last `c` positions. -/
theorem isShuffle_inv_iff {N a c : ℕ} (hA : a + c = N) (u : Perm (Fin N)) :
    IsShuffle hA u⁻¹ ↔ ∀ j (hj : j + 1 < N), (j + 1 < a ∨ a ≤ j) →
      u ⟨j, by omega⟩ < u ⟨j + 1, hj⟩ := by
  rw [isShuffle_iff_forall]
  simp only [inv_inv]

variable {m n n' n'' n''' : ℕ} {hJ : n + n' = m} {hK : n'' + n''' = m}
  {d : Perm (Fin m)} (hd : IsDoubleShuffle hJ hK d)
  {a c g e : ℕ} (hA : a + c = n) (hG : g + e = n') (hAG : a + g = n'') (hCE : c + e = n''')
  (hc : crossCount n n'' d = c)

include hd hA hG hAG hc in
theorem IsDoubleShuffle.val_eq_blocks (p : Fin m) :
    (d p).val = if p.val < a then p.val
      else if p.val < n'' then p.val + c
      else if p.val < n'' + c then p.val - g
      else p.val := by
  rw [hd.val_eq_ite hJ hK, hc]
  have : n - c = a := by omega
  rw [this]
  split_ifs <;> omega

include hd hA hG hAG hc in
theorem IsDoubleShuffle.apply_α (y : Fin a) :
    d (blockEquiv hK (Sum.inl (blockEquiv hAG (Sum.inl y)))) =
      blockEquiv hJ (Sum.inl (blockEquiv hA (Sum.inl y))) := by
  have := y.2
  ext; rw [hd.val_eq_blocks hA hG hAG hc]
  simp only [blockEquiv_inl_val, blockEquiv_inr_val]; split_ifs; omega

include hd hA hG hAG hc in
theorem IsDoubleShuffle.apply_γ (y : Fin g) :
    d (blockEquiv hK (Sum.inl (blockEquiv hAG (Sum.inr y)))) =
      blockEquiv hJ (Sum.inr (blockEquiv hG (Sum.inl y))) := by
  have := y.2
  ext; rw [hd.val_eq_blocks hA hG hAG hc]
  simp only [blockEquiv_inl_val, blockEquiv_inr_val]; split_ifs <;> omega

include hd hA hG hAG hCE hc in
theorem IsDoubleShuffle.apply_β (y : Fin c) :
    d (blockEquiv hK (Sum.inr (blockEquiv hCE (Sum.inl y)))) =
      blockEquiv hJ (Sum.inl (blockEquiv hA (Sum.inr y))) := by
  have := y.2
  ext; rw [hd.val_eq_blocks hA hG hAG hc]
  simp only [blockEquiv_inl_val, blockEquiv_inr_val]; split_ifs <;> omega

include hd hA hG hAG hCE hc in
theorem IsDoubleShuffle.apply_δ (y : Fin e) :
    d (blockEquiv hK (Sum.inr (blockEquiv hCE (Sum.inr y)))) =
      blockEquiv hJ (Sum.inr (blockEquiv hG (Sum.inr y))) := by
  have := y.2
  ext; rw [hd.val_eq_blocks hA hG hAG hc]
  simp only [blockEquiv_inl_val, blockEquiv_inr_val]; split_ifs <;> omega

include hd hA hG hAG hCE hc in
/-- **Block permutations slide through `d`**:
`((a₁ × a₂) × (b₁ × b₂)) · d = d · ((a₁ × b₁) × (a₂ × b₂))`. -/
theorem IsDoubleShuffle.blockPerm_mul_eq (a₁ : Perm (Fin a)) (a₂ : Perm (Fin c))
    (b₁ : Perm (Fin g)) (b₂ : Perm (Fin e)) :
    blockPerm hJ (blockPerm hA a₁ a₂) (blockPerm hG b₁ b₂) * d =
      d * blockPerm hK (blockPerm hAG a₁ b₁) (blockPerm hCE a₂ b₂) := by
  ext1 p
  obtain ⟨s, rfl⟩ := (blockEquiv hK).surjective p
  rcases s with x | x
  · obtain ⟨t, rfl⟩ := (blockEquiv hAG).surjective x
    rcases t with y | y
    · simp only [Perm.mul_apply, blockPerm_inl, hd.apply_α hA hG hAG hc]
    · simp only [Perm.mul_apply, blockPerm_inl, blockPerm_inr, hd.apply_γ hA hG hAG hc]
  · obtain ⟨t, rfl⟩ := (blockEquiv hCE).surjective x
    rcases t with y | y
    · simp only [Perm.mul_apply, blockPerm_inl, blockPerm_inr, hd.apply_β hA hG hAG hCE hc]
    · simp only [Perm.mul_apply, blockPerm_inr, hd.apply_δ hA hG hAG hCE hc]

omit hA hG hAG hCE in
/-- A function on `Fin N = Fin a ⊕ Fin g` which is strictly monotone on both blocks and takes
smaller values on the first block is strictly monotone. -/
theorem strictMono_of_blocks {N : ℕ} (h : a + g = N) {β : Type*} [LinearOrder β]
    {f : Fin N → β} (h₁ : StrictMono fun y => f (blockEquiv h (Sum.inl y)))
    (h₂ : StrictMono fun y => f (blockEquiv h (Sum.inr y)))
    (h₃ : ∀ y y', f (blockEquiv h (Sum.inl y)) < f (blockEquiv h (Sum.inr y'))) :
    StrictMono f := by
  intro p q hpq
  obtain ⟨s, rfl⟩ := (blockEquiv h).surjective p
  obtain ⟨t, rfl⟩ := (blockEquiv h).surjective q
  rcases s with y | y <;> rcases t with y' | y'
  · exact h₁ ((blockEquiv_inl_lt_inl h).1 hpq)
  · exact h₃ y y'
  · exact absurd hpq (not_blockEquiv_inr_lt_inl h y' y)
  · exact h₂ ((blockEquiv_inr_lt_inr h).1 hpq)

include hd hA hG hAG hCE hc in
/-- For minimal left coset representatives `u₁` (of `S_a × S_c` in `S_n`) and `u₂` (of `S_g × S_e`
in `S_{n'}`), `d⁻¹ (u₁ × u₂)⁻¹` is a shuffle for the bottom blocks `S_{n''} × S_{n'''}`. -/
theorem IsDoubleShuffle.isShuffle_inv_mul {u₁ : Perm (Fin n)} {u₂ : Perm (Fin n')}
    (hu₁ : IsShuffle hA u₁⁻¹) (hu₂ : IsShuffle hG u₂⁻¹) :
    IsShuffle hK (d⁻¹ * (blockPerm hJ u₁ u₂)⁻¹) := by
  simp only [IsShuffle, inv_inv] at hu₁ hu₂
  simp only [IsShuffle, mul_inv_rev, inv_inv, Perm.mul_apply]
  constructor
  · refine strictMono_of_blocks hAG ?_ ?_ ?_
    · intro y y' hy
      simp only [hd.apply_α hA hG hAG hc, blockPerm_inl]
      exact (blockEquiv_inl_lt_inl hJ).2 (hu₁.1 hy)
    · intro y y' hy
      simp only [hd.apply_γ hA hG hAG hc, blockPerm_inr]
      exact (blockEquiv_inr_lt_inr hJ).2 (hu₂.1 hy)
    · intro y y'
      simp only [hd.apply_α hA hG hAG hc, hd.apply_γ hA hG hAG hc, blockPerm_inl,
        blockPerm_inr]
      exact blockEquiv_inl_lt_inr hJ _ _
  · refine strictMono_of_blocks hCE ?_ ?_ ?_
    · intro y y' hy
      simp only [hd.apply_β hA hG hAG hCE hc, blockPerm_inl]
      exact (blockEquiv_inl_lt_inl hJ).2 (hu₁.2 hy)
    · intro y y' hy
      simp only [hd.apply_δ hA hG hAG hCE hc, blockPerm_inr]
      exact (blockEquiv_inr_lt_inr hJ).2 (hu₂.2 hy)
    · intro y y'
      simp only [hd.apply_β hA hG hAG hCE hc, hd.apply_δ hA hG hAG hCE hc, blockPerm_inl,
        blockPerm_inr]
      exact blockEquiv_inl_lt_inr hJ _ _

include hd hA hG hAG hCE hc in
/-- **Existence of the refined Mackey factorisation**
`w = (u₁ × u₂) · d · (Y × Y')`, with lengths adding up. -/
theorem IsDoubleShuffle.exists_refinedFactor (w : Perm (Fin m))
    (hw : crossCount n n'' w = c) :
    ∃ (u₁ : Perm (Fin n)) (u₂ : Perm (Fin n')) (Y : Perm (Fin n'')) (Y' : Perm (Fin n''')),
      IsShuffle hA u₁⁻¹ ∧ IsShuffle hG u₂⁻¹ ∧ w = blockPerm hJ u₁ u₂ * d * blockPerm hK Y Y' ∧
      length m w = length n u₁ + length n' u₂ + length m d + (length n'' Y + length n''' Y') := by
  obtain ⟨A, B, d', y, y', hd', hw', hl⟩ := mackey_factorisation hJ hK w
  have hdd : d' = d := by
    refine hd'.eq_of_crossCount_eq hJ hK hd ?_
    rw [hc, ← hw, hw', crossCount_mul_blockPerm, crossCount_blockPerm_mul]
  rw [hdd] at hw' hl
  obtain ⟨x₁, x₂, v₁, hv₁, hA'⟩ := exists_blockPerm_mul hA A⁻¹
  obtain ⟨z₁, z₂, v₂, hv₂, hB'⟩ := exists_blockPerm_mul hG B⁻¹
  have hlA : length n A = length a x₁ + length c x₂ + length n v₁ := by
    rw [← length_inv A, ← hA', length_blockPerm_mul hA _ _ hv₁]
  have hlB : length n' B = length g z₁ + length e z₂ + length n' v₂ := by
    rw [← length_inv B, ← hB', length_blockPerm_mul hG _ _ hv₂]
  have eA : A = v₁⁻¹ * blockPerm hA x₁⁻¹ x₂⁻¹ := by
    rw [← blockPerm_inv, ← mul_inv_rev, hA', inv_inv]
  have eB : B = v₂⁻¹ * blockPerm hG z₁⁻¹ z₂⁻¹ := by
    rw [← blockPerm_inv, ← mul_inv_rev, hB', inv_inv]
  refine ⟨v₁⁻¹, v₂⁻¹, blockPerm hAG x₁⁻¹ z₁⁻¹ * y, blockPerm hCE x₂⁻¹ z₂⁻¹ * y',
    by rwa [inv_inv], by rwa [inv_inv], ?_, ?_⟩
  · rw [hw', eA, eB, ← blockPerm_mul, mul_assoc (blockPerm hJ v₁⁻¹ v₂⁻¹),
      hd.blockPerm_mul_eq hA hG hAG hCE hc, ← blockPerm_mul]
    simp only [mul_assoc]
  · have h1 := length_mul_le (blockPerm hAG x₁⁻¹ z₁⁻¹) y
    have h2 := length_mul_le (blockPerm hCE x₂⁻¹ z₂⁻¹) y'
    rw [length_blockPerm, length_inv, length_inv] at h1 h2
    have h3 := length_mul_le (blockPerm hJ v₁⁻¹ v₂⁻¹ * d)
      (blockPerm hK (blockPerm hAG x₁⁻¹ z₁⁻¹ * y) (blockPerm hCE x₂⁻¹ z₂⁻¹ * y'))
    rw [length_blockPerm_mul hJ _ _ hd.1, length_blockPerm] at h3
    have hw'' : w = blockPerm hJ v₁⁻¹ v₂⁻¹ * d *
        blockPerm hK (blockPerm hAG x₁⁻¹ z₁⁻¹ * y) (blockPerm hCE x₂⁻¹ z₂⁻¹ * y') := by
      rw [hw', eA, eB, ← blockPerm_mul, mul_assoc (blockPerm hJ v₁⁻¹ v₂⁻¹),
        hd.blockPerm_mul_eq hA hG hAG hCE hc, ← blockPerm_mul]
      simp only [mul_assoc]
    rw [← hw''] at h3
    rw [length_inv, length_inv]
    rw [length_inv, length_inv] at h3
    omega

include hd hA hG hAG hCE hc in
/-- **Uniqueness of the refined Mackey factorisation.** -/
theorem IsDoubleShuffle.refinedFactor_unique {u₁ u₁' : Perm (Fin n)} {u₂ u₂' : Perm (Fin n')}
    {Y Z : Perm (Fin n'')} {Y' Z' : Perm (Fin n''')} (hu₁ : IsShuffle hA u₁⁻¹)
    (hu₂ : IsShuffle hG u₂⁻¹) (hu₁' : IsShuffle hA u₁'⁻¹) (hu₂' : IsShuffle hG u₂'⁻¹)
    (he : blockPerm hJ u₁ u₂ * d * blockPerm hK Y Y' = blockPerm hJ u₁' u₂' * d * blockPerm hK Z Z') :
    u₁ = u₁' ∧ u₂ = u₂' ∧ Y = Z ∧ Y' = Z' := by
  have hv := hd.isShuffle_inv_mul hA hG hAG hCE hc hu₁ hu₂
  have hv' := hd.isShuffle_inv_mul hA hG hAG hCE hc hu₁' hu₂'
  have he' : blockPerm hK Y⁻¹ Y'⁻¹ * (d⁻¹ * (blockPerm hJ u₁ u₂)⁻¹) =
      blockPerm hK Z⁻¹ Z'⁻¹ * (d⁻¹ * (blockPerm hJ u₁' u₂')⁻¹) := by
    rw [← blockPerm_inv, ← blockPerm_inv, ← mul_inv_rev, ← mul_inv_rev, ← mul_inv_rev,
      ← mul_inv_rev, he]
  obtain ⟨h1, h2, h3⟩ := blockPerm_mul_injective hK hv hv' he'
  have h4 := blockPerm_injective hJ (inv_injective (mul_left_cancel h3))
  exact ⟨h4.1, h4.2, inv_injective h1, inv_injective h2⟩

/-! ### Right parabolic factorisations -/

section Right

variable {N a c : ℕ} (hA : a + c = N)

theorem exists_rightFac (w : Perm (Fin N)) :
    ∃ x : Perm (Fin N) × Perm (Fin a) × Perm (Fin c), IsShuffle hA x.1⁻¹ ∧
      w = x.1 * blockPerm hA x.2.1 x.2.2 ∧
      length N w = length N x.1 + length a x.2.1 + length c x.2.2 := by
  obtain ⟨y₁, y₂, v, hv, hw⟩ := exists_blockPerm_mul hA w⁻¹
  refine ⟨(v⁻¹, y₁⁻¹, y₂⁻¹), by rwa [inv_inv], ?_, ?_⟩
  · rw [← blockPerm_inv, ← mul_inv_rev, hw, inv_inv]
  · rw [← length_inv w, ← hw, length_blockPerm_mul hA _ _ hv, length_inv, length_inv, length_inv]
    ring

/-- The factorisation `w = u (y₁ × y₂)` with `u` a minimal left coset representative. -/
noncomputable def rightFac (w : Perm (Fin N)) : Perm (Fin N) × Perm (Fin a) × Perm (Fin c) :=
  Classical.choose (exists_rightFac hA w)

theorem rightFac_spec (w : Perm (Fin N)) :
    IsShuffle hA (rightFac hA w).1⁻¹ ∧ w = (rightFac hA w).1 * blockPerm hA (rightFac hA w).2.1
      (rightFac hA w).2.2 ∧ length N w = length N (rightFac hA w).1 + length a (rightFac hA w).2.1 +
        length c (rightFac hA w).2.2 :=
  Classical.choose_spec (exists_rightFac hA w)

/-- The reduced word `σ(u) σ(y₁) (a + σ(y₂))` of `w = u (y₁ × y₂)`. -/
noncomputable def rightWord (w : Perm (Fin N)) : List ℕ :=
  canWord N (rightFac hA w).1 ++
    (canWord a (rightFac hA w).2.1 ++ shiftWord a (canWord c (rightFac hA w).2.2))

theorem rightWord_spec (w : Perm (Fin N)) :
    IsReduced N (rightWord hA w) ∧ wordProd N (rightWord hA w) = w := by
  obtain ⟨-, hw, hl⟩ := rightFac_spec hA w
  have hv : ValidWord N (rightWord hA w) := by
    simp only [rightWord, validWord_append]
    exact ⟨validWord_canWord _ _, (validWord_canWord _ _).of_le (by omega),
      (validWord_canWord _ _).shiftWord hA⟩
  have hprod : wordProd N (rightWord hA w) = w := by
    rw [rightWord, wordProd_append, wordProd_append_shiftWord hA (validWord_canWord _ _)
      (validWord_canWord _ _), wordProd_canWord, wordProd_canWord, wordProd_canWord, ← hw]
  refine ⟨(isReduced_iff_length_le hv).2 ?_, hprod⟩
  rw [hprod, hl]
  simp only [rightWord, List.length_append, length_shiftWord, length_canWord]
  omega

end Right

end Categorification.TypeA
