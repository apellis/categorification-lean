/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.NilHecke
import Categorification.TypeA.Inversions
import Mathlib.Data.Sym.Card

/-!
# The idempotent `e_m = x^δ ∂_{w_0}` of the nilHecke ring

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2, Example 3 (TeX lines ~685–700):

  "Define `e_m = x_1^{m-1} x_2^{m-2} ⋯ x_{m-1} ∂_{w_0}`, where `w_0` is the longest
  permutation. This element is an idempotent of degree `0`. We will also use the idempotent
  `ψ(e_m) = ∂_{w_0} x_1^{m-1} x_2^{m-2} ⋯ x_{m-1}`."

Positions are zero-indexed: `x^δ = ∏_a x_a^{m-1-a}` (`xDelta`).

## Main definitions

* `NilHecke.w0Word n` : the word `[0, 1, …, n-2] ++ w0Word (n-1)` of length `n choose 2`;
  for `n = m` it is a reduced word (`isReduced_w0Word`) of the longest element
  `longest m = wordProd m (w0Word m)` (`length_longest`, `length_le_length_longest`).
* `NilHecke.xDelta n` : `x^δ = ∏_{a < n} x_a^{n-1-a}`.
* `NilHecke.idemNH m = x^δ ∂_{w_0}` and `NilHecke.idemNH' m = ∂_{w_0} x^δ` (`= ψ(e_m)`).

## Main results

* `ddw_w0Word_xDelta` : `∂_{w_0}(x^δ) = 1`.
* `dd_mul_ddw_w0Word` : `∂_a ∂_{w_0} = 0` for all `a` (the image of `∂_{w_0}` is symmetric).
* `ddw_w0Word_mul_xDelta_mul_ddw_w0Word` : the key identity `∂_{w_0} x^δ ∂_{w_0} = ∂_{w_0}`.
* `isIdempotentElem_idemNH`, `isIdempotentElem_idemNH'` : **KL I §2.2, Example 3**: `e_m` and
  `ψ(e_m)` are idempotents (over any commutative ring `k`).

The degree-zero statement and the transport to the KLR algebras (blocks of strands of
`R(ν)`) are in `Categorification.KLR.DividedPowerIdempotents`.
-/

namespace Categorification.NilHecke

open MvPolynomial Equiv TypeA

/-! ### The word `w0Word` -/

/-- The word `w0Word n = [0, 1, …, n-2] ++ w0Word (n-1)`, a reduced word for the longest
element of `S_n` (`isReduced_w0Word`). For instance `w0Word 3 = [0, 1, 0]`. -/
def w0Word : ℕ → List ℕ
  | 0 => []
  | n + 1 => List.range n ++ w0Word n

theorem w0Word_succ (n : ℕ) : w0Word (n + 1) = List.range n ++ w0Word n := rfl

theorem lt_of_mem_w0Word {n j : ℕ} (h : j ∈ w0Word n) : j + 1 < n := by
  induction n with
  | zero => simp [w0Word] at h
  | succ n ih =>
    rw [w0Word_succ, List.mem_append, List.mem_range] at h
    rcases h with h | h
    · omega
    · have := ih h; omega

theorem length_w0Word (n : ℕ) : (w0Word n).length = n.choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [w0Word_succ, List.length_append, List.length_range, ih, Nat.choose_succ_succ',
      Nat.choose_one_right]

theorem validWord_w0Word {m n : ℕ} (h : n ≤ m) : ValidWord m (w0Word n) :=
  fun _ hj => by have := lt_of_mem_w0Word hj; omega

/-! ### Every permutation has at most `m choose 2` inversions -/

theorem invCount_le_choose (m : ℕ) (w : Perm (Fin m)) : invCount m w ≤ m.choose 2 := by
  classical
  have ht : ((Finset.univ : Finset (Sym2 (Fin m))).filter fun z => ¬ z.IsDiag).card =
      m.choose 2 := by
    rw [← Fintype.card_subtype, Sym2.card_subtype_not_diag, Fintype.card_fin]
  rw [← ht]
  refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
  · intro p hp
    simp only [Finset.mem_coe, mem_invSet] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mk_isDiag_iff]
    exact ne_of_lt hp.1
  · intro p hp q hq hpq
    simp only [Finset.mem_coe, mem_invSet] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exact absurd (h1 ▸ h2 ▸ hq.1) (not_lt.2 hp.1.le)

theorem length_le_choose (m : ℕ) (w : Perm (Fin m)) : length m w ≤ m.choose 2 :=
  (length_eq_invCount w).trans_le (invCount_le_choose m w)

variable {k : Type*} [CommRing k] {m : ℕ}

/-! ### Words with a repeated letter, and non-reduced words -/

theorem ddw_eq_zero_of_hasRepeat {ρ : List ℕ} (h : HasRepeat ρ) :
    ddw (k := k) (m := m) ρ = 0 := by
  obtain ⟨α, β, a, rfl⟩ := h
  simp only [ddw_append, ddw_cons, ddw_nil, mul_one, dd_mul_self, mul_zero, zero_mul]

/-- `∂_ρ = 0` for a valid word `ρ` which is not reduced (KL I §2.2, Example 3:
`∂_{a_1} ⋯ ∂_{a_r} = 0` unless `s_{a_1} ⋯ s_{a_r}` is a reduced expression). -/
theorem ddw_eq_zero_of_not_isReduced {ρ : List ℕ} (hv : ValidWord m ρ)
    (hr : ¬ IsReduced m ρ) : ddw (k := k) (m := m) ρ = 0 := by
  obtain ⟨σ, hσ, hrep⟩ := exists_braidEquiv_hasRepeat_of_not_isReduced hv hr
  rw [ddw_eq_of_braidEquiv hσ, ddw_eq_zero_of_hasRepeat hrep]

/-- `∂_a ∂_{w_0} = 0` for every `a`. -/
theorem dd_mul_ddw_w0Word (j : ℕ) :
    dd k m j * ddw (k := k) (m := m) (w0Word m) = 0 := by
  by_cases hj : j + 1 < m
  · rw [← ddw_cons]
    apply ddw_eq_zero_of_not_isReduced
    · intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact hj
      · exact validWord_w0Word le_rfl l hl
    · intro hr
      have h1 := hr.2
      rw [List.length_cons, length_w0Word] at h1
      have := length_le_choose m (wordProd m (j :: w0Word m))
      omega
  · rw [dd_eq_zero (by omega), zero_mul]

/-! ### Invariant polynomials -/

/-- Products of powers of variables with swap-invariant exponents are swap-invariant. -/
theorem rename_swap_prod_pow (d : Fin m → ℕ) {a b : Fin m}
    (hd : ∀ c, d (swap a b c) = d c) :
    rename (swap a b) (∏ c, X c ^ d c : MvPolynomial (Fin m) k) = ∏ c, X c ^ d c := by
  rw [map_prod]
  simp only [map_pow, rename_X]
  exact Fintype.prod_equiv (swap a b) _ _ fun c => by rw [hd c]

/-- `∂_ρ (g f) = g ∂_ρ f` if `g` is invariant under the transpositions of the letters of
`ρ`. -/
theorem ddw_mul_of_forall {ρ : List ℕ} {g : MvPolynomial (Fin m) k}
    (hg : ∀ j ∈ ρ, ∀ h : j + 1 < m,
      rename (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩) g = g)
    (f : MvPolynomial (Fin m) k) : ddw ρ (g * f) = g * ddw ρ f := by
  induction ρ with
  | nil => rfl
  | cons j ρ ih =>
    rw [ddw_cons, Module.End.mul_apply, Module.End.mul_apply,
      ih fun l hl => hg l (List.mem_cons_of_mem _ hl)]
    by_cases h : j + 1 < m
    · rw [dd_of_lt h]
      exact ddiff_mul_of_rename_eq (by simp [Fin.ext_iff]) (hg j List.mem_cons_self h) _
    · rw [dd_eq_zero (by omega)]; simp

/-- A polynomial killed by `∂_j` is `s_j`-invariant. -/
theorem rename_swap_eq_of_dd_eq_zero {j : ℕ} (h : j + 1 < m) {g : MvPolynomial (Fin m) k}
    (hg : dd k m j g = 0) : rename (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩) g = g := by
  rw [dd_of_lt h] at hg
  have := ddiff_spec (k := k) (show (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ by simp [Fin.ext_iff]) g
  rw [hg, mul_zero] at this
  exact (sub_eq_zero.1 this.symm).symm

/-- The image of `∂_{w_0}` consists of symmetric polynomials. -/
theorem rename_swap_ddw_w0Word {j : ℕ} (h : j + 1 < m) (f : MvPolynomial (Fin m) k) :
    rename (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩) (ddw (w0Word m) f) = ddw (w0Word m) f := by
  apply rename_swap_eq_of_dd_eq_zero h
  rw [← Module.End.mul_apply, dd_mul_ddw_w0Word]; rfl

/-! ### `x^δ` and `∂_{w_0}(x^δ) = 1` -/

/-- `x^δ = ∏_{a < n} x_a^{n-1-a}` in `k[x_0, …, x_{m-1}]` (the paper's
`x_1^{n-1} x_2^{n-2} ⋯ x_{n-1}`). -/
noncomputable def xDelta (n : ℕ) : MvPolynomial (Fin m) k := ∏ a : Fin m, X a ^ (n - 1 - a)

/-- `x_0 x_1 ⋯ x_{n-1}`. -/
noncomputable def xPre (n : ℕ) : MvPolynomial (Fin m) k :=
  ∏ a : Fin m, X a ^ (if (a : ℕ) < n then 1 else 0)

theorem xDelta_zero : xDelta (k := k) (m := m) 0 = 1 := by
  simp [xDelta]

theorem xDelta_succ (n : ℕ) :
    xDelta (k := k) (m := m) (n + 1) = xPre n * xDelta n := by
  rw [xDelta, xPre, xDelta, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← pow_add]
  congr 1
  split_ifs <;> omega

theorem xPre_zero : xPre (k := k) (m := m) 0 = 1 := by
  simp [xPre]

theorem xPre_succ {n : ℕ} (h : n < m) :
    xPre (k := k) (m := m) (n + 1) = xPre n * X ⟨n, h⟩ := by
  rw [xPre, xPre, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (⟨n, h⟩ : Fin m)),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ (⟨n, h⟩ : Fin m)), if_pos (by simp),
    if_neg (by simp), pow_one, pow_zero, one_mul, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun a ha => ?_
  have : (a : ℕ) ≠ n := fun e => (Finset.mem_erase.1 ha).1 (Fin.ext e)
  congr 1
  split_ifs <;> omega

theorem rename_swap_xPre {n j : ℕ} (h : j + 1 < m) (hj : j + 1 < n ∨ n ≤ j) :
    rename (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩) (xPre (k := k) n) = xPre n := by
  apply rename_swap_prod_pow
  intro c
  rcases eq_or_ne c ⟨j, by omega⟩ with rfl | h1
  · rw [swap_apply_left]; simp only; split_ifs <;> omega
  rcases eq_or_ne c ⟨j + 1, h⟩ with rfl | h2
  · rw [swap_apply_right]; simp only; split_ifs <;> omega
  rw [swap_apply_of_ne_of_ne h1 h2]

theorem ddw_range_xPre {n : ℕ} (h : n < m) :
    ddw (k := k) (m := m) (List.range n) (xPre n) = 1 := by
  induction n with
  | zero => simp [xPre_zero]
  | succ n ih =>
    have hne : (⟨n, by omega⟩ : Fin m) ≠ ⟨n + 1, h⟩ := by simp [Fin.ext_iff]
    rw [List.range_succ, ddw_append, ddw_cons, ddw_nil, mul_one, Module.End.mul_apply,
      xPre_succ (by omega), dd_of_lt h,
      ddiff_mul_of_rename_eq hne (rename_swap_xPre h (Or.inr le_rfl)), ddiff_X_left hne,
      mul_one, ih (by omega)]

/-- `∂_{w_0}(x^δ) = 1`, computed for the first `n` variables: `∂_{w0Word n}(x^δ_n) = 1`. -/
theorem ddw_w0Word_xDelta_of_le {n : ℕ} (h : n ≤ m) :
    ddw (k := k) (m := m) (w0Word n) (xDelta n) = 1 := by
  induction n with
  | zero => simp [w0Word, xDelta_zero]
  | succ n ih =>
    rw [w0Word_succ, ddw_append, Module.End.mul_apply, xDelta_succ,
      ddw_mul_of_forall (fun j hj h' => rename_swap_xPre h' (Or.inl (lt_of_mem_w0Word hj))),
      ih (by omega), mul_one, ddw_range_xPre (by omega)]

/-- **KL I §2.2, Example 3**: `∂_{w_0}(x_1^{m-1} ⋯ x_{m-1}) = 1`. -/
theorem ddw_w0Word_xDelta : ddw (k := k) (m := m) (w0Word m) (xDelta m) = 1 :=
  ddw_w0Word_xDelta_of_le le_rfl

/-! ### The key identity and the idempotents -/

/-- The key identity `∂_{w_0} p ∂_{w_0} = ∂_{w_0}(p) ∂_{w_0}` (the image of `∂_{w_0}` is
symmetric and `∂_{w_0}` is linear over symmetric polynomials). -/
theorem ddw_w0Word_mul_mulPoly_mul_ddw_w0Word (p : MvPolynomial (Fin m) k) :
    ddw (w0Word m) * mulPoly k m p * ddw (w0Word m) =
      mulPoly k m (ddw (w0Word m) p) * ddw (w0Word m) := by
  refine LinearMap.ext fun f => ?_
  simp only [Module.End.mul_apply, mulPoly_apply]
  rw [mul_comm p, ddw_mul_of_forall (fun j _ h => rename_swap_ddw_w0Word h f), mul_comm]

/-- `∂_{w_0} x^δ ∂_{w_0} = ∂_{w_0}`. -/
theorem ddw_w0Word_mul_xDelta_mul_ddw_w0Word :
    ddw (w0Word m) * mulPoly k m (xDelta m) * ddw (w0Word m) = ddw (k := k) (w0Word m) := by
  rw [ddw_w0Word_mul_mulPoly_mul_ddw_w0Word, ddw_w0Word_xDelta, map_one, one_mul]

variable (k m) in
/-- The idempotent `e_m = x^δ ∂_{w_0}` of `NH_m` (KL I §2.2, Example 3). -/
noncomputable def idemNH : Module.End k (MvPolynomial (Fin m) k) :=
  mulPoly k m (xDelta m) * ddw (w0Word m)

variable (k m) in
/-- The idempotent `ψ(e_m) = ∂_{w_0} x^δ` of `NH_m` (KL I §2.2, Example 3). -/
noncomputable def idemNH' : Module.End k (MvPolynomial (Fin m) k) :=
  ddw (w0Word m) * mulPoly k m (xDelta m)

theorem idemNH_mem : idemNH k m ∈ nilHecke k m := mul_mem (mulPoly_mem _) (ddw_mem _)

theorem idemNH'_mem : idemNH' k m ∈ nilHecke k m := mul_mem (ddw_mem _) (mulPoly_mem _)

/-- **KL I §2.2, Example 3**: `e_m = x_1^{m-1} ⋯ x_{m-1} ∂_{w_0}` is an idempotent. -/
theorem isIdempotentElem_idemNH : IsIdempotentElem (idemNH k m) := by
  unfold IsIdempotentElem idemNH
  rw [mul_assoc, ← mul_assoc (ddw _), ddw_w0Word_mul_xDelta_mul_ddw_w0Word]

/-- **KL I §2.2, Example 3**: `ψ(e_m) = ∂_{w_0} x_1^{m-1} ⋯ x_{m-1}` is an idempotent. -/
theorem isIdempotentElem_idemNH' : IsIdempotentElem (idemNH' k m) := by
  unfold IsIdempotentElem idemNH'
  rw [← mul_assoc, ddw_w0Word_mul_xDelta_mul_ddw_w0Word]

/-! ### `w0Word m` is a reduced word of the longest element -/

/-- `w0Word m` is a reduced word. (Were it not, `∂_{w0Word m}` would vanish, contradicting
`∂_{w0Word m}(x^δ) = 1` over `ℤ`.) -/
theorem isReduced_w0Word (m : ℕ) : IsReduced m (w0Word m) := by
  by_contra hr
  have h0 := ddw_eq_zero_of_not_isReduced (k := ℤ) (validWord_w0Word le_rfl) hr
  have h1 := ddw_w0Word_xDelta (k := ℤ) (m := m)
  rw [h0, LinearMap.zero_apply] at h1
  exact zero_ne_one h1

/-- The longest element `w_0 ∈ S_m`. -/
def longest (m : ℕ) : Perm (Fin m) := wordProd m (w0Word m)

theorem length_longest (m : ℕ) : length m (longest m) = m.choose 2 :=
  (isReduced_w0Word m).2.symm.trans (length_w0Word m)

/-- `w_0` is the longest permutation. -/
theorem length_le_length_longest (w : Perm (Fin m)) : length m w ≤ length m (longest m) := by
  rw [length_longest]; exact length_le_choose m w

/-- `∂_{w0Word m} = ∂_{w_0}` (independent of the reduced word, `ddw_eq_ddPerm`). -/
theorem ddw_w0Word_eq_ddPerm : ddw (k := k) (m := m) (w0Word m) = ddPerm k m (longest m) :=
  ddw_eq_ddPerm (isReduced_w0Word m)

end Categorification.NilHecke
