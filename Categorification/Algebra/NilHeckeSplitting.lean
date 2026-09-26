/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.NilHeckeIdempotent
import Categorification.Algebra.SymmetricFree
import Categorification.TypeA.Parabolic

/-!
# Splitting `e_n ⊗ 1` in the nilHecke ring `NH_{n+1}`

M. Khovanov, A. Lauda, *A diagrammatic approach to categorification of quantum groups I*,
arXiv:0803.4121v2, §2.2, Example 3 (TeX lines ~700–712: "The regular representation of
`NH_m` decomposes as the sum of `m!` copies of the polynomial one … `NH_m ≅ P_m^{[m]!}`") and
§2.5 (TeX line ~1604: `gdim (1_î M) = q^{-⟨i⟩} i! gdim (1_i M)`, "which follows from the
structure of the nilHecke algebra").

We prove the inductive step behind these statements. In `NH_{n+1}` (acting on
`k[x_0, …, x_n]`, zero-indexed, `y = x_n` the last variable) let

* `E = e_{n+1} = x^δ ∂_{w_0}` (the idempotent `idemNH k (n+1)`), and
* `E' = e_n ⊗ 1 = x^{δ'} ∂_{w_0'}`, the idempotent `e_n` on the first `n` strands
  (`x^{δ'} = xDelta n`, `∂_{w_0'} = ddw (w0Word n)`).

Then `E' = ∑_{j=0}^{n} a_j b_j` with `b_i a_j = δ_{ij} E`, where

  `a_j = x^{δ'} y^j ∂_{w_0}`,   `b_j = x^δ ∂_{w_0} Q_j x^{δ'} ∂_{w_0'}`

and `Q_0, …, Q_n` are the polynomials dual to `1, y, …, y^n` for the pairing
`(f, g) ↦ ∂_{w_0}(x^{δ'} f g)` on polynomials symmetric in `x_0, …, x_{n-1}`
(`nhDual`). In particular `E'` is the sum of the `n + 1` orthogonal idempotents `a_j b_j`, each
equivalent to `E`. Since `Q_j` is homogeneous of degree `n - j` (`isHomogeneous_nhDual`), in the
graded nilHecke ring (`deg x = 2`, `deg ∂ = -2`) `a_j` has degree `2(j - n)` and `b_j` degree
`2(n - j)`; so `E' M ≅ ⊕_{j=0}^n (E M){2(j - n)}` and
`gdim (E' M) = q^{-n} [n+1] gdim (E M)`. Iterating from `n = 0` gives
`gdim M = q^{-m(m-1)/2} [m]! gdim (e_m M)`, the formula of KL I §2.5.

## Main results

* `ddiff_isHomogeneous`, `ddw_isHomogeneous` : divided differences lower the degree by one.
* `dd_mul_ddw_w0Word_of_lt` : `∂_a ∂_{w_0'} = 0` for `a + 1 < n` in `NH_{n+1}`.
* `nhPair_pow_of_lt`, `exists_nhPair_pow_eq_C` : `∂_{w_0}(x^{δ'} y^j) = 0` for `j < n`, and it is a
  unit constant for `j = n`.
* `exists_sum_mul_pow_last_of_mem` : polynomials symmetric in `x_0, …, x_{n-1}` are combinations
  `∑_{j ≤ n} s_j y^j` with symmetric `s_j` (from `Categorification.Algebra.SymmetricFree`).
* `nhDual`, `nhPair_nhDual_mul_pow`, `sum_pow_mul_nhPair` : the dual polynomials,
  `∂_{w_0}(x^{δ'} Q_i y^j) = δ_{ij}`, and the reconstruction `g = ∑_j y^j ∂_{w_0}(x^{δ'} Q_j g)`.
* `nhB_mul_nhA`, `sum_nhA_mul_nhB` : **the splitting** `b_i a_j = δ_{ij} E` and
  `∑_j a_j b_j = E'` in `End_k(k[x_0, …, x_n])`.
-/

namespace Categorification.NilHecke

open MvPolynomial Equiv TypeA

variable {σ : Type*} {k : Type*} [CommRing k]

/-! ### Divided differences are homogeneous of degree `-1` -/

section Homogeneous

variable [DecidableEq σ] {a b : σ}

private theorem degree_erase_erase (hab : a ≠ b) (s : σ →₀ ℕ) :
    ((s.erase a).erase b).degree + s a + s b = s.degree := by
  conv_rhs => rw [← erase_add_single hab s]
  rw [Finsupp.degree_add, Finsupp.degree_add, Finsupp.degree_single, Finsupp.degree_single]

omit [DecidableEq σ] in
private theorem isHomogeneous_ddiffMonomial_aux (r : MvPolynomial σ k) {e : ℕ}
    (hr : r.IsHomogeneous e) (p q : ℕ) :
    (r * ∑ t ∈ Finset.range (p - q), X a ^ (q + t) * X b ^ (p - 1 - t)).IsHomogeneous
      (e + (p + q - 1)) := by
  refine hr.mul (IsHomogeneous.sum _ _ _ fun t ht => ?_)
  rw [Finset.mem_range] at ht
  have := (isHomogeneous_X_pow (R := k) a (q + t)).mul (isHomogeneous_X_pow (R := k) b (p - 1 - t))
  convert this using 1
  omega

theorem isHomogeneous_ddiffMonomial (hab : a ≠ b) (s : σ →₀ ℕ) {d : ℕ}
    (hs : s.degree = d + 1) : (ddiffMonomial (k := k) a b s).IsHomogeneous d := by
  have hdeg := degree_erase_erase hab s
  have hr : (monomial ((s.erase a).erase b) (1 : k)).IsHomogeneous
      ((s.erase a).erase b).degree := isHomogeneous_monomial _ rfl
  unfold ddiffMonomial
  simp only
  split_ifs with h
  · by_cases hp : s b < s a
    · have := isHomogeneous_ddiffMonomial_aux (a := a) (b := b) _ hr (s a) (s b)
      convert this using 1
      omega
    · rw [show s a - s b = 0 by omega, Finset.range_zero, Finset.sum_empty, mul_zero]
      exact isHomogeneous_zero _ _ _
  · have := isHomogeneous_ddiffMonomial_aux (a := a) (b := b) _ hr (s b) (s a)
    convert this.neg using 1
    omega

/-- Divided differences lower the degree of homogeneous polynomials by one. -/
theorem ddiff_isHomogeneous (hab : a ≠ b) {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous (d + 1)) : (ddiff a b f).IsHomogeneous d := by
  rw [f.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun s hs => ?_
  have hc : (monomial s (coeff s f) : MvPolynomial σ k) = coeff s f • monomial s 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, map_smul, ddiff_monomial_one, smul_eq_C_mul]
  have := (isHomogeneous_C σ (coeff s f)).mul
    (isHomogeneous_ddiffMonomial (k := k) (d := d) hab s (by
      rw [Finsupp.degree_eq_weight_one]; exact hf (mem_support_iff.1 hs)))
  rwa [zero_add] at this

/-- Divided differences kill constants. -/
theorem ddiff_eq_zero_of_isHomogeneous_zero (hab : a ≠ b) {f : MvPolynomial σ k}
    (hf : f.IsHomogeneous 0) : ddiff a b f = 0 := by
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hf
  rw [hf]
  exact ddiff_eq_zero_of_rename_eq hab (by rw [rename_C])

end Homogeneous

section ddHomogeneous

variable {m : ℕ}

theorem dd_isHomogeneous (j : ℕ) {f : MvPolynomial (Fin m) k} {d : ℕ}
    (hf : f.IsHomogeneous (d + 1)) : (dd k m j f).IsHomogeneous d := by
  by_cases h : j + 1 < m
  · rw [dd_of_lt h]; exact ddiff_isHomogeneous (by simp [Fin.ext_iff]) hf
  · rw [dd_eq_zero (by omega)]; exact isHomogeneous_zero _ _ _

theorem dd_eq_zero_of_isHomogeneous_zero (j : ℕ) {f : MvPolynomial (Fin m) k}
    (hf : f.IsHomogeneous 0) : dd k m j f = 0 := by
  by_cases h : j + 1 < m
  · rw [dd_of_lt h]; exact ddiff_eq_zero_of_isHomogeneous_zero (by simp [Fin.ext_iff]) hf
  · rw [dd_eq_zero (by omega)]; rfl

/-- `∂_ρ` lowers the degree of homogeneous polynomials by the length of `ρ`. -/
theorem ddw_isHomogeneous (ρ : List ℕ) {f : MvPolynomial (Fin m) k} {d : ℕ}
    (hf : f.IsHomogeneous (d + ρ.length)) : (ddw (k := k) (m := m) ρ f).IsHomogeneous d := by
  induction ρ generalizing d with
  | nil => simpa using hf
  | cons j ρ ih =>
    rw [ddw_cons, Module.End.mul_apply]
    exact dd_isHomogeneous j (ih (by rw [List.length_cons] at hf; convert hf using 1; omega))

/-- `∂_ρ` kills homogeneous polynomials of degree less than the length of `ρ`. -/
theorem ddw_eq_zero_of_isHomogeneous (ρ : List ℕ) {f : MvPolynomial (Fin m) k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : d < ρ.length) : ddw (k := k) (m := m) ρ f = 0 := by
  induction ρ with
  | nil => simp at hd
  | cons j ρ ih =>
    rw [ddw_cons, Module.End.mul_apply]
    by_cases h : d < ρ.length
    · rw [ih h, map_zero]
    · rw [List.length_cons] at hd
      exact dd_eq_zero_of_isHomogeneous_zero j (ddw_isHomogeneous ρ (d := 0)
        (by convert hf using 1; omega))

end ddHomogeneous

/-! ### Polynomials invariant under the first adjacent transpositions -/

section AdjInv

variable (k) {m : ℕ}

/-- The polynomials in `k[x_0, …, x_{m-1}]` invariant under the adjacent transpositions
`s_j = (j, j + 1)` with `j + 1 < r` (i.e. symmetric in the first `r` variables). -/
def adjInv (m r : ℕ) : Subalgebra k (MvPolynomial (Fin m) k) where
  carrier := {g | ∀ j (h : j + 1 < m), j + 1 < r →
    rename (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩) g = g}
  mul_mem' {f g} hf hg j h hr := by rw [map_mul, hf j h hr, hg j h hr]
  add_mem' {f g} hf hg j h hr := by rw [map_add, hf j h hr, hg j h hr]
  algebraMap_mem' c j h hr := by rw [algebraMap_eq, rename_C]

variable {k}

theorem mem_adjInv {r : ℕ} {g : MvPolynomial (Fin m) k} :
    g ∈ adjInv k m r ↔ ∀ j (h : j + 1 < m), j + 1 < r →
      rename (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩) g = g := Iff.rfl

theorem adjInv_mono {r r' : ℕ} (h : r' ≤ r) {g : MvPolynomial (Fin m) k}
    (hg : g ∈ adjInv k m r) : g ∈ adjInv k m r' :=
  fun j hj hr => hg j hj (by omega)

theorem mem_adjInv_of_isSymmetric {r : ℕ} {g : MvPolynomial (Fin m) k} (hg : g.IsSymmetric) :
    g ∈ adjInv k m r := fun _ _ _ => hg _

/-- `∂_{w_0'}` (for `S_r`, `r ≤ m`) is linear over polynomials symmetric in the first `r`
variables. -/
theorem ddw_w0Word_mul_of_mem {r : ℕ} {g : MvPolynomial (Fin m) k} (hg : g ∈ adjInv k m r)
    (f : MvPolynomial (Fin m) k) : ddw (w0Word r) (g * f) = g * ddw (w0Word r) f :=
  ddw_mul_of_forall (fun j hj h => hg j h (lt_of_mem_w0Word hj)) f

/-- The image of `∂_{w_0}` is symmetric. -/
theorem ddw_w0Word_mem_adjInv (r : ℕ) (f : MvPolynomial (Fin m) k) :
    ddw (w0Word m) f ∈ adjInv k m r := fun _ h _ => rename_swap_ddw_w0Word h f

/-- `∂_a ∂_{w_0'} = 0` for `a + 1 < r ≤ m`, where `w_0'` is the longest element of `S_r`. -/
theorem dd_mul_ddw_w0Word_of_lt {r : ℕ} (hr : r ≤ m) {a : ℕ} (ha : a + 1 < r) :
    dd k m a * ddw (k := k) (m := m) (w0Word r) = 0 := by
  rw [← ddw_cons]
  apply ddw_eq_zero_of_not_isReduced
  · intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · omega
    · exact validWord_w0Word hr l hl
  · intro hred
    have hv : ValidWord r (a :: w0Word r) := by
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact ha
      · exact validWord_w0Word le_rfl l hl
    have h1 := hred.2
    rw [wordProd_eq_blockPerm_left (show r + (m - r) = m by omega) hv, length_blockPerm,
      length_one, add_zero, List.length_cons, length_w0Word] at h1
    have := length_le_choose r (wordProd r (a :: w0Word r))
    omega

/-- The image of `∂_{w_0'}` (for `S_r`, `r ≤ m`) is symmetric in the first `r` variables. -/
theorem ddw_w0Word_mem_adjInv_of_le {r : ℕ} (hr : r ≤ m) (f : MvPolynomial (Fin m) k) :
    ddw (w0Word r) f ∈ adjInv k m r := fun j h hj => by
  apply rename_swap_eq_of_dd_eq_zero h
  rw [← Module.End.mul_apply, dd_mul_ddw_w0Word_of_lt hr hj]; rfl

/-- `extendLastPerm` on `castSucc`. -/
theorem extendLastPerm_castSucc {n : ℕ} (σ : Perm (Fin n)) (a : Fin n) :
    extendLastPerm σ (Fin.castSucc a) = Fin.castSucc (σ a) := by
  simp [extendLastPerm, finSuccEquiv'_below (Fin.castSucc_lt_last a),
    finSuccEquiv'_symm_some_below (Fin.castSucc_lt_last (σ a))]

theorem extendLastPerm_last {n : ℕ} (σ : Perm (Fin n)) :
    extendLastPerm σ (Fin.last n) = Fin.last n := by
  simp [extendLastPerm, finSuccEquiv'_at, finSuccEquiv'_symm_none]

theorem extendLastPerm_mul {n : ℕ} (σ τ : Perm (Fin n)) :
    extendLastPerm (σ * τ) = extendLastPerm σ * extendLastPerm τ := by
  ext x
  induction x using Fin.lastCases with
  | last => simp [extendLastPerm_last]
  | cast a => simp [extendLastPerm_castSucc]

theorem extendLastPerm_swap {n : ℕ} (a b : Fin n) :
    extendLastPerm (swap a b) = swap (Fin.castSucc a) (Fin.castSucc b) := by
  ext x
  induction x using Fin.lastCases with
  | last =>
    rw [extendLastPerm_last, swap_apply_of_ne_of_ne (Fin.castSucc_lt_last a).ne'
      (Fin.castSucc_lt_last b).ne']
  | cast c =>
    rw [extendLastPerm_castSucc, ← (Fin.castSucc_injective n).map_swap]

/-- **Tower step** (from `Categorification.Algebra.SymmetricFree`): a polynomial in
`k[x_0, …, x_n]` symmetric in `x_0, …, x_{n-1}` is a combination `∑_{j ≤ n} s_j y^j` of powers
of `y = x_n` with symmetric coefficients. -/
theorem exists_sum_mul_pow_last_of_mem {n : ℕ} {g : MvPolynomial (Fin (n + 1)) k}
    (hg : g ∈ adjInv k (n + 1) n) :
    ∃ s : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k, (∀ j, (s j).IsSymmetric) ∧
      ∑ j, s j * X (Fin.last n) ^ (j : ℕ) = g := by
  refine exists_sum_mul_pow_last fun σ => ?_
  rw [← lastVarEquiv_rename_extendLastPerm]
  congr 1
  let S : Submonoid (Perm (Fin n)) :=
    { carrier := {σ | rename (extendLastPerm σ) g = g}
      mul_mem' := fun {σ τ} hσ hτ => by
        simp only [Set.mem_setOf_eq] at *
        rw [extendLastPerm_mul, Perm.coe_mul, ← rename_rename, hτ, hσ]
      one_mem' := by
        simp only [Set.mem_setOf_eq]
        have : extendLastPerm (1 : Perm (Fin n)) = 1 := by
          ext x
          induction x using Fin.lastCases with
          | last => simp [extendLastPerm_last]
          | cast a => simp [extendLastPerm_castSucc]
        rw [this, Perm.coe_one, rename_id_apply] }
  have hS : σ ∈ S := by
    rcases n with _ | n
    · rw [Subsingleton.elim σ 1]; exact S.one_mem
    · have hle : Submonoid.closure (Set.range fun i : Fin n => swap i.castSucc i.succ) ≤ S := by
        refine Submonoid.closure_le.2 ?_
        rintro _ ⟨i, rfl⟩
        show rename (extendLastPerm (swap i.castSucc i.succ)) g = g
        rw [extendLastPerm_swap]
        have := hg i (by omega) (by omega)
        convert this using 3
      rw [Perm.mclosure_swap_castSucc_succ] at hle
      exact hle (Submonoid.mem_top σ)
  exact hS

end AdjInv

/-! ### The pairing `g ↦ ∂_{w_0}(x^{δ'} g)` and the dual polynomials -/

section Pairing

variable (k) (n : ℕ)

/-- The pairing `g ↦ ∂_{w_0}(x^{δ'} g)` on `k[x_0, …, x_n]`, where `w_0` is the longest element of
`S_{n+1}` and `x^{δ'} = x_0^{n-1} ⋯ x_{n-2}` (`xDelta n`). On polynomials symmetric in
`x_0, …, x_{n-1}` it is the relative divided difference down to symmetric polynomials. -/
noncomputable def nhPair : Module.End k (MvPolynomial (Fin (n + 1)) k) :=
  ddw (w0Word (n + 1)) * mulPoly k (n + 1) (xDelta n)

variable {k n}

theorem nhPair_apply (g : MvPolynomial (Fin (n + 1)) k) :
    nhPair k n g = ddw (w0Word (n + 1)) (xDelta n * g) := rfl

theorem nhPair_mem_adjInv (r : ℕ) (g : MvPolynomial (Fin (n + 1)) k) :
    nhPair k n g ∈ adjInv k (n + 1) r :=
  ddw_w0Word_mem_adjInv r _

/-- The pairing is linear over symmetric polynomials. -/
theorem nhPair_mul_of_mem {s : MvPolynomial (Fin (n + 1)) k} (hs : s ∈ adjInv k (n + 1) (n + 1))
    (g : MvPolynomial (Fin (n + 1)) k) : nhPair k n (s * g) = s * nhPair k n g := by
  rw [nhPair_apply, nhPair_apply, mul_left_comm, ddw_w0Word_mul_of_mem hs]

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  have := Nat.choose_succ_succ' n 1
  simp only [Nat.reduceAdd, Nat.choose_one_right] at this
  omega

theorem isHomogeneous_xDelta : (xDelta (k := k) (m := n + 1) n).IsHomogeneous (n.choose 2) := by
  have : ∑ a : Fin (n + 1), (n - 1 - (a : ℕ)) = n.choose 2 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [show n - 1 - n = 0 by omega, add_zero,
      Fin.sum_univ_eq_sum_range (fun a => n - 1 - a) n, Finset.sum_range_reflect (fun j => j) n,
      Finset.sum_range_id, Nat.choose_two_right]
  rw [← this]
  exact IsHomogeneous.prod _ _ _ fun a _ => isHomogeneous_X_pow _ _

/-- `∂_{w_0}(x^{δ'} y^j) = 0` for `j < n` (degree reasons). -/
theorem nhPair_pow_of_lt {j : ℕ} (hj : j < n) :
    nhPair k n ((X (Fin.last n)) ^ j) = 0 := by
  rw [nhPair_apply]
  refine ddw_eq_zero_of_isHomogeneous _ (isHomogeneous_xDelta.mul (isHomogeneous_X_pow _ j)) ?_
  rw [length_w0Word, choose_two_succ]
  omega

/-- `∂_{w_0}(x^{δ'} y^{n + r})` is homogeneous of degree `r`. -/
theorem nhPair_pow_isHomogeneous (r : ℕ) :
    (nhPair k n ((X (Fin.last n)) ^ (n + r))).IsHomogeneous r := by
  rw [nhPair_apply]
  refine ddw_isHomogeneous _ ?_
  convert isHomogeneous_xDelta.mul (isHomogeneous_X_pow (R := k) (Fin.last n) (n + r)) using 1
  rw [length_w0Word, choose_two_succ]
  omega

/-- `∂_{w_0}(x^{δ'} x_0 ⋯ x_{n-1}) = ∂_{w_0}(x^δ) = 1`. -/
theorem nhPair_xPre : nhPair k n (xPre n) = 1 := by
  rw [nhPair_apply, mul_comm, ← xDelta_succ, ddw_w0Word_xDelta]

theorem xPre_mem_adjInv : (xPre n : MvPolynomial (Fin (n + 1)) k) ∈ adjInv k (n + 1) n :=
  fun _ h hj => rename_swap_xPre h (Or.inl hj)

theorem last_pow_mem_adjInv (j : ℕ) :
    (X (Fin.last n) : MvPolynomial (Fin (n + 1)) k) ^ j ∈ adjInv k (n + 1) n := by
  refine Subalgebra.pow_mem _ (show (X (Fin.last n) : MvPolynomial (Fin (n + 1)) k) ∈
    adjInv k (n + 1) n from fun l h hl => ?_) j
  rw [rename_X, swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff]; omega)]

/-- `∂_{w_0}(x^{δ'} y^n)` is a unit constant. -/
theorem exists_nhPair_pow_eq_C :
    ∃ u : kˣ, nhPair k n ((X (Fin.last n)) ^ n) = C (u : k) := by
  have h0 := nhPair_pow_isHomogeneous (k := k) (n := n) 0
  rw [add_zero, ← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h0
  set u0 := coeff 0 (nhPair k n ((X (Fin.last n)) ^ n))
  obtain ⟨s, hs, hsum⟩ := exists_sum_mul_pow_last_of_mem (xPre_mem_adjInv (k := k) (n := n))
  have h1 := nhPair_xPre (k := k) (n := n)
  rw [← hsum, map_sum, Fin.sum_univ_castSucc] at h1
  simp only [Fin.coe_castSucc, Fin.val_last] at h1
  rw [Finset.sum_eq_zero (fun j _ => by
    rw [nhPair_mul_of_mem (mem_adjInv_of_isSymmetric (hs _)), nhPair_pow_of_lt j.2, mul_zero]),
    zero_add, nhPair_mul_of_mem (mem_adjInv_of_isSymmetric (hs _)), h0] at h1
  have h2 := congrArg (coeff 0) h1
  rw [mul_comm, coeff_C_mul, coeff_one, if_pos rfl] at h2
  refine ⟨(isUnit_of_mul_eq_one _ _ h2).unit, ?_⟩
  rw [IsUnit.unit_spec]
  exact h0

variable (k n)

/-- The unit `u` with `∂_{w_0}(x^{δ'} y^n) = u` (in fact `u = (-1)^n`). -/
noncomputable def nhUnit : kˣ := (exists_nhPair_pow_eq_C (k := k) (n := n)).choose

theorem nhPair_pow_self : nhPair k n ((X (Fin.last n)) ^ n) = C (nhUnit k n : k) :=
  (exists_nhPair_pow_eq_C (k := k) (n := n)).choose_spec

/-- The generating series `∑_r ∂_{w_0}(x^{δ'} y^{n + r}) t^r`. -/
noncomputable def nhSer : PowerSeries (MvPolynomial (Fin (n + 1)) k) :=
  PowerSeries.mk fun r => nhPair k n ((X (Fin.last n)) ^ (n + r))

/-- Its inverse. -/
noncomputable def nhSerInv : PowerSeries (MvPolynomial (Fin (n + 1)) k) :=
  PowerSeries.invOfUnit (nhSer k n)
    (Units.map (C : k →+* MvPolynomial (Fin (n + 1)) k).toMonoidHom (nhUnit k n))

/-- **The dual polynomials** `Q_i = ∑_{s ≤ n - i} d_s y^{n - i - s}`, where
`∑_s d_s t^s = (∑_r ∂_{w_0}(x^{δ'} y^{n+r}) t^r)⁻¹`; see `nhPair_nhDual_mul_pow`. -/
noncomputable def nhDual (i : ℕ) : MvPolynomial (Fin (n + 1)) k :=
  ∑ s ∈ Finset.range (n - i + 1),
    PowerSeries.coeff _ s (nhSerInv k n) * (X (Fin.last n)) ^ (n - i - s)

variable {k n}

theorem nhSerInv_mul_nhSer : nhSerInv k n * nhSer k n = 1 :=
  PowerSeries.invOfUnit_mul _ _ (by
    rw [nhSer, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, add_zero,
      nhPair_pow_self]; rfl)

theorem coeff_nhSerInv (s : ℕ) :
    PowerSeries.coeff _ s (nhSerInv k n) = if s = 0 then C (((nhUnit k n)⁻¹ : kˣ) : k) else
      -C (((nhUnit k n)⁻¹ : kˣ) : k) * ∑ x ∈ Finset.antidiagonal s, if x.2 < s then
        PowerSeries.coeff _ x.1 (nhSer k n) * PowerSeries.coeff _ x.2 (nhSerInv k n) else 0 := by
  rw [nhSerInv, PowerSeries.coeff_invOfUnit, Units.coe_map_inv]
  rfl

theorem coeff_nhSerInv_mem (s : ℕ) :
    PowerSeries.coeff _ s (nhSerInv k n) ∈ adjInv k (n + 1) (n + 1) ∧
      (PowerSeries.coeff _ s (nhSerInv k n)).IsHomogeneous s := by
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rw [coeff_nhSerInv]
    split_ifs with hs
    · subst hs; exact ⟨Subalgebra.algebraMap_mem _ _, isHomogeneous_C _ _⟩
    · refine ⟨Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (Subalgebra.algebraMap_mem _ _))
        (Subalgebra.sum_mem _ fun x hx => ?_), ?_⟩
      · split_ifs with h2
        · refine Subalgebra.mul_mem _ ?_ ((ih x.2 h2).1)
          rw [nhSer, PowerSeries.coeff_mk]; exact nhPair_mem_adjInv _ _
        · exact Subalgebra.zero_mem _
      · have := ((isHomogeneous_C (σ := Fin (n + 1)) (-((nhUnit k n)⁻¹ : kˣ) : k))).mul
          (IsHomogeneous.sum (Finset.antidiagonal s) (fun x => if x.2 < s then
            PowerSeries.coeff _ x.1 (nhSer k n) * PowerSeries.coeff _ x.2 (nhSerInv k n) else 0)
            s fun x hx => by
            dsimp only
            split_ifs with h2
            · have h3 := (nhPair_pow_isHomogeneous (k := k) (n := n) x.1).mul (ih x.2 h2).2
              rw [Finset.mem_antidiagonal] at hx
              rw [hx] at h3
              rw [nhSer, PowerSeries.coeff_mk]; exact h3
            · exact isHomogeneous_zero _ _ _)
        rw [zero_add, map_neg] at this
        exact this

theorem coeff_nhSerInv_mem_adjInv (s : ℕ) :
    PowerSeries.coeff _ s (nhSerInv k n) ∈ adjInv k (n + 1) (n + 1) :=
  (coeff_nhSerInv_mem s).1

theorem isHomogeneous_nhDual {i : ℕ} (hi : i ≤ n) : (nhDual k n i).IsHomogeneous (n - i) := by
  refine IsHomogeneous.sum _ _ _ fun s hs => ?_
  rw [Finset.mem_range] at hs
  have := (coeff_nhSerInv_mem (k := k) (n := n) s).2.mul (isHomogeneous_X_pow (Fin.last n) (n - i - s))
  convert this using 1
  omega

theorem nhDual_mem_adjInv (i : ℕ) : nhDual k n i ∈ adjInv k (n + 1) n :=
  Subalgebra.sum_mem _ fun s _ => Subalgebra.mul_mem _
    (adjInv_mono (Nat.le_succ n) (coeff_nhSerInv_mem_adjInv s)) (last_pow_mem_adjInv _)

/-- `∂_{w_0}(x^{δ'} y^{n + r})` in terms of the series. -/
theorem nhPair_pow_eq_coeff (r : ℕ) :
    nhPair k n ((X (Fin.last n)) ^ (n + r)) = PowerSeries.coeff _ r (nhSer k n) := by
  rw [nhSer, PowerSeries.coeff_mk]

/-- **Duality**: `∂_{w_0}(x^{δ'} Q_i y^j) = δ_{ij}` for `i, j ≤ n`. -/
theorem nhPair_nhDual_mul_pow {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    nhPair k n (nhDual k n i * (X (Fin.last n)) ^ j) = if i = j then 1 else 0 := by
  rw [nhDual, Finset.sum_mul, map_sum]
  have hterm : ∀ s ∈ Finset.range (n - i + 1),
      nhPair k n (PowerSeries.coeff _ s (nhSerInv k n) * (X (Fin.last n)) ^ (n - i - s) *
        (X (Fin.last n)) ^ j) =
      if i + s ≤ j then PowerSeries.coeff _ s (nhSerInv k n) *
        PowerSeries.coeff _ (j - i - s) (nhSer k n) else 0 := by
    intro s hs
    rw [Finset.mem_range] at hs
    rw [mul_assoc, nhPair_mul_of_mem (coeff_nhSerInv_mem_adjInv s), ← pow_add]
    split_ifs with h
    · rw [show n - i - s + j = n + (j - i - s) by omega, nhPair_pow_eq_coeff]
    · rw [nhPair_pow_of_lt (by omega), mul_zero]
  rw [Finset.sum_congr rfl hterm]
  by_cases hij : i ≤ j
  · have h1 : ∑ s ∈ Finset.range (n - i + 1), (if i + s ≤ j then
        PowerSeries.coeff _ s (nhSerInv k n) * PowerSeries.coeff _ (j - i - s) (nhSer k n)
        else 0) = ∑ s ∈ Finset.range (j - i + 1),
        PowerSeries.coeff _ s (nhSerInv k n) * PowerSeries.coeff _ (j - i - s) (nhSer k n) := by
      rw [← Finset.sum_range_add_sum_Ico _ (show j - i + 1 ≤ n - i + 1 by omega)]
      rw [Finset.sum_eq_zero (s := Finset.Ico (j - i + 1) (n - i + 1)) (fun s hs => by
        rw [Finset.mem_Ico] at hs; exact if_neg (by omega)), add_zero]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [Finset.mem_range] at hs
      exact if_pos (by omega)
    rw [h1, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun s t =>
      PowerSeries.coeff _ s (nhSerInv k n) * PowerSeries.coeff _ t (nhSer k n)),
      ← PowerSeries.coeff_mul, nhSerInv_mul_nhSer, PowerSeries.coeff_one]
    by_cases h : i = j
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · rw [if_neg (by omega)]
    exact Finset.sum_eq_zero fun s _ => if_neg (by omega)

/-- **Reconstruction**: `g = ∑_{j ≤ n} y^j ∂_{w_0}(x^{δ'} Q_j g)` for `g` symmetric in
`x_0, …, x_{n-1}`. -/
theorem sum_pow_mul_nhPair {g : MvPolynomial (Fin (n + 1)) k} (hg : g ∈ adjInv k (n + 1) n) :
    ∑ j : Fin (n + 1), (X (Fin.last n)) ^ (j : ℕ) * nhPair k n (nhDual k n j * g) = g := by
  obtain ⟨s, hs, hsum⟩ := exists_sum_mul_pow_last_of_mem hg
  have hc : ∀ j : Fin (n + 1), nhPair k n (nhDual k n j * g) = s j := by
    intro j
    rw [← hsum, Finset.mul_sum, map_sum]
    rw [Finset.sum_eq_single j (fun l _ hlj => by
      rw [mul_left_comm, nhPair_mul_of_mem (mem_adjInv_of_isSymmetric (hs l)),
        nhPair_nhDual_mul_pow (by omega) (by omega), if_neg (fun h => hlj (Fin.ext h.symm)),
        mul_zero]) (fun h => absurd (Finset.mem_univ j) h)]
    rw [mul_left_comm, nhPair_mul_of_mem (mem_adjInv_of_isSymmetric (hs j)),
      nhPair_nhDual_mul_pow (by omega) (by omega), if_pos rfl, mul_one]
  simp_rw [hc]
  rw [← hsum]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end Pairing

/-! ### The splitting of `e_n ⊗ 1` in `NH_{n+1}` -/

section Splitting

variable (k) (n : ℕ)

/-- The idempotent `E' = e_n ⊗ 1 = x^{δ'} ∂_{w_0'}` of `NH_{n+1}` (`e_n` on the first `n`
strands). -/
noncomputable def nhE' : Module.End k (MvPolynomial (Fin (n + 1)) k) :=
  mulPoly k (n + 1) (xDelta n) * ddw (w0Word n)

/-- `a_j = x^{δ'} y^j ∂_{w_0}`. -/
noncomputable def nhA (j : ℕ) : Module.End k (MvPolynomial (Fin (n + 1)) k) :=
  mulPoly k (n + 1) (xDelta n * (X (Fin.last n)) ^ j) * ddw (w0Word (n + 1))

/-- `b_j = x^δ ∂_{w_0} Q_j x^{δ'} ∂_{w_0'}`. -/
noncomputable def nhB (j : ℕ) : Module.End k (MvPolynomial (Fin (n + 1)) k) :=
  mulPoly k (n + 1) (xDelta (n + 1)) * ddw (w0Word (n + 1)) *
    mulPoly k (n + 1) (nhDual k n j * xDelta n) * ddw (w0Word n)

variable {k n}

theorem nhE'_mem : nhE' k n ∈ nilHecke k (n + 1) := mul_mem (mulPoly_mem _) (ddw_mem _)

theorem nhA_mem (j : ℕ) : nhA k n j ∈ nilHecke k (n + 1) := mul_mem (mulPoly_mem _) (ddw_mem _)

theorem nhB_mem (j : ℕ) : nhB k n j ∈ nilHecke k (n + 1) :=
  mul_mem (mul_mem (mul_mem (mulPoly_mem _) (ddw_mem _)) (mulPoly_mem _)) (ddw_mem _)

/-- `∂_{w_0'} x^{δ'} y^j ∂_{w_0} = y^j ∂_{w_0}`. -/
theorem ddw_mul_mulPoly_pow_mul_ddw (j : ℕ) :
    ddw (w0Word n) * mulPoly k (n + 1) (xDelta n * (X (Fin.last n)) ^ j) *
      ddw (w0Word (n + 1)) = mulPoly k (n + 1) ((X (Fin.last n)) ^ j) * ddw (w0Word (n + 1)) := by
  refine LinearMap.ext fun f => ?_
  simp only [Module.End.mul_apply, mulPoly_apply]
  rw [mul_assoc, mul_comm, ddw_w0Word_mul_of_mem (Subalgebra.mul_mem _ (last_pow_mem_adjInv j)
    (ddw_w0Word_mem_adjInv _ f)), ddw_w0Word_xDelta_of_le (Nat.le_succ n), mul_one]

/-- **The splitting, part 1**: `b_i a_j = δ_{ij} e_{n+1}` for `i, j ≤ n`. -/
theorem nhB_mul_nhA {i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    nhB k n i * nhA k n j = if i = j then idemNH k (n + 1) else 0 := by
  have h1 : nhB k n i * nhA k n j = mulPoly k (n + 1) (xDelta (n + 1)) *
      (ddw (w0Word (n + 1)) * mulPoly k (n + 1) (nhDual k n i * xDelta n * (X (Fin.last n)) ^ j) *
        ddw (w0Word (n + 1))) := by
    rw [nhB, nhA, map_mul (mulPoly k (n + 1)) (nhDual k n i * xDelta n)]
    have := ddw_mul_mulPoly_pow_mul_ddw (k := k) (n := n) j
    simp only [mul_assoc] at this ⊢
    rw [this]
  rw [h1, ddw_w0Word_mul_mulPoly_mul_ddw_w0Word, show nhDual k n i * xDelta n *
    (X (Fin.last n)) ^ j = xDelta n * (nhDual k n i * (X (Fin.last n)) ^ j) by ring,
    ← nhPair_apply, nhPair_nhDual_mul_pow hi hj]
  split_ifs
  · rw [map_one, one_mul]; rfl
  · rw [map_zero, zero_mul, mul_zero]

/-- **The splitting, part 2**: `∑_{j ≤ n} a_j b_j = e_n ⊗ 1`. -/
theorem sum_nhA_mul_nhB : ∑ j : Fin (n + 1), nhA k n j * nhB k n j = nhE' k n := by
  have h1 : ∀ j : ℕ, nhA k n j * nhB k n j = mulPoly k (n + 1) (xDelta n * (X (Fin.last n)) ^ j) *
      ddw (w0Word (n + 1)) * mulPoly k (n + 1) (nhDual k n j * xDelta n) * ddw (w0Word n) := by
    intro j
    rw [nhA, nhB, show ∀ a b c d e : Module.End k (MvPolynomial (Fin (n + 1)) k),
      a * b * (c * b * d * e) = a * (b * c * b) * d * e from fun _ _ _ _ _ => by
        simp only [mul_assoc], ddw_w0Word_mul_xDelta_mul_ddw_w0Word]
  simp_rw [h1]
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.sum_apply]
  simp only [Module.End.mul_apply, mulPoly_apply]
  have h2 : ∀ j : Fin (n + 1), xDelta n * (X (Fin.last n)) ^ (j : ℕ) *
      ddw (w0Word (n + 1)) (nhDual k n j * xDelta n * ddw (w0Word n) f) =
      xDelta n * ((X (Fin.last n)) ^ (j : ℕ) *
        nhPair k n (nhDual k n j * ddw (k := k) (m := n + 1) (w0Word n) f)) := by
    intro j
    rw [nhPair_apply, mul_assoc, show nhDual k n j * xDelta n * ddw (w0Word n) f =
      xDelta n * (nhDual k n j * ddw (k := k) (m := n + 1) (w0Word n) f) by ring]
  simp_rw [h2]
  rw [← Finset.mul_sum, sum_pow_mul_nhPair (ddw_w0Word_mem_adjInv_of_le (Nat.le_succ n) f)]
  rfl

end Splitting

end Categorification.NilHecke
