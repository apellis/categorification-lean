/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Divided difference operators on multivariate polynomials

For distinct variables `a b : σ`, the divided difference operator
`∂_{ab} f = (f - s_{ab} f) / (X a - X b)`, where `s_{ab}` swaps `X a` and `X b`.
It is defined over any commutative ring by its values on monomials:
if `f = X a ^ p * X b ^ q * r` with `r` free of `X a`, `X b`, then
`∂_{ab} f = r * ∑_{t < p - q} X a ^ (q + t) * X b ^ (p - 1 - t)` when `q ≤ p`, and
`∂_{ab} f = - r * ∑_{t < q - p} X a ^ (p + t) * X b ^ (q - 1 - t)` when `p < q`.

## Main results

For `a ≠ b` and an arbitrary commutative ring `k`:

* `ddiff_spec` : `(X a - X b) * ∂_{ab} f = f - s_{ab} f`;
* `isRegular_X_sub_X` : `X a - X b` is a non-zero-divisor, so `ddiff_spec` characterises
  `∂_{ab}` (`ddiff_eq_of_mul`);
* `ddiff_mul` : the twisted Leibniz rule `∂(fg) = ∂f · g + s f · ∂g`;
* `ddiff_eq_zero_of_rename_eq`, `ddiff_X_left`, `ddiff_ddiff` : `∂` kills symmetric
  polynomials, `∂_{ab} (X a) = 1`, `∂² = 0`;
* `rename_ddiff` : `rename φ (∂_{ab} f) = ∂_{φ a, φ b} (rename φ f)` for injective `φ`;
* `ddiff_ddiff_comm` : divided differences of disjoint pairs commute;
* `ddiff_braid` : the nilHecke braid relation `∂_{ab} ∂_{bc} ∂_{ab} = ∂_{bc} ∂_{ab} ∂_{bc}`.
-/

namespace Categorification

open MvPolynomial Equiv

variable {σ : Type*} {k : Type*} [CommRing k]

/-- The divided difference of the monomial `X^s` with respect to `a, b`. -/
noncomputable def ddiffMonomial (a b : σ) (s : σ →₀ ℕ) : MvPolynomial σ k :=
  let r : MvPolynomial σ k := monomial ((s.erase a).erase b) 1
  if s b ≤ s a then
    r * ∑ t ∈ Finset.range (s a - s b), X a ^ (s b + t) * X b ^ (s a - 1 - t)
  else
    -(r * ∑ t ∈ Finset.range (s b - s a), X a ^ (s a + t) * X b ^ (s b - 1 - t))

/-- The divided difference operator `∂_{ab} f = (f - s_{ab} f) / (X a - X b)`. -/
noncomputable def ddiff (a b : σ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  (basisMonomials σ k).constr k (ddiffMonomial a b)

theorem ddiff_monomial_one (a b : σ) (s : σ →₀ ℕ) :
    ddiff a b (monomial s (1 : k)) = ddiffMonomial a b s := by
  have : (monomial s (1 : k)) = basisMonomials σ k s := rfl
  rw [ddiff, this, Basis.constr_basis]

variable [DecidableEq σ] {a b : σ}

/-! ### The defining identity -/

theorem erase_add_single (hab : a ≠ b) (s : σ →₀ ℕ) :
    (s.erase a).erase b + Finsupp.single a (s a) + Finsupp.single b (s b) = s := by
  ext c
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.erase_apply, Finsupp.single_apply]
  by_cases hca : c = a
  · subst hca; simp [hab, Ne.symm hab]
  · by_cases hcb : c = b
    · subst hcb; simp [hca, Ne.symm hca]
    · simp [hca, hcb, Ne.symm hca, Ne.symm hcb]

theorem monomial_one_eq_erase_mul (hab : a ≠ b) (s : σ →₀ ℕ) :
    monomial s (1 : k) = monomial ((s.erase a).erase b) 1 * X a ^ s a * X b ^ s b := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, monomial_mul, one_mul, one_mul,
    erase_add_single hab]

theorem rename_swap_monomial_erase (s : σ →₀ ℕ) :
    rename (swap a b) (monomial ((s.erase a).erase b) (1 : k)) =
      monomial ((s.erase a).erase b) 1 := by
  have : Finsupp.mapDomain (swap a b) ((s.erase a).erase b) = (s.erase a).erase b := by
    ext c
    rw [← swap_apply_self a b c, Finsupp.mapDomain_apply (swap a b).injective, swap_apply_self]
    simp only [Finsupp.erase_apply]
    by_cases hca : c = a
    · subst hca; by_cases h : c = b <;> simp [h, swap_apply_left]
    · by_cases hcb : c = b
      · subst hcb; simp [swap_apply_right]
      · simp [swap_apply_of_ne_of_ne hca hcb, hca, hcb]
  rw [rename_monomial, this]

omit [DecidableEq σ] in
private theorem sum_shift (x y : MvPolynomial σ k) (p q : ℕ) :
    ∑ t ∈ Finset.range p, x ^ (q + t) * y ^ (q + p - 1 - t) =
      x ^ q * y ^ q * ∑ t ∈ Finset.range p, x ^ t * y ^ (p - 1 - t) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [show q + p - 1 - t = q + (p - 1 - t) by omega, pow_add, pow_add]
  ring

theorem ddiffMonomial_spec (hab : a ≠ b) (s : σ →₀ ℕ) :
    (X a - X b) * ddiffMonomial a b s = monomial s (1 : k) - rename (swap a b) (monomial s 1) := by
  have hs := monomial_one_eq_erase_mul (k := k) hab s
  rw [hs, map_mul, map_mul, rename_swap_monomial_erase, map_pow, map_pow, rename_X, rename_X,
    swap_apply_left, swap_apply_right]
  set r : MvPolynomial σ k := monomial ((s.erase a).erase b) 1
  simp only [ddiffMonomial]
  split_ifs with h
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h
    rw [hn, show s b + n - s b = n by omega]
    have := sum_shift (X a : MvPolynomial σ k) (X b) n (s b)
    rw [this]
    have hg := geom_sum₂_mul (X a : MvPolynomial σ k) (X b) n
    rw [pow_add, pow_add]
    linear_combination (r * X a ^ s b * X b ^ s b) * hg
  · obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (le_of_lt (not_le.1 h))
    rw [hn, show s a + n - s a = n by omega]
    have := sum_shift (X a : MvPolynomial σ k) (X b) n (s a)
    rw [this]
    have hg := geom_sum₂_mul (X a : MvPolynomial σ k) (X b) n
    rw [pow_add, pow_add]
    linear_combination (-(r * X a ^ s a * X b ^ s a)) * hg

/-- The defining identity of the divided difference: `(X a - X b) ∂_{ab} f = f - s_{ab} f`. -/
theorem ddiff_spec (hab : a ≠ b) (f : MvPolynomial σ k) :
    (X a - X b) * ddiff a b f = f - rename (swap a b) f := by
  induction f using MvPolynomial.induction_on' with
  | monomial s c =>
    have hc : (monomial s c : MvPolynomial σ k) = c • monomial s 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hc, map_smul, map_smul, ddiff_monomial_one, mul_smul_comm, ddiffMonomial_spec hab,
      smul_sub]
  | add p q hp hq => rw [map_add, mul_add, hp, hq, map_add]; ring

/-! ### `X a - X b` is a non-zero-divisor -/

/-- The algebra endomorphism `X a ↦ X a + X b` (other variables fixed). -/
private noncomputable def shiftHom (a b : σ) (c : k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun d => if d = a then X a + C c * X b else X d

private theorem shiftHom_comp (hab : a ≠ b) (f : MvPolynomial σ k) :
    shiftHom a b (-1) (shiftHom a b 1 f) = f := by
  have : (shiftHom a b (-1 : k)).comp (shiftHom a b 1) = AlgHom.id k _ := by
    apply MvPolynomial.algHom_ext
    intro d
    simp only [shiftHom, AlgHom.comp_apply, aeval_X, AlgHom.id_apply]
    split_ifs with h
    · subst h
      simp [Ne.symm hab]
    · simp [h]
  exact congrArg (fun φ => φ f) this

theorem isRegular_X_sub_X (hab : a ≠ b) : IsRegular (X a - X b : MvPolynomial σ k) := by
  suffices IsLeftRegular (X a - X b : MvPolynomial σ k) from
    ⟨this, this.right_of_commute <| Commute.all _⟩
  intro p q (hpq : (X a - X b) * p = (X a - X b) * q)
  have h := congrArg (shiftHom a b (1 : k)) hpq
  have hX : shiftHom a b (1 : k) (X a - X b) = X a := by
    simp [shiftHom, Ne.symm hab]
  rw [map_mul, map_mul, hX] at h
  have := (isRegular_X (n := a) (R := k) (σ := σ)).left h
  rw [← shiftHom_comp hab p, ← shiftHom_comp hab q, this]

theorem X_sub_X_mul_left_cancel (hab : a ≠ b) {p q : MvPolynomial σ k}
    (h : (X a - X b) * p = (X a - X b) * q) : p = q :=
  (isRegular_X_sub_X hab).left h

/-- `∂_{ab} f` is the unique `g` with `(X a - X b) g = f - s_{ab} f`. -/
theorem ddiff_eq_of_mul (hab : a ≠ b) {f g : MvPolynomial σ k}
    (h : (X a - X b) * g = f - rename (swap a b) f) : ddiff a b f = g :=
  X_sub_X_mul_left_cancel hab (by rw [ddiff_spec hab, h])

theorem ddiff_eq_iff (hab : a ≠ b) {f g : MvPolynomial σ k} :
    ddiff a b f = g ↔ (X a - X b) * g = f - rename (swap a b) f :=
  ⟨fun h => h ▸ ddiff_spec hab f, ddiff_eq_of_mul hab⟩

/-! ### Basic properties -/

@[simp] theorem rename_swap_rename_swap (a b : σ) (f : MvPolynomial σ k) :
    rename (swap a b) (rename (swap a b) f) = f := by
  rw [rename_rename]
  have : (⇑(swap a b) ∘ ⇑(swap a b)) = id := funext fun c => swap_apply_self a b c
  rw [this, rename_id_apply]

/-- `∂_{ab} f` is symmetric in `a, b`. -/
theorem rename_swap_ddiff (hab : a ≠ b) (f : MvPolynomial σ k) :
    rename (swap a b) (ddiff a b f) = ddiff a b f := by
  apply X_sub_X_mul_left_cancel hab
  have h := congrArg (rename (swap a b)) (ddiff_spec hab f)
  simp only [map_mul, map_sub, rename_X, swap_apply_left, swap_apply_right,
    rename_swap_rename_swap] at h
  rw [ddiff_spec hab]
  linear_combination -h

/-- `∂_{ab}` kills `s_{ab}`-invariant polynomials. -/
theorem ddiff_eq_zero_of_rename_eq (hab : a ≠ b) {f : MvPolynomial σ k}
    (hf : rename (swap a b) f = f) : ddiff a b f = 0 :=
  ddiff_eq_of_mul hab (by rw [hf]; ring)

theorem ddiff_ddiff (hab : a ≠ b) (f : MvPolynomial σ k) : ddiff a b (ddiff a b f) = 0 :=
  ddiff_eq_zero_of_rename_eq hab (rename_swap_ddiff hab f)

@[simp] theorem ddiff_X_left (hab : a ≠ b) : ddiff a b (X a : MvPolynomial σ k) = 1 :=
  ddiff_eq_of_mul hab (by simp)

@[simp] theorem ddiff_X_right (hab : a ≠ b) : ddiff a b (X b : MvPolynomial σ k) = -1 :=
  ddiff_eq_of_mul hab (by simp)

theorem ddiff_X_of_ne (hab : a ≠ b) {c : σ} (hca : c ≠ a) (hcb : c ≠ b) :
    ddiff a b (X c : MvPolynomial σ k) = 0 :=
  ddiff_eq_zero_of_rename_eq hab (by rw [rename_X, swap_apply_of_ne_of_ne hca hcb])

@[simp] theorem ddiff_C (hab : a ≠ b) (c : k) : ddiff a b (C c : MvPolynomial σ k) = 0 :=
  ddiff_eq_zero_of_rename_eq hab (rename_C _ _)

/-- The twisted Leibniz rule `∂(f g) = ∂f · g + s f · ∂g`. -/
theorem ddiff_mul (hab : a ≠ b) (f g : MvPolynomial σ k) :
    ddiff a b (f * g) = ddiff a b f * g + rename (swap a b) f * ddiff a b g := by
  apply ddiff_eq_of_mul hab
  have h1 := ddiff_spec hab f
  have h2 := ddiff_spec hab g
  rw [map_mul]
  linear_combination g * h1 + rename (swap a b) f * h2

/-- Symmetric factors can be pulled out of `∂_{ab}`. -/
theorem ddiff_mul_of_rename_eq (hab : a ≠ b) {g : MvPolynomial σ k}
    (hg : rename (swap a b) g = g) (f : MvPolynomial σ k) :
    ddiff a b (g * f) = g * ddiff a b f := by
  rw [ddiff_mul hab, ddiff_eq_zero_of_rename_eq hab hg, hg, zero_mul, zero_add]

theorem ddiff_rename_swap (hab : a ≠ b) (f : MvPolynomial σ k) :
    ddiff a b (rename (swap a b) f) = -ddiff a b f := by
  apply ddiff_eq_of_mul hab
  rw [rename_swap_rename_swap, mul_neg, ddiff_spec hab]; ring

theorem ddiff_comm (hab : a ≠ b) (f : MvPolynomial σ k) : ddiff b a f = -ddiff a b f := by
  apply ddiff_eq_of_mul (Ne.symm hab)
  rw [swap_comm, ← ddiff_spec hab]; ring

/-! ### Renaming variables -/

/-- Conjugation: `φ ∘ ∂_{ab} = ∂_{φ a, φ b} ∘ φ` for an injective renaming `φ`. -/
theorem rename_ddiff {τ : Type*} [DecidableEq τ] {φ : σ → τ} (hφ : Function.Injective φ)
    (hab : a ≠ b) (f : MvPolynomial σ k) :
    rename φ (ddiff a b f) = ddiff (φ a) (φ b) (rename φ f) := by
  symm
  apply ddiff_eq_of_mul (hφ.ne hab)
  have h := congrArg (rename φ) (ddiff_spec hab f)
  simp only [map_mul, map_sub, rename_X, rename_rename] at h
  rw [h, rename_rename, hφ.swap_comp]

/-- Renamings fixing `a` and `b` commute with `∂_{ab}`. -/
theorem rename_ddiff_of_fix {φ : σ → σ} (hφ : Function.Injective φ) (hab : a ≠ b)
    (ha : φ a = a) (hb : φ b = b) (f : MvPolynomial σ k) :
    rename φ (ddiff a b f) = ddiff a b (rename φ f) := by
  rw [rename_ddiff hφ hab, ha, hb]

/-- Divided differences of disjoint pairs of variables commute. -/
theorem ddiff_ddiff_comm {c d : σ} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (f : MvPolynomial σ k) :
    ddiff a b (ddiff c d f) = ddiff c d (ddiff a b f) := by
  apply ddiff_eq_of_mul hab
  have hsym : rename (swap c d) (X a - X b : MvPolynomial σ k) = X a - X b := by
    simp [swap_apply_of_ne_of_ne hac had, swap_apply_of_ne_of_ne hbc hbd]
  rw [← ddiff_mul_of_rename_eq hcd hsym, ddiff_spec hab, map_sub,
    rename_ddiff (swap a b).injective hcd, swap_apply_of_ne_of_ne hac.symm hbc.symm,
    swap_apply_of_ne_of_ne had.symm hbd.symm]

/-! ### The nilHecke braid relation -/

/-- `Δ · ∂_{ab} ∂_{bc} ∂_{ab} f` is the alternating sum of the `S₃`-translates of `f`,
where `Δ = (X a - X b)(X a - X c)(X b - X c)`. -/
theorem ddiff_braid_aux {c : σ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (f : MvPolynomial σ k) :
    (X a - X b) * (X a - X c) * (X b - X c) * ddiff a b (ddiff b c (ddiff a b f)) =
      f - rename (swap a b) f - rename (swap b c) f
        + rename (swap b c) (rename (swap a b) f) + rename (swap a b) (rename (swap b c) f)
        - rename (swap a b) (rename (swap b c) (rename (swap a b) f)) := by
  have E1 := ddiff_spec hab f
  have E2 := ddiff_spec hbc (ddiff a b f)
  have E3 := ddiff_spec hab (ddiff b c (ddiff a b f))
  have s1E2 := congrArg (rename (swap a b)) E2
  have s2E1 := congrArg (rename (swap b c)) E1
  have s1E1 := congrArg (rename (swap a b)) E1
  have s1s2E1 := congrArg (rename (swap a b)) s2E1
  have h1 : swap a b c = c := swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)
  have h2 : swap b c a = a := swap_apply_of_ne_of_ne hab hac
  simp only [map_mul, map_sub, rename_X, swap_apply_left, swap_apply_right, h1, h2,
    rename_swap_rename_swap] at s1E2 s2E1 s1E1 s1s2E1
  apply X_sub_X_mul_left_cancel hab
  linear_combination (X a - X b) * (X a - X c) * (X b - X c) * E3
    + (X a - X b) * (X a - X c) * E2 - (X a - X b) * (X b - X c) * s1E2
    + (X a - X c) * E1 - (X a - X b) * s2E1 + (X b - X c) * s1E1 + (X a - X b) * s1s2E1

theorem swap_mul_swap_mul_swap_eq {α : Type*} [DecidableEq α] {a b c : α} (hbc : b ≠ c)
    (hac : a ≠ c) : swap a b * swap b c * swap a b = swap a c := by
  rw [show swap a b * swap b c * swap a b = swap a b * swap b c * (swap a b)⁻¹ by
    rw [swap_inv], ← swap_apply_apply, swap_apply_right,
    swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]

/-- The braid relation for transpositions of three distinct elements. -/
theorem swap_braid {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : swap a b * swap b c * swap a b = swap b c * swap a b * swap b c := by
  have e1 := swap_mul_swap_mul_swap_eq hbc hac
  have e2 : swap b c * swap a b * swap b c = swap a c := by
    rw [show swap b c * swap a b * swap b c = swap b c * swap a b * (swap b c)⁻¹ by
      rw [swap_inv], ← swap_apply_apply, swap_apply_left, swap_apply_of_ne_of_ne hab hac]
  rw [e1, e2]

theorem rename_swap_braid {c : σ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (f : MvPolynomial σ k) :
    rename (swap a b) (rename (swap b c) (rename (swap a b) f)) =
      rename (swap b c) (rename (swap a b) (rename (swap b c) f)) := by
  have : (⇑(swap a b) ∘ ⇑(swap b c) ∘ ⇑(swap a b)) = ⇑(swap b c) ∘ ⇑(swap a b) ∘ ⇑(swap b c) := by
    rw [← Perm.coe_mul, ← Perm.coe_mul, ← Perm.coe_mul, ← Perm.coe_mul, ← mul_assoc,
      ← mul_assoc, swap_braid hab hbc hac]
  simp only [rename_rename, this]

/-- The nilHecke braid relation `∂_{ab} ∂_{bc} ∂_{ab} = ∂_{bc} ∂_{ab} ∂_{bc}`
for three distinct variables. -/
theorem ddiff_braid {c : σ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (f : MvPolynomial σ k) :
    ddiff a b (ddiff b c (ddiff a b f)) = ddiff b c (ddiff a b (ddiff b c f)) := by
  have hL := ddiff_braid_aux hab hbc hac f
  have hR := ddiff_braid_aux hbc.symm hab.symm hac.symm f
  rw [ddiff_comm hbc, ddiff_comm hab, ddiff_comm hbc] at hR
  simp only [map_neg, neg_neg, mul_neg] at hR
  rw [swap_comm c b, swap_comm b a, ← rename_swap_braid hab hbc hac] at hR
  apply X_sub_X_mul_left_cancel hab
  apply X_sub_X_mul_left_cancel hac
  apply X_sub_X_mul_left_cancel hbc
  linear_combination hL - hR

end Categorification
