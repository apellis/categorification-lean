/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.ParabolicSymmetricFree

/-!
# Elementary symmetric polynomials of a set of variables

Auxiliary material for the cohomology rings of partial flag varieties (Khovanov–Lauda III,
arXiv:0807.3250v1, §5.1). For a finite set `s` of variables of `k[V]`,

  `setEsymm s r = e_r(x_v : v ∈ s) = ∑_{t ⊆ s, |t| = r} ∏_{v ∈ t} x_v`,

with generating polynomial `esSeries s = ∏_{v ∈ s} (1 + x_v t) = ∑_r e_r(s) t^r`
(`coeff_esSeries`). The Chern classes of the tautological bundles of a flag variety are
represented, in the Borel presentation, by the `e_r` of the blocks of variables; the identities
of KL III §5 are all consequences of the multiplicativity of `esSeries` on disjoint unions:

* `setEsymm_union` : `e_r(s ⊔ t) = ∑_{a + b = r} e_a(s) e_b(t)`;
* `setEsymm_insert` : `e_{r+1}(s ∪ {v}) = e_{r+1}(s) + x_v e_r(s)`;
* `setEsymm_eq_sum_insert` : `e_r(s) = ∑_{f ≤ r} (-x_v)^f e_{r-f}(s ∪ {v})` (the inverse relation).

We also record that `setEsymm` of a union of blocks of a labelling `lab : V → J` is invariant
under the label-preserving permutations (`setEsymm_labSet_mem`).
-/

namespace Categorification.Flag

open MvPolynomial Finset

variable {k : Type*} [CommRing k] {V : Type*}

/-- The elementary symmetric polynomial `e_r` in the variables `x_v`, `v ∈ s`. -/
noncomputable def setEsymm (s : Finset V) (r : ℕ) : MvPolynomial V k :=
  ∑ t ∈ s.powersetCard r, ∏ v ∈ t, X v

/-- The generating polynomial `∏_{v ∈ s} (1 + x_v t) ∈ k[V][t]`. -/
noncomputable def esSeries (s : Finset V) : Polynomial (MvPolynomial V k) :=
  ∏ v ∈ s, (1 + Polynomial.C (X v) * Polynomial.X)

theorem coeff_esSeries (s : Finset V) (r : ℕ) :
    (esSeries (k := k) s).coeff r = setEsymm s r := by
  classical
  unfold esSeries setEsymm
  rw [Finset.prod_one_add, Polynomial.finset_sum_coeff, powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_mul_distrib, prod_const, ← map_prod, Polynomial.coeff_C_mul_X_pow]
  by_cases h : t.card = r
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

theorem setEsymm_univ [Fintype V] (r : ℕ) : setEsymm (univ : Finset V) r = esymm V k r := rfl

@[simp] theorem setEsymm_zero (s : Finset V) : setEsymm (k := k) s 0 = 1 := by
  simp [setEsymm]

theorem setEsymm_eq_zero {s : Finset V} {r : ℕ} (h : s.card < r) :
    setEsymm (k := k) s r = 0 := by
  simp [setEsymm, powersetCard_eq_empty.2 h]

theorem setEsymm_empty_succ (r : ℕ) : setEsymm (k := k) (∅ : Finset V) (r + 1) = 0 :=
  setEsymm_eq_zero (by simp)

theorem esSeries_union [DecidableEq V] {s t : Finset V} (h : Disjoint s t) :
    esSeries (k := k) (s ∪ t) = esSeries s * esSeries t :=
  prod_union h

theorem esSeries_insert [DecidableEq V] {s : Finset V} {v : V} (h : v ∉ s) :
    esSeries (k := k) (insert v s) = (1 + Polynomial.C (X v) * Polynomial.X) * esSeries s :=
  prod_insert h

/-- `e_r(s ⊔ t) = ∑_{a + b = r} e_a(s) e_b(t)`. -/
theorem setEsymm_union [DecidableEq V] {s t : Finset V} (h : Disjoint s t) (r : ℕ) :
    setEsymm (k := k) (s ∪ t) r = ∑ p ∈ antidiagonal r, setEsymm s p.1 * setEsymm t p.2 := by
  rw [← coeff_esSeries, esSeries_union h, Polynomial.coeff_mul]
  simp only [coeff_esSeries]

/-- `e_{r+1}(s ∪ {v}) = e_{r+1}(s) + x_v e_r(s)` for `v ∉ s`. -/
theorem setEsymm_insert [DecidableEq V] {s : Finset V} {v : V} (h : v ∉ s) (r : ℕ) :
    setEsymm (k := k) (insert v s) (r + 1) = setEsymm s (r + 1) + X v * setEsymm s r := by
  rw [← coeff_esSeries, esSeries_insert h, add_mul, one_mul, Polynomial.coeff_add, mul_assoc,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, coeff_esSeries, coeff_esSeries]

/-- The inverse relation: `e_r(s) = ∑_{f ≤ r} (-x_v)^f e_{r-f}(s ∪ {v})` for `v ∉ s`
(the algebraic content of KL III eqs. (5.28), (5.29)). -/
theorem setEsymm_eq_sum_insert [DecidableEq V] {s : Finset V} {v : V} (h : v ∉ s) :
    ∀ r : ℕ, setEsymm (k := k) s r =
      ∑ f ∈ range (r + 1), (-X v) ^ f * setEsymm (insert v s) (r - f)
  | 0 => by simp
  | r + 1 => by
    rw [sum_range_succ', pow_zero, one_mul, Nat.sub_zero, setEsymm_insert h]
    have ih := setEsymm_eq_sum_insert h r
    have : ∑ f ∈ range (r + 1), (-X v : MvPolynomial V k) ^ (f + 1) *
        setEsymm (insert v s) (r + 1 - (f + 1)) = -X v * setEsymm s r := by
      rw [ih, mul_sum]
      refine sum_congr rfl fun f _ => ?_
      rw [pow_succ, Nat.add_sub_add_right]
      ring
    rw [this]
    ring

theorem rename_setEsymm {W : Type*} (f : V ↪ W) (s : Finset V) (r : ℕ) :
    rename f (setEsymm (k := k) s r) = setEsymm (s.map f) r := by
  simp only [setEsymm, map_sum, map_prod, rename_X, powersetCard_map, sum_map]
  refine sum_congr rfl fun t _ => ?_
  change _ = ∏ v ∈ t.map f, X v
  rw [prod_map]

theorem setEsymm_isHomogeneous (s : Finset V) (r : ℕ) :
    (setEsymm (k := k) s r).IsHomogeneous r := by
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  have := IsHomogeneous.prod t (fun v => (X v : MvPolynomial V k)) (fun _ => 1)
    (fun v _ => isHomogeneous_X k v)
  simpa [(mem_powersetCard.1 ht).2] using this

theorem constantCoeff_setEsymm_succ (s : Finset V) (r : ℕ) :
    constantCoeff (setEsymm (k := k) s (r + 1)) = 0 := by
  have h := setEsymm_isHomogeneous (k := k) s (r + 1)
  rw [constantCoeff_eq]
  exact h.coeff_eq_zero (by simp)

/-! ### Blocks of a labelling -/

section Label

variable [Fintype V] {J : Type*} (lab : V → J)

/-- The set of variables whose label satisfies `p`. -/
def labSet (p : J → Prop) [DecidablePred p] : Finset V := univ.filter fun v => p (lab v)

@[simp] theorem mem_labSet (p : J → Prop) [DecidablePred p] {v : V} :
    v ∈ labSet lab p ↔ p (lab v) := by
  simp [labSet]

/-- The elementary symmetric polynomials of a union of blocks of `lab` are invariant under the
label-preserving permutations. -/
theorem setEsymm_labSet_mem (p : J → Prop) [DecidablePred p] (r : ℕ) :
    setEsymm (k := k) (labSet lab p) r ∈ labelInvariants k lab := by
  intro g hg
  have hs : (labSet lab p).map g.toEmbedding = labSet lab p := by
    ext v
    rw [mem_map_equiv, mem_labSet, mem_labSet]
    have := congrFun hg (g.symm v)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
    rw [← this]
  have := rename_setEsymm (k := k) g.toEmbedding (labSet lab p) r
  rw [hs] at this
  exact this

end Label

end Categorification.Flag
