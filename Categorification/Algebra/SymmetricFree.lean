/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Categorification.Algebra.DividedDifference

/-!
# Polynomials are free over symmetric polynomials (E. Artin)

For a commutative ring `k` and `n : ℕ`, the polynomial ring `k[x_0, …, x_{n-1}]` is a free module
over the subring `symmetricSubalgebra (Fin n) k` of symmetric polynomials, of rank `n!`.
A basis is given by the *staircase monomials* `x^u = ∏ a, x_a ^ u a` with `u a ≤ a` for every `a`
(0-indexed: the exponent of `x_a` is at most `a`, so `x_0` never occurs and `x_{n-1}` occurs to
power at most `n - 1`).

## Main results

* `Categorification.symmetricBasis` : the staircase basis
  `Basis {u : Fin n → ℕ // ∀ a, u a ≤ a} (symmetricSubalgebra (Fin n) k) (MvPolynomial (Fin n) k)`,
  with `symmetricBasis_apply : symmetricBasis k n u = ∏ a, X a ^ u.1 a`;
* `Categorification.card_staircase` : the index set has `n!` elements;
* `Categorification.symmetric_free`, `Categorification.symmetric_finite` : freeness and finiteness;
* `Categorification.finrank_symmetric` : `finrank = n!` when `k` is nontrivial.

All statements hold over an arbitrary commutative ring `k`.

## Proof

Induction on `n`, generalising the coefficient ring. Write `y = x_n` for the last of `n + 1`
variables and identify `k[x_0, …, x_n] ≅ k[y][x_0, …, x_{n-1}]` (`lastVarEquiv`).

* *Tower step.* Polynomials symmetric in `x_0, …, x_{n-1}` are exactly the combinations
  `∑_{j ≤ n} s_j y^j` with `s_j` symmetric in all `n + 1` variables, uniquely
  (`exists_sum_mul_pow_last`, `eq_zero_of_sum_mul_pow_last`). Existence uses the fundamental
  theorem of symmetric polynomials over `k[y]` (Mathlib's `esymmAlgHom_fin_bijective`), the
  recursion `e_{r+1} = e'_{r+1} + y e'_r` (`esymm_succ_castSucc`) and the monic relation
  `∏_i (y - x_i) = 0`. Uniqueness: permuting `y` with each `x_i` gives a Vandermonde system whose
  determinant `∏ (x_j - x_i)` is a non-zero-divisor (`isRegular_X_sub_X`).
* *Induction step.* Apply the induction hypothesis over the coefficient ring `k[y]` and combine it
  with the tower step.
-/

namespace Categorification

open MvPolynomial Finset

universe u

section Esymm

/-- Recursion for elementary symmetric functions of a multiset. -/
theorem multiset_esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (r : ℕ) :
    (a ::ₘ s).esymm (r + 1) = s.esymm (r + 1) + a * s.esymm r := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

/-- Elementary symmetric functions commute with ring homomorphisms. -/
theorem multiset_esymm_map_ringHom {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (s : Multiset R) (r : ℕ) : (s.map f).esymm r = f (s.esymm r) := by
  simp [Multiset.esymm, Multiset.powersetCard_map, map_multiset_sum, map_multiset_prod,
    Multiset.map_map]

private theorem univ_val_map_fin {M : Type*} {n : ℕ} (f : Fin (n + 1) → M) :
    (Finset.univ : Finset (Fin (n + 1))).val.map f =
      f (Fin.last n) ::ₘ (Finset.univ : Finset (Fin n)).val.map (fun i => f i.castSucc) := by
  rw [Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ', List.concat_eq_append,
    ← Multiset.coe_add, add_comm, ← Multiset.singleton_add]
  rfl

variable {k : Type*} [CommRing k]

/-- `e_{r+1}(x_0, …, x_n) = e_{r+1}(x_0, …, x_{n-1}) + x_n e_r(x_0, …, x_{n-1})`. -/
theorem esymm_succ_castSucc (n r : ℕ) :
    esymm (Fin (n + 1)) k (r + 1) =
      rename Fin.castSucc (esymm (Fin n) k (r + 1)) +
        X (Fin.last n) * rename Fin.castSucc (esymm (Fin n) k r) := by
  simp only [esymm_eq_multiset_esymm]
  rw [univ_val_map_fin, multiset_esymm_cons_succ]
  have : ∀ j, (Finset.univ.val.map fun i : Fin n =>
      (X i.castSucc : MvPolynomial (Fin (n + 1)) k)).esymm j
      = rename Fin.castSucc
          ((Finset.univ.val.map (X : Fin n → MvPolynomial (Fin n) k)).esymm j) := by
    intro j
    rw [← AlgHom.coe_toRingHom, ← multiset_esymm_map_ringHom, Multiset.map_map]
    congr 2
    funext i
    simp
  rw [this, this]

end Esymm

variable (k : Type u) [CommRing k]

section LastVar

/-- Separating the last variable: `k[x_0, …, x_n] ≃ k[y][x_0, …, x_{n-1}]`, `x_n ↦ y`. -/
noncomputable def lastVarEquiv (n : ℕ) :
    MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin n) (Polynomial k) :=
  (renameEquiv k (finSuccEquiv' (Fin.last n))).trans (optionEquivRight k (Fin n))

variable {k}

@[simp]
theorem lastVarEquiv_X_last (n : ℕ) :
    lastVarEquiv k n (X (Fin.last n)) = C Polynomial.X := by
  simp [lastVarEquiv, finSuccEquiv'_at, optionEquivRight_X_none]

@[simp]
theorem lastVarEquiv_X_castSucc {n : ℕ} (a : Fin n) :
    lastVarEquiv k n (X a.castSucc) = X a := by
  simp [lastVarEquiv, finSuccEquiv'_below (Fin.castSucc_lt_last a), optionEquivRight_X_some]

theorem lastVarEquiv_rename_castSucc {n : ℕ} (p : MvPolynomial (Fin n) k) :
    lastVarEquiv k n (rename Fin.castSucc p) = map Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [rename_C, map_C, ← algebraMap_eq, AlgEquiv.commutes]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, rename_X, lastVarEquiv_X_castSucc, map_X]

theorem lastVarEquiv_symm_C {n : ℕ} (c : Polynomial k) :
    (lastVarEquiv k n).symm (C c) = Polynomial.aeval (X (Fin.last n)) c := by
  have h : ((lastVarEquiv k n).toAlgHom.comp (Polynomial.aeval (X (Fin.last n)))) =
      IsScalarTower.toAlgHom k (Polynomial k) (MvPolynomial (Fin n) (Polynomial k)) :=
    Polynomial.algHom_ext (by simp)
  have := congrArg (fun f => f c) h
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    IsScalarTower.coe_toAlgHom', algebraMap_eq] at this
  rw [← this, AlgEquiv.symm_apply_apply]

/-- A permutation of `Fin n`, extended to `Fin (n + 1)` by fixing the last element. -/
def extendLastPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' (Fin.last n)).trans ((Equiv.optionCongr σ).trans (finSuccEquiv' (Fin.last n)).symm)

theorem lastVarEquiv_rename_extendLastPerm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : MvPolynomial (Fin (n + 1)) k) :
    lastVarEquiv k n (rename (extendLastPerm σ) p) = rename σ (lastVarEquiv k n p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [rename_C, ← algebraMap_eq, AlgEquiv.commutes, MvPolynomial.algebraMap_apply, rename_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp only [lastVarEquiv, extendLastPerm, AlgEquiv.trans_apply, renameEquiv_apply, rename_X,
      Equiv.trans_apply, Equiv.apply_symm_apply]
    cases finSuccEquiv' (Fin.last n) i with
    | none => simp [optionEquivRight_X_none]
    | some a => simp [optionEquivRight_X_some]

theorem isSymmetric_lastVarEquiv {n : ℕ} {q : MvPolynomial (Fin (n + 1)) k} (hq : q.IsSymmetric) :
    (lastVarEquiv k n q).IsSymmetric := fun σ => by
  rw [← lastVarEquiv_rename_extendLastPerm, hq]

theorem lastVarEquiv_symm_esymm (n r : ℕ) :
    (lastVarEquiv k n).symm (esymm (Fin n) (Polynomial k) r) =
      rename Fin.castSucc (esymm (Fin n) k r) := by
  rw [AlgEquiv.symm_apply_eq, lastVarEquiv_rename_castSucc, map_esymm]

end LastVar

section Tower

variable {k}

/-- The Sym-span of `1, y, …, y^n`, where `y = x_n` is the last of `n + 1` variables. -/
noncomputable abbrev lastPowSpan (n : ℕ) :
    Submodule (symmetricSubalgebra (Fin (n + 1)) k) (MvPolynomial (Fin (n + 1)) k) :=
  Submodule.span _ (Set.range fun j : Fin (n + 1) => (X (Fin.last n) : MvPolynomial _ k) ^ (j : ℕ))

theorem sym_mul_pow_mem_lastPowSpan {n : ℕ} {s : MvPolynomial (Fin (n + 1)) k}
    (hs : s.IsSymmetric) {m : ℕ} (hm : m ≤ n) :
    s * X (Fin.last n) ^ m ∈ lastPowSpan n := by
  have : s * X (Fin.last n) ^ m =
      (⟨s, hs⟩ : symmetricSubalgebra (Fin (n + 1)) k) •
        (X (Fin.last n) ^ ((⟨m, by omega⟩ : Fin (n + 1)) : ℕ)) := by
    rw [Subalgebra.smul_def, smul_eq_mul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The monic relation: `y^{n+1}` lies in the Sym-span of `1, y, …, y^n`. -/
theorem last_pow_succ_mem_lastPowSpan (n : ℕ) :
    (X (Fin.last n) : MvPolynomial (Fin (n + 1)) k) ^ (n + 1) ∈ lastPowSpan n := by
  set y : MvPolynomial (Fin (n + 1)) k := X (Fin.last n)
  have hv := congrArg (Polynomial.eval (-y)) (prod_C_add_X_eq_sum_esymm k (Fin (n + 1)))
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow, Fintype.card_fin] at hv
  rw [Finset.prod_eq_zero (Finset.mem_univ (Fin.last n)) (by simp [y]),
    Finset.sum_range_succ', esymm_zero, one_mul, Nat.sub_zero] at hv
  have hmem : (-1) ^ (n + 1) * y ^ (n + 1) ∈ lastPowSpan n := by
    rw [← neg_pow, eq_neg_of_add_eq_zero_right hv.symm]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
    have hj : j < n + 1 := Finset.mem_range.mp hj
    rw [neg_pow, ← mul_assoc]
    refine sym_mul_pow_mem_lastPowSpan ?_ (by omega)
    rw [← mem_symmetricSubalgebra]
    exact Subalgebra.mul_mem _ ((mem_symmetricSubalgebra _).2 (esymm_isSymmetric _ _ _))
      (Subalgebra.pow_mem _ (Subalgebra.neg_mem _ (Subalgebra.one_mem _)) _)
  rcases neg_one_pow_eq_or (MvPolynomial (Fin (n + 1)) k) (n + 1) with h | h
  · simpa [h] using hmem
  · simpa [h] using Submodule.neg_mem _ hmem

theorem last_mul_mem_lastPowSpan {n : ℕ} {w : MvPolynomial (Fin (n + 1)) k}
    (hw : w ∈ lastPowSpan n) : X (Fin.last n) * w ∈ lastPowSpan n := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [← pow_succ']
    by_cases hj : (j : ℕ) + 1 ≤ n
    · simpa using sym_mul_pow_mem_lastPowSpan (k := k) (IsSymmetric.one) hj
    · have : (j : ℕ) = n := by omega
      rw [this]
      exact last_pow_succ_mem_lastPowSpan n
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ _ hx

theorem mul_last_pow_mem_lastPowSpan {n : ℕ} (j : ℕ) {w : MvPolynomial (Fin (n + 1)) k}
    (hw : w ∈ lastPowSpan n) : w * X (Fin.last n) ^ j ∈ lastPowSpan n := by
  induction j with
  | zero => simpa using hw
  | succ j ih => rw [pow_succ', mul_left_comm]; exact last_mul_mem_lastPowSpan ih

theorem mul_mem_lastPowSpan {n : ℕ} {w w' : MvPolynomial (Fin (n + 1)) k}
    (hw : w ∈ lastPowSpan n) (hw' : w' ∈ lastPowSpan n) : w * w' ∈ lastPowSpan n := by
  induction hw' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact mul_last_pow_mem_lastPowSpan _ hw
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm, ← smul_eq_mul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ _ hx

theorem sym_mem_lastPowSpan {n : ℕ} {s : MvPolynomial (Fin (n + 1)) k} (hs : s.IsSymmetric) :
    s ∈ lastPowSpan n := by
  simpa using sym_mul_pow_mem_lastPowSpan hs (Nat.zero_le n)

theorem last_mem_lastPowSpan (n : ℕ) :
    (X (Fin.last n) : MvPolynomial (Fin (n + 1)) k) ∈ lastPowSpan n := by
  simpa using last_mul_mem_lastPowSpan (sym_mem_lastPowSpan (k := k) (n := n) IsSymmetric.one)

/-- `lastPowSpan n` as a `k`-subalgebra. -/
noncomputable def lastPowSubalgebra (n : ℕ) : Subalgebra k (MvPolynomial (Fin (n + 1)) k) where
  carrier := (lastPowSpan (k := k) n : Set (MvPolynomial (Fin (n + 1)) k))
  mul_mem' := mul_mem_lastPowSpan
  one_mem' := sym_mem_lastPowSpan IsSymmetric.one
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  algebraMap_mem' c := by rw [algebraMap_eq]; exact sym_mem_lastPowSpan (IsSymmetric.C c)

theorem mem_lastPowSubalgebra {n : ℕ} {w : MvPolynomial (Fin (n + 1)) k} :
    w ∈ lastPowSubalgebra n ↔ w ∈ lastPowSpan n := by rfl

theorem rename_esymm_castSucc_mem (n r : ℕ) :
    rename Fin.castSucc (esymm (Fin n) k r) ∈ lastPowSubalgebra n := by
  induction r with
  | zero => rw [esymm_zero, map_one]; exact Subalgebra.one_mem _
  | succ r ih =>
    have h : rename Fin.castSucc (esymm (Fin n) k (r + 1)) = esymm (Fin (n + 1)) k (r + 1) -
        X (Fin.last n) * rename Fin.castSucc (esymm (Fin n) k r) := by
      rw [esymm_succ_castSucc]; ring
    rw [h]
    refine Subalgebra.sub_mem _ ?_ (Subalgebra.mul_mem _ ?_ ih)
    · exact sym_mem_lastPowSpan (esymm_isSymmetric (Fin (n + 1)) k (r + 1))
    · exact last_mem_lastPowSpan n

/-- Tower step, existence: a polynomial symmetric in `x_0, …, x_{n-1}` is a combination
`∑_{j ≤ n} s_j x_n^j` with `s_j` symmetric in `x_0, …, x_n`. -/
theorem mem_lastPowSpan_of_isSymmetric {n : ℕ} {q : MvPolynomial (Fin (n + 1)) k}
    (hq : (lastVarEquiv k n q).IsSymmetric) : q ∈ lastPowSpan n := by
  obtain ⟨P, hP⟩ := (esymmAlgHom_fin_bijective (Polynomial k) n).2
    ⟨_, (mem_symmetricSubalgebra _).2 hq⟩
  have hP' : aeval (fun i : Fin n => esymm (Fin n) (Polynomial k) (i + 1)) P =
      lastVarEquiv k n q := by
    rw [← esymmAlgHom_apply, hP]
  rw [← mem_lastPowSubalgebra, ← (lastVarEquiv k n).symm_apply_apply q, ← hP']
  clear hP hP' hq
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C, algebraMap_eq, lastVarEquiv_symm_C]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.2 (last_mem_lastPowSpan n))
      (Polynomial.aeval_mem_adjoin_singleton k _)
  | add p q hp hq => rw [map_add, map_add]; exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, aeval_X, lastVarEquiv_symm_esymm]
    exact Subalgebra.mul_mem _ hp (rename_esymm_castSucc_mem n _)

/-- Tower step, existence, explicit form. -/
theorem exists_sum_mul_pow_last {n : ℕ} {q : MvPolynomial (Fin (n + 1)) k}
    (hq : (lastVarEquiv k n q).IsSymmetric) :
    ∃ s : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k, (∀ j, (s j).IsSymmetric) ∧
      ∑ j, s j * X (Fin.last n) ^ (j : ℕ) = q := by
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun _).1 (mem_lastPowSpan_of_isSymmetric hq)
  refine ⟨fun j => c j, fun j => (mem_symmetricSubalgebra _).1 (c j).2, ?_⟩
  rw [← hc]
  simp only [Subalgebra.smul_def, smul_eq_mul]

/-- Tower step, uniqueness: if `∑_{j ≤ n} s_j x_n^j = 0` with every `s_j` symmetric in
`x_0, …, x_n`, then all `s_j = 0` (Vandermonde argument). -/
theorem eq_zero_of_sum_mul_pow_last {n : ℕ} (s : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k)
    (hs : ∀ j, (s j).IsSymmetric) (h : ∑ j, s j * X (Fin.last n) ^ (j : ℕ) = 0)
    (j : Fin (n + 1)) : s j = 0 := by
  set V := Matrix.vandermonde (fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) k))
  have hV : V.mulVec s = 0 := by
    funext i
    have := congrArg (rename (Equiv.swap i (Fin.last n))) h
    simp only [map_sum, map_mul, map_pow, rename_X, Equiv.swap_apply_right, hs _ _,
      map_zero] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply, V]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hdet : V.det • s = 0 := by
    rw [← Matrix.one_mulVec s, ← Matrix.smul_mulVec_assoc, ← Matrix.adjugate_mul,
      ← Matrix.mulVec_mulVec, hV, Matrix.mulVec_zero]
  have hreg : IsRegular V.det := by
    rw [Matrix.det_vandermonde]
    refine Finset.prod_induction _ IsRegular (fun a b ha hb => ha.mul hb) isRegular_one
      fun i _ => ?_
    refine Finset.prod_induction _ IsRegular (fun a b ha hb => ha.mul hb) isRegular_one
      fun j hj => ?_
    exact isRegular_X_sub_X (ne_of_gt (Finset.mem_Ioi.1 hj))
  have := congrFun hdet j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact hreg.left (show V.det * s j = V.det * 0 by rw [this, mul_zero])

end Tower

section Staircase

/-- Staircase exponent vectors `u` (with `u a ≤ a`) correspond to `Π a : Fin n, Fin (a + 1)`. -/
def staircaseEquivPi (n : ℕ) :
    {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a} ≃ ((a : Fin n) → Fin (a + 1)) where
  toFun u a := ⟨u.1 a, Nat.lt_succ_of_le (u.2 a)⟩
  invFun f := ⟨fun a => f a, fun a => Nat.le_of_lt_succ (f a).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance fintypeStaircase (n : ℕ) : Fintype {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a} :=
  Fintype.ofEquiv _ (staircaseEquivPi n).symm

/-- There are `n!` staircase exponent vectors. -/
theorem card_staircase (n : ℕ) :
    Fintype.card {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a} = n.factorial := by
  rw [Fintype.card_congr (staircaseEquivPi n), Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Fin.prod_univ_eq_prod_range (fun i => i + 1) n, Finset.prod_range_add_one_eq_factorial]

/-- Extend a staircase vector for `n` by a last exponent `j ≤ n`. -/
def staircaseSnoc {n : ℕ} (v : {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a}) (j : Fin (n + 1)) :
    {u : Fin (n + 1) → ℕ // ∀ a : Fin (n + 1), u a ≤ a} :=
  ⟨Fin.snoc (α := fun _ => ℕ) v.1 (j : ℕ), fun a => by
    refine Fin.lastCases ?_ (fun b => ?_) a
    · simpa using Nat.le_of_lt_succ j.2
    · simpa using v.2 b⟩

/-- Staircase vectors for `n + 1` split as a staircase vector for `n` and a last exponent. -/
def staircaseSplit (n : ℕ) : {u : Fin (n + 1) → ℕ // ∀ a : Fin (n + 1), u a ≤ a} ≃
    {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a} × Fin (n + 1) where
  toFun u := (⟨fun b => u.1 b.castSucc, fun b => by simpa using u.2 b.castSucc⟩,
    ⟨u.1 (Fin.last n), Nat.lt_succ_of_le (by simpa using u.2 (Fin.last n))⟩)
  invFun p := staircaseSnoc p.1 p.2
  left_inv u := by
    apply Subtype.ext
    funext a
    refine Fin.lastCases ?_ (fun b => ?_) a <;> simp [staircaseSnoc]
  right_inv p := by
    rcases p with ⟨v, j⟩
    simp only [staircaseSnoc, Fin.snoc_castSucc, Fin.snoc_last, Fin.eta]

@[simp]
theorem staircaseSplit_snoc {n : ℕ} (v : {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a})
    (j : Fin (n + 1)) : staircaseSplit n (staircaseSnoc v j) = (v, j) :=
  (staircaseSplit n).apply_symm_apply (v, j)

theorem sum_staircase_succ {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : {u : Fin (n + 1) → ℕ // ∀ a : Fin (n + 1), u a ≤ a} → M) :
    ∑ u, F u = ∑ v, ∑ j, F (staircaseSnoc v j) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (staircaseSplit n) _ _ fun u =>
    congrArg F ((staircaseSplit n).symm_apply_apply u).symm

/-- The monomial `x^u = ∏ a, x_a ^ u a`. -/
noncomputable def stairMonomial {n : ℕ} (u : Fin n → ℕ) : MvPolynomial (Fin n) k :=
  ∏ a, X a ^ u a

variable {k}

theorem stairMonomial_snoc {n : ℕ} (v : {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a})
    (j : Fin (n + 1)) :
    stairMonomial k (staircaseSnoc v j).1 =
      rename Fin.castSucc (stairMonomial k v.1) * X (Fin.last n) ^ (j : ℕ) := by
  simp [stairMonomial, staircaseSnoc, Fin.prod_univ_castSucc, map_prod]

theorem lastVarEquiv_stairMonomial {n : ℕ} (v : Fin n → ℕ) :
    lastVarEquiv k n (rename Fin.castSucc (stairMonomial k v)) =
      stairMonomial (Polynomial k) v := by
  simp [lastVarEquiv_rename_castSucc, stairMonomial, map_prod]

end Staircase

section Main

/-- Artin's theorem in explicit form: the staircase monomials are linearly independent over the
symmetric polynomials, and every polynomial is a symmetric combination of them. -/
theorem staircase_indep_and_span (n : ℕ) : ∀ (k : Type u) [CommRing k],
    (∀ g : {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a} → MvPolynomial (Fin n) k,
      (∀ u, (g u).IsSymmetric) → ∑ u, g u * stairMonomial k u.1 = 0 → ∀ u, g u = 0) ∧
    (∀ p : MvPolynomial (Fin n) k,
      ∃ g : {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a} → MvPolynomial (Fin n) k,
        (∀ u, (g u).IsSymmetric) ∧ ∑ u, g u * stairMonomial k u.1 = p) := by
  induction n with
  | zero =>
    intro k _
    have hsym : ∀ p : MvPolynomial (Fin 0) k, p.IsSymmetric := fun p σ => by
      rw [show (⇑σ : Fin 0 → Fin 0) = id from Subsingleton.elim _ _, rename_id_apply]
    have hmono : ∀ u : {u : Fin 0 → ℕ // ∀ a : Fin 0, u a ≤ a}, stairMonomial k u.1 = 1 :=
      fun u => by simp [stairMonomial]
    constructor
    · intro g _ h u
      rw [Fintype.sum_subsingleton _ u, hmono, mul_one] at h
      exact h
    · intro p
      let u0 : {u : Fin 0 → ℕ // ∀ a : Fin 0, u a ≤ a} := ⟨fun _ => 0, fun a => a.elim0⟩
      exact ⟨fun _ => p, fun _ => hsym p, by rw [Fintype.sum_subsingleton _ u0, hmono, mul_one]⟩
  | succ n ih =>
    intro k _
    obtain ⟨ihI, ihS⟩ := ih (Polynomial k)
    constructor
    · intro g hg h u
      have hsym : ∀ v, (lastVarEquiv k n
          (∑ j, g (staircaseSnoc v j) * X (Fin.last n) ^ (j : ℕ))).IsSymmetric := fun v => by
        rw [← mem_symmetricSubalgebra, map_sum]
        refine Subalgebra.sum_mem _ fun j _ => ?_
        rw [map_mul, map_pow, lastVarEquiv_X_last]
        exact Subalgebra.mul_mem _
          ((mem_symmetricSubalgebra _).2 (isSymmetric_lastVarEquiv (hg _)))
          (Subalgebra.pow_mem _ ((mem_symmetricSubalgebra _).2 (IsSymmetric.C _)) _)
      have hsum : ∑ v, lastVarEquiv k n
          (∑ j, g (staircaseSnoc v j) * X (Fin.last n) ^ (j : ℕ)) *
            stairMonomial (Polynomial k) v.1 = 0 := by
        rw [sum_staircase_succ] at h
        rw [← map_zero (lastVarEquiv k n), ← h, map_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← lastVarEquiv_stairMonomial, ← map_mul, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [stairMonomial_snoc]
        ring
      have h0 := ihI _ hsym hsum
      have key : ∀ v j, g (staircaseSnoc v j) = 0 := fun v j =>
        eq_zero_of_sum_mul_pow_last _ (fun _ => hg _)
          ((lastVarEquiv k n).injective (by rw [h0 v, map_zero])) j
      rw [← (staircaseSplit n).symm_apply_apply u]
      exact key _ _
    · intro p
      obtain ⟨G, hG, hGp⟩ := ihS (lastVarEquiv k n p)
      choose s hs hsq using fun v => exists_sum_mul_pow_last (q := (lastVarEquiv k n).symm (G v))
        (by simpa using hG v)
      refine ⟨fun u => s (staircaseSplit n u).1 (staircaseSplit n u).2, fun u => hs _ _, ?_⟩
      rw [sum_staircase_succ]
      apply (lastVarEquiv k n).injective
      rw [← hGp, map_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [staircaseSplit_snoc]
      rw [← (lastVarEquiv k n).apply_symm_apply (G v), ← hsq v, ← lastVarEquiv_stairMonomial,
        ← map_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [stairMonomial_snoc]
      ring

/-- **Artin's theorem.** Over any commutative ring `k`, `k[x_0, …, x_{n-1}]` is a free module over
the symmetric polynomials, with basis the staircase monomials `∏ a, x_a ^ u a`, `u a ≤ a`. -/
noncomputable def symmetricBasis (n : ℕ) :
    Basis {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a} (symmetricSubalgebra (Fin n) k)
      (MvPolynomial (Fin n) k) :=
  Basis.mk (v := fun u => stairMonomial k u.1)
    (Fintype.linearIndependent_iff.2 fun c hc u =>
      Subtype.ext <| (staircase_indep_and_span n k).1 (fun u => c u)
        (fun u => (mem_symmetricSubalgebra _).1 (c u).2)
        (by simpa [Subalgebra.smul_def] using hc) u)
    (fun p _ => by
      obtain ⟨g, hg, hgp⟩ := (staircase_indep_and_span n k).2 p
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨fun u => ⟨g u, (mem_symmetricSubalgebra _).2 (hg u)⟩,
        by simpa [Subalgebra.smul_def] using hgp⟩)

@[simp]
theorem symmetricBasis_apply (n : ℕ) (u : {u : Fin n → ℕ // ∀ a : Fin n, u a ≤ a}) :
    symmetricBasis k n u = ∏ a, X a ^ u.1 a := by
  simp [symmetricBasis, stairMonomial]

/-- `k[x_0, …, x_{n-1}]` is a free module over the symmetric polynomials. -/
instance symmetric_free (n : ℕ) :
    Module.Free (symmetricSubalgebra (Fin n) k) (MvPolynomial (Fin n) k) :=
  Module.Free.of_basis (symmetricBasis k n)

/-- `k[x_0, …, x_{n-1}]` is a finite module over the symmetric polynomials. -/
instance symmetric_finite (n : ℕ) :
    Module.Finite (symmetricSubalgebra (Fin n) k) (MvPolynomial (Fin n) k) :=
  Module.Finite.of_basis (symmetricBasis k n)

/-- The rank of `k[x_0, …, x_{n-1}]` over the symmetric polynomials is `n!`. -/
theorem finrank_symmetric [Nontrivial k] (n : ℕ) :
    Module.finrank (symmetricSubalgebra (Fin n) k) (MvPolynomial (Fin n) k) = n.factorial := by
  rw [Module.finrank_eq_card_basis (symmetricBasis k n), card_staircase]

end Main

end Categorification
