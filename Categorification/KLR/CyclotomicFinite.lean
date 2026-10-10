/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Cyclotomic
import Categorification.KLR.Symmetries
import Categorification.KLR.Spanning
import Categorification.Algebra.NilHecke

/-!
# Dots in cyclotomic KLR algebras are integral; `R^Λ(ν)` is a finite `k`-module

S.-J. Kang, M. Kashiwara, *Categorification of highest weight modules via
Khovanov–Lauda–Rouquier algebras*, arXiv:1102.4677v4, §4.1: Lemma 4.2, Lemma 4.3 (a) and
Corollary 4.4.

The hypotheses are those of Kang–Kashiwara: each `a_i` is monic, and for `i ≠ j` the polynomial
`Q_{ij}(u, v)` has a unit leading coefficient as a polynomial in `v` (KK assume
`t_{i,j;-a_{ij},0}` is a unit and `Q_{ij}(u, v) = Q_{ji}(v, u)`). The base ring `k` is any
commutative ring and the index type `I` is arbitrary.

## Main results

* `KLRAlgebra.ψ_mul_pol_mul_e`: `ψ_j f e(𝐢) = (s_j f) ψ_j e(𝐢) + [i_j = i_{j+1}] (∂_j f) e(𝐢)`
  for a polynomial `f` in the dots;
* `KLRAlgebra.dd_smul_eq_zero`, `KLRAlgebra.swap_smul_eq_zero` (KK Lemma 4.2): if
  `f e(𝐢) M = 0` and `i_j = i_{j+1}`, then `(∂_j f) e(𝐢) M = 0` and `(s_j f) e(𝐢) M = 0`;
* `exists_monic_mem_span`: for monic `g(x)` and `q(x, y)` with unit leading coefficient in `y`,
  the ideal `(g(x), q(x, y))` contains a monic polynomial in `y` (proof of KK Lemma 4.3 (a));
* `KLRAlgebra.exists_monic_dots`, `CycKLR.exists_monic_dots` (KK Lemma 4.3 (a)): all dots
  satisfy a common monic polynomial on any `R(ν)`-module killed by the cyclotomic ideal, in
  particular in `R^Λ(ν)`;
* `CycKLR.module_finite` (KK Corollary 4.4): `R^Λ(ν)` is a finitely generated `k`-module.
-/

namespace Categorification.KLR

open Polynomial Equiv NilHecke TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-! ### A monic polynomial in `y` in the ideal `(g(x), q(x, y))` -/

/-- A polynomial `q(x, y)` in two variables, viewed as a polynomial in `y` with coefficients in
`k[x]`. -/
noncomputable def polyInY (q : MvPolynomial (Fin 2) k) : (k[X])[X] :=
  MvPolynomial.aeval ![Polynomial.C Polynomial.X, Polynomial.X] q

/-- Evaluating `polyInY q` back at `x ↦ π(X 0)`, `y ↦ π(X 1)` recovers `π q`. -/
theorem eval₂_polyInY {R : Type*} [CommRing R] [Algebra k R]
    (π : MvPolynomial (Fin 2) k →ₐ[k] R) (q : MvPolynomial (Fin 2) k) :
    (polyInY q).eval₂ (Polynomial.eval₂RingHom (algebraMap k R) (π (MvPolynomial.X 0)))
      (π (MvPolynomial.X 1)) = π q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp [polyInY, Polynomial.eval₂_C]
  | add p q hp hq => simp only [polyInY, map_add, Polynomial.eval₂_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p n hp =>
    simp only [polyInY, map_mul, Polynomial.eval₂_mul, MvPolynomial.aeval_X] at hp ⊢
    rw [hp]
    congr 1
    fin_cases n <;> simp

/-- If `g` is monic and `q(x, y)` has unit leading coefficient as a polynomial in `y`, then the
ideal `(g(x), q(x, y))` of `k[x, y]` contains a monic polynomial in `y` alone (Kang–Kashiwara,
proof of Lemma 4.3 (a), case (i)). -/
theorem exists_monic_mem_span (g : k[X]) (hg : g.Monic) (q : MvPolynomial (Fin 2) k)
    (hq : IsUnit (polyInY q).leadingCoeff) :
    ∃ h : k[X], h.Monic ∧ aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) h ∈
      Ideal.span {aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) g, q} := by
  classical
  set J := Ideal.span {aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) g, q}
  let π : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k ⧸ J := Ideal.Quotient.mkₐ k J
  have hgJ : aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) g ∈ J :=
    Ideal.subset_span (by simp)
  have hqJ : q ∈ J := Ideal.subset_span (by simp)
  have hπ : ∀ p, p ∈ J ↔ π p = 0 := fun p => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  have : Module.Finite k (AdjoinRoot g) := hg.finite_adjoinRoot
  let fB : AdjoinRoot g →+* MvPolynomial (Fin 2) k ⧸ J :=
    AdjoinRoot.lift (algebraMap k _) (π (MvPolynomial.X 0)) (by
      rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, ← hπ]; exact hgJ)
  have hfB : fB.comp (AdjoinRoot.mk g) =
      Polynomial.eval₂RingHom (algebraMap k _) (π (MvPolynomial.X 0)) := by
    ext p <;> simp [fB]
  let u := (polyInY q).leadingCoeff
  have hu : IsUnit (AdjoinRoot.mk g u) := hq.map _
  let ψ : (AdjoinRoot g)[X] := Polynomial.C ((hu.unit⁻¹ : (AdjoinRoot g)ˣ) : AdjoinRoot g) * (polyInY q).map (AdjoinRoot.mk g)
  have hψ : ψ.Monic := by
    rcases subsingleton_or_nontrivial (AdjoinRoot g) with hB | hB
    · exact Subsingleton.elim _ _
    · apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
      rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hu.ne_zero]
      exact hu.unit.inv_mul
  have : Module.Finite (AdjoinRoot g) (AdjoinRoot ψ) := hψ.finite_adjoinRoot
  have : Module.Finite k (AdjoinRoot ψ) := Module.Finite.trans (AdjoinRoot g) _
  obtain ⟨h, hmon, hy⟩ := IsIntegral.of_finite k (AdjoinRoot.root ψ)
  let Φ : AdjoinRoot ψ →+* MvPolynomial (Fin 2) k ⧸ J :=
    AdjoinRoot.lift fB (π (MvPolynomial.X 1)) (by
      simp only [ψ, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_map, hfB,
        eval₂_polyInY]
      rw [(hπ q).mp hqJ, mul_zero])
  refine ⟨h, hmon, (hπ _).2 ?_⟩
  have hΦ : Φ.comp (algebraMap k (AdjoinRoot ψ)) = algebraMap k _ := by
    ext c
    simp [Φ, fB, AdjoinRoot.algebraMap_eq', AdjoinRoot.lift_of]
  rw [← Polynomial.aeval_algHom_apply, Polynomial.aeval_def, ← hΦ,
    show π (MvPolynomial.X 1) = Φ (AdjoinRoot.root ψ) by simp [Φ, AdjoinRoot.lift_root],
    ← Polynomial.hom_eval₂, hy, map_zero]

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

/-- The transposition of the strands `j` and `j + 1`, acting on polynomials in the dots. -/
noncomputable abbrev swapPol (j : ℕ) (h : j + 1 < m) :
    MvPolynomial (Fin m) k →ₐ[k] MvPolynomial (Fin m) k :=
  MvPolynomial.rename (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩)

/-- **Crossings past polynomials**: `ψ_j f e(𝐢) = (s_j f) ψ_j e(𝐢) + [i_j = i_{j+1}] (∂_j f) e(𝐢)`,
where `∂_j` is the divided difference in the dots `x_j, x_{j+1}`. -/
theorem ψ_mul_pol_mul_e (j : ℕ) (h : j + 1 < m) (i : Seq ν) (f : MvPolynomial (Fin m) k) :
    (ψ j * pol f * e i : KLRAlgebra k Q ν) =
      pol (swapPol j h f) * ψ j * e i +
        if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then pol (dd k m j f) * e i else 0 := by
  have hne : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := fun e => by simp [Fin.ext_iff] at e
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.algHom_C, dd_of_lt h, ddiff_C hne, map_zero, zero_mul, ite_self,
      add_zero]
    rw [AlgHom.commutes, Algebra.commutes c (ψ j)]
  | add f g hf hg =>
    simp only [map_add, mul_add, add_mul, hf, hg]
    split_ifs <;> abel
  | mul_X f a hf =>
    have hxe : ∀ b : Fin m, (x b * e i : KLRAlgebra k Q ν) = e i * x b := fun b => x_mul_e b i
    -- `ψ f x_a e = (ψ f e) x_a`
    have hL : (ψ j * pol (f * MvPolynomial.X a) * e i : KLRAlgebra k Q ν) =
        (ψ j * pol f * e i) * x a := by
      rw [map_mul, pol_X, mul_assoc, mul_assoc, hxe, ← mul_assoc, ← mul_assoc, mul_assoc]
    rw [hL, hf, add_mul]
    -- the two pieces
    have hdd : dd k m j (f * MvPolynomial.X a) =
        dd k m j f * MvPolynomial.X a + swapPol j h f * dd k m j (MvPolynomial.X a) := by
      rw [dd_of_lt h]; exact ddiff_mul hne f _
    have hsw : swapPol j h (f * MvPolynomial.X a) =
        swapPol j h f * MvPolynomial.X (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩ a) := by
      simp
    rw [hdd, hsw]
    -- `ψ_j x_a e(𝐢)`
    have key : (ψ j * x a * e i : KLRAlgebra k Q ν) =
        x (swap (⟨j, by omega⟩ : Fin m) ⟨j + 1, h⟩ a) * ψ j * e i +
          if i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩ then
            pol (dd k m j (MvPolynomial.X a)) * e i else 0 := by
      by_cases ha : a = ⟨j, by omega⟩
      · subst ha
        have := dot_cross_right (Q := Q) j h i
        rw [swap_apply_left, dd_of_lt h, ddiff_X_left hne, map_one, one_mul]
        rw [sub_mul] at this
        split_ifs at this ⊢
        · exact sub_eq_iff_eq_add'.mp this
        · rw [add_zero]; exact sub_eq_zero.mp this
      · by_cases hb : a = ⟨j + 1, h⟩
        · subst hb
          have := dot_cross_left (Q := Q) j h i
          rw [swap_apply_right, dd_of_lt h, ddiff_X_right hne, map_neg, map_one, neg_one_mul]
          rw [sub_mul] at this
          split_ifs at this ⊢
          · rw [sub_eq_iff_eq_add'.mp this]; abel
          · rw [add_zero]; exact (sub_eq_zero.mp this).symm
        · have h1 : a.val ≠ j := fun e => ha (Fin.ext e)
          have h2 : a.val ≠ j + 1 := fun e => hb (Fin.ext e)
          rw [swap_apply_of_ne_of_ne ha hb, dd_of_lt h, ddiff_X_of_ne hne ha hb, map_zero,
            zero_mul, ite_self, add_zero, x_mul_ψ a j h1 h2]
    have e1 : (pol (swapPol j h f) * ψ j * e i * x a : KLRAlgebra k Q ν) =
        pol (swapPol j h f) * (ψ j * x a * e i) := by
      simp only [mul_assoc, hxe]
    rw [e1, key]
    split_ifs with hc
    · have e2 : (pol (dd k m j f) * e i * x a : KLRAlgebra k Q ν) =
          pol (dd k m j f * MvPolynomial.X a) * e i := by
        rw [map_mul, pol_X, mul_assoc, ← hxe, ← mul_assoc]
      rw [e2]
      simp only [map_add, map_mul, pol_X]
      noncomm_ring
    · simp only [map_mul, pol_X]
      noncomm_ring

theorem ψ_mul_e_comm (j : ℕ) (h : j + 1 < m) {i : Seq ν}
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) :
    (ψ j * e i : KLRAlgebra k Q ν) = e i * ψ j := by
  rw [ψ_mul_e, sadj_smul_eq_self h hi]

theorem ψ_mul_ψ_mul_e_same (j : ℕ) (h : j + 1 < m) {i : Seq ν}
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) :
    (ψ j * ψ j * e i : KLRAlgebra k Q ν) = 0 := by
  simp only [ψ_sq j h i, hi, ↓reduceIte]

/-- The divided difference identity `(x_j - x_{j+1}) ∂_j f = f - s_j f` in `R(ν)`. -/
theorem pol_sub_mul_pol_dd (j : ℕ) (h : j + 1 < m) (f : MvPolynomial (Fin m) k) :
    (pol (MvPolynomial.X ⟨j, by omega⟩ - MvPolynomial.X ⟨j + 1, h⟩) * pol (dd k m j f) :
        KLRAlgebra k Q ν) = pol f - pol (swapPol j h f) := by
  have hne : (⟨j, by omega⟩ : Fin m) ≠ ⟨j + 1, h⟩ := fun e => by simp [Fin.ext_iff] at e
  rw [← map_mul, dd_of_lt h, ddiff_spec hne, map_sub]

section Module

variable {M : Type*} [AddCommGroup M] [Module (KLRAlgebra k Q ν) M]

/-- **Kang–Kashiwara, Lemma 4.2** (label `lem:van`, divided difference part): if
`f e(𝐢) M = 0` and `i_j = i_{j+1}`, then `(∂_j f) e(𝐢) M = 0`. -/
theorem dd_smul_eq_zero (j : ℕ) (h : j + 1 < m) {i : Seq ν}
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) {f : MvPolynomial (Fin m) k}
    (hf : ∀ v : M, (pol f * e i : KLRAlgebra k Q ν) • v = 0) (v : M) :
    (pol (dd k m j f) * e i : KLRAlgebra k Q ν) • v = 0 := by
  have hc := ψ_mul_pol_mul_e (Q := Q) j h i f
  simp only [hi, ↓reduceIte] at hc
  -- `ψ f ψ e = (∂f) ψ e`
  have h1 : (ψ j * pol f * ψ j * e i : KLRAlgebra k Q ν) = pol (dd k m j f) * ψ j * e i := by
    have : (ψ j * pol f * ψ j * e i : KLRAlgebra k Q ν) = (ψ j * pol f * e i) * ψ j := by
      rw [mul_assoc (ψ j * pol f), ψ_mul_e_comm j h hi, ← mul_assoc]
    have hz : (ψ j * (ψ j * e i) : KLRAlgebra k Q ν) = 0 := by
      rw [← mul_assoc]; exact ψ_mul_ψ_mul_e_same j h hi
    rw [this, hc, add_mul]
    simp only [mul_assoc, ← ψ_mul_e_comm j h hi, hz, mul_zero, zero_add]
  -- solve for `(∂f) e`
  have h2 : (pol (dd k m j f) * e i : KLRAlgebra k Q ν) =
      pol (MvPolynomial.X ⟨j, by omega⟩ - MvPolynomial.X ⟨j + 1, h⟩) *
          (ψ j * pol f * ψ j * e i) - pol f * ψ j * e i + ψ j * pol f * e i := by
    rw [h1, ← mul_assoc, ← mul_assoc, pol_sub_mul_pol_dd j h f, sub_mul, sub_mul, hc]
    abel
  rw [h2, add_smul, sub_smul]
  have t1 : ((pol (MvPolynomial.X ⟨j, by omega⟩ - MvPolynomial.X ⟨j + 1, h⟩) *
      (ψ j * pol f * ψ j * e i) : KLRAlgebra k Q ν)) • v = 0 := by
    rw [show (ψ j * pol f * ψ j * e i : KLRAlgebra k Q ν) =
        ψ j * ((pol f * e i) * ψ j) by
          rw [mul_assoc (pol f), ← ψ_mul_e_comm j h hi]; noncomm_ring,
      mul_smul, mul_smul, mul_smul, hf, smul_zero, smul_zero]
  have t2 : ((pol f * ψ j * e i : KLRAlgebra k Q ν)) • v = 0 := by
    rw [mul_assoc, ψ_mul_e_comm j h hi, ← mul_assoc, mul_smul, hf]
  have t3 : ((ψ j * pol f * e i : KLRAlgebra k Q ν)) • v = 0 := by
    rw [mul_assoc, mul_smul, hf, smul_zero]
  rw [t1, t2, t3]; simp

/-- **Kang–Kashiwara, Lemma 4.2** (label `lem:van`, symmetry part): if `f e(𝐢) M = 0` and
`i_j = i_{j+1}`, then `(s_j f) e(𝐢) M = 0`. -/
theorem swap_smul_eq_zero (j : ℕ) (h : j + 1 < m) {i : Seq ν}
    (hi : i.lbl ⟨j, by omega⟩ = i.lbl ⟨j + 1, h⟩) {f : MvPolynomial (Fin m) k}
    (hf : ∀ v : M, (pol f * e i : KLRAlgebra k Q ν) • v = 0) (v : M) :
    (pol (swapPol j h f) * e i : KLRAlgebra k Q ν) • v = 0 := by
  have e1 : (pol (swapPol j h f) : KLRAlgebra k Q ν) = pol f -
      pol (MvPolynomial.X ⟨j, by omega⟩ - MvPolynomial.X ⟨j + 1, h⟩) * pol (dd k m j f) := by
    rw [pol_sub_mul_pol_dd j h f]; abel
  rw [e1, sub_mul, sub_smul, hf, mul_assoc, mul_smul, dd_smul_eq_zero j h hi hf, smul_zero,
    sub_zero]

/-- An element kills `M` as soon as all its products with the idempotents `e(𝐢)` do. -/
theorem smul_eq_zero_of_mul_e (r : KLRAlgebra k Q ν) (hr : ∀ (i : Seq ν) (v : M), (r * e i) • v = 0)
    (v : M) : r • v = 0 := by
  classical
  have : r = ∑ i, r * e i := by rw [← Finset.mul_sum, sum_e, mul_one]
  rw [this, Finset.sum_smul]
  exact Finset.sum_eq_zero fun i _ => hr i v

theorem rename_aeval_X {n n' : ℕ} (σ : Fin n → Fin n') (b : Fin n) (g : k[X]) :
    MvPolynomial.rename σ (aeval (MvPolynomial.X b : MvPolynomial (Fin n) k) g) =
      aeval (MvPolynomial.X (σ b)) g := by
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.rename_X]

/-- The annihilator of `e(𝐢) M` in the polynomial ring of the dots. -/
noncomputable def annE (M : Type*) [AddCommGroup M] [Module (KLRAlgebra k Q ν) M] (i : Seq ν) :
    Ideal (MvPolynomial (Fin m) k) where
  carrier := {p | ∀ v : M, (pol p * e i : KLRAlgebra k Q ν) • v = 0}
  add_mem' {p q} hp hq v := by rw [map_add, add_mul, add_smul, hp, hq, add_zero]
  zero_mem' v := by simp
  smul_mem' c p hp v := by rw [smul_eq_mul, map_mul, mul_assoc, mul_smul, hp, smul_zero]

/-- **Kang–Kashiwara, Lemma 4.3 (a)**, induction step (`eq:x12`): if the dot `x_b` satisfies a
monic polynomial on `M`, so does `x_{b+1}`. Here `Q_{ij}(u, v)` (`i ≠ j`) is assumed to have unit
leading coefficient as a polynomial in `v` (as in KK, where `t_{j,i;-a_{ji},0}` is a unit). -/
theorem exists_monic_next (hQ : ∀ i j : I, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff)
    (b : ℕ) (hb : b + 1 < m) (g : k[X]) (hg : g.Monic)
    (hgM : ∀ v : M, (pol (aeval (MvPolynomial.X ⟨b, by omega⟩) g) : KLRAlgebra k Q ν) • v = 0) :
    ∃ h : k[X], h.Monic ∧
      ∀ v : M, (pol (aeval (MvPolynomial.X ⟨b + 1, hb⟩) h) : KLRAlgebra k Q ν) • v = 0 := by
  classical
  have : Fintype (Seq ν) := Fintype.ofFinite _
  -- a monic `h_i` for each idempotent
  have hloc : ∀ i : Seq ν, ∃ h : k[X], h.Monic ∧
      aeval (MvPolynomial.X ⟨b + 1, hb⟩) h ∈ annE (Q := Q) M i := by
    intro i
    by_cases hi : i.lbl ⟨b, by omega⟩ = i.lbl ⟨b + 1, hb⟩
    · refine ⟨g, hg, fun v => ?_⟩
      have := swap_smul_eq_zero (Q := Q) (M := M) b hb hi
        (f := aeval (MvPolynomial.X ⟨b, by omega⟩) g)
        (fun v => by rw [mul_smul, hgM]) v
      rwa [swapPol, rename_aeval_X, swap_apply_left] at this
    · let ι : Fin 2 → Fin m := ![⟨b, by omega⟩, ⟨b + 1, hb⟩]
      let q : MvPolynomial (Fin 2) k :=
        aeval (MvPolynomial.X 1) g * Q (i.lbl ⟨b, by omega⟩) (i.lbl ⟨b + 1, hb⟩)
      have hq : IsUnit (polyInY q).leadingCoeff := by
        have h1 : polyInY (aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) g) =
            g.map (algebraMap k k[X]) := by
          rw [polyInY, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
          rfl
        rw [polyInY, map_mul, ← polyInY, h1, Polynomial.leadingCoeff_monic_mul (hg.map _)]
        exact hQ _ _ hi
      obtain ⟨h, hmon, hmem⟩ := exists_monic_mem_span g hg q hq
      refine ⟨h, hmon, ?_⟩
      have hle : Ideal.map (MvPolynomial.rename ι)
          (Ideal.span {aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) g, q}) ≤
          annE (Q := Q) M i := by
        rw [Ideal.map_span, Ideal.span_le]
        rintro _ ⟨p, hp, rfl⟩
        rcases hp with rfl | rfl
        · intro v
          rw [rename_aeval_X, mul_smul]
          exact hgM _
        · intro v
          -- `g(x_{b+1}) Q(x_b, x_{b+1}) e(𝐢) = g(x_{b+1}) ψ ψ e(𝐢) = ψ g(x_b) ψ e(𝐢)`
          have hQe : (pol (MvPolynomial.rename ι (Q (i.lbl ⟨b, by omega⟩) (i.lbl ⟨b + 1, hb⟩)))
              * e i : KLRAlgebra k Q ν) = ψ b * ψ b * e i := by
            rw [ψ_sq b hb i, ite_eq_right_of_eq_false _ _ (eq_false hi), ← ncEval_eq_pol]
            congr 2
            funext t; fin_cases t <;> rfl
          have hi' : ¬ (sadj m b • i).lbl ⟨b, by omega⟩ = (sadj m b • i).lbl ⟨b + 1, hb⟩ := by
            simp only [Seq.lbl, sadj_smul_apply]
            intro e; apply hi
            have e1 := sadj_apply_val hb ⟨b, by omega⟩
            have e2 := sadj_apply_val hb ⟨b + 1, hb⟩
            simp only [↓reduceIte, add_eq_left, one_ne_zero] at e1 e2
            rw [lbl_congr i (a := sadj m b ⟨b, by omega⟩) (b := ⟨b + 1, hb⟩) e1,
              lbl_congr i (a := sadj m b ⟨b + 1, hb⟩) (b := ⟨b, by omega⟩) (by simpa using e2)] at e
            exact e.symm
          have hc := ψ_mul_pol_mul_e (Q := Q) b hb (sadj m b • i)
            (aeval (MvPolynomial.X ⟨b, by omega⟩) g)
          rw [ite_eq_right_of_eq_false _ _ (eq_false hi'), add_zero, swapPol, rename_aeval_X, swap_apply_left] at hc
          have key : (pol (MvPolynomial.rename ι q) * e i : KLRAlgebra k Q ν) =
              ψ b * (pol (aeval (MvPolynomial.X ⟨b, by omega⟩) g) * (e (sadj m b • i) * ψ b)) := by
            rw [map_mul, map_mul, rename_aeval_X, mul_assoc, hQe]
            have : (ι 1) = ⟨b + 1, hb⟩ := rfl
            rw [this, ← mul_assoc, ← mul_assoc, mul_assoc _ (ψ b) (e i), ψ_mul_e, ← mul_assoc,
              ← hc]
            noncomm_ring
          rw [key, mul_smul, mul_smul, hgM, smul_zero]
      have h' := hle (Ideal.mem_map_of_mem _ hmem)
      rw [rename_aeval_X] at h'
      exact h'
  choose hs hmon hmem using hloc
  refine ⟨∏ i, hs i, Polynomial.monic_prod_of_monic _ _ fun i _ => hmon i, fun v => ?_⟩
  refine smul_eq_zero_of_mul_e _ (fun i v => ?_) v
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm (hs i), map_mul, map_mul,
    mul_assoc, mul_smul, hmem i v, smul_zero]

theorem pol_aeval_X (b : Fin m) (p : k[X]) :
    (pol (aeval (MvPolynomial.X b) p) : KLRAlgebra k Q ν) = aeval (x b) p := by
  rw [← Polynomial.aeval_algHom_apply, pol_X]

/-- **Kang–Kashiwara, Lemma 4.3 (a)**, first strand: on a module killed by the cyclotomic
elements, `x_1` satisfies the monic polynomial `∏_{i ∈ ν} a_i`. -/
theorem exists_monic_first (a : I → k[X]) (ha : ∀ i, (a i).Monic)
    (hM : ∀ (i : Seq ν) (v : M), cycElt Q a i • v = 0) (h0 : 0 < m) :
    ∃ g : k[X], g.Monic ∧
      ∀ v : M, (pol (aeval (MvPolynomial.X ⟨0, h0⟩) g) : KLRAlgebra k Q ν) • v = 0 := by
  classical
  refine ⟨∏ c ∈ ν.toFinset, a c, Polynomial.monic_prod_of_monic _ _ fun c _ => ha c,
    fun v => smul_eq_zero_of_mul_e _ (fun i v => ?_) v⟩
  have hmem : i.lbl ⟨0, h0⟩ ∈ ν.toFinset := Multiset.mem_toFinset.2 (i.mem _)
  rw [← Finset.mul_prod_erase _ _ hmem, mul_comm, map_mul, map_mul, mul_assoc, mul_smul,
    pol_aeval_X (Q := Q) ⟨0, h0⟩ (a _), ← cycElt_of_pos Q a i h0, hM, smul_zero]

/-- **Kang–Kashiwara, Lemma 4.3 (a)**: on a module over `R(ν)` killed by the cyclotomic elements,
all dots satisfy a common monic polynomial (for monic `a_i` and `Q_{ij}` with unit leading
coefficient in the second variable). -/
theorem exists_monic_dots (hQ : ∀ i j : I, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff)
    (a : I → k[X]) (ha : ∀ i, (a i).Monic)
    (hM : ∀ (i : Seq ν) (v : M), cycElt Q a i • v = 0) :
    ∃ g : k[X], g.Monic ∧
      ∀ (b : Fin m) (v : M), (pol (aeval (MvPolynomial.X b) g) : KLRAlgebra k Q ν) • v = 0 := by
  classical
  have step : ∀ (n : ℕ) (hn : n < m), ∃ g : k[X], g.Monic ∧
      ∀ v : M, (pol (aeval (MvPolynomial.X ⟨n, hn⟩) g) : KLRAlgebra k Q ν) • v = 0 := by
    intro n
    induction n with
    | zero => exact fun hn => exists_monic_first a ha hM hn
    | succ n ih =>
      intro hn
      obtain ⟨g, hg, hgM⟩ := ih (by omega)
      exact exists_monic_next hQ n hn g hg hgM
  choose gs hmon hgs using step
  refine ⟨∏ b : Fin m, gs b.1 b.2, Polynomial.monic_prod_of_monic _ _ fun b _ => hmon _ _,
    fun b v => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ b), mul_comm, map_mul, map_mul, mul_smul,
    hgs b.1 b.2 v, smul_zero]

end Module

end KLRAlgebra

open KLRAlgebra

namespace CycKLR

variable {a : I → k[X]}

/-- **Kang–Kashiwara, Lemma 4.3 (a)** for `R^Λ(ν)`: there is a monic polynomial `g` with
`g(x_b) = 0` in `R^Λ(ν)` for every strand `b`. -/
theorem exists_monic_dots (hQ : ∀ i j : I, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff)
    (ha : ∀ i, (a i).Monic) :
    ∃ g : k[X], g.Monic ∧ ∀ b : Fin (Multiset.card ν),
      mk k Q a ν (pol (aeval (MvPolynomial.X b) g)) = 0 := by
  let _ : Module (KLRAlgebra k Q ν) (CycKLR k Q a ν) := Module.compHom _ (mk k Q a ν).toRingHom
  obtain ⟨g, hg, hgM⟩ := KLRAlgebra.exists_monic_dots (M := CycKLR k Q a ν) hQ a ha
    (fun i v => show mk k Q a ν (cycElt Q a i) * v = 0 by rw [mk_cycElt, zero_mul])
  refine ⟨g, hg, fun b => ?_⟩
  have := hgM b 1
  rwa [show ∀ r : KLRAlgebra k Q ν, r • (1 : CycKLR k Q a ν) = mk k Q a ν r * 1 from
    fun _ => rfl, mul_one] at this

/-- **`R^Λ(ν)` is a finitely generated `k`-module** (Kang–Kashiwara, Corollary 4.4; from
Lemma 4.3 (a) and the spanning theorem `span_eq_top'`), for monic `a_i` and `Q_{ij}` with unit leading
coefficient in the second variable. -/
theorem module_finite (hQ : ∀ i j : I, i ≠ j → IsUnit (polyInY (Q i j)).leadingCoeff)
    (ha : ∀ i, (a i).Monic) : Module.Finite k (CycKLR k Q a ν) := by
  classical
  obtain ⟨g, hg, hgz⟩ := exists_monic_dots (ν := ν) hQ ha
  set n := Multiset.card ν
  let J : Ideal (MvPolynomial (Fin n) k) :=
    Ideal.span (Set.range fun b : Fin n => aeval (MvPolynomial.X b) g)
  -- the polynomial part is a finite `k`-module
  have hS : Module.Finite k (MvPolynomial (Fin n) k ⧸ J) := by
    have hint : ∀ y ∈ Set.range fun b : Fin n =>
        Ideal.Quotient.mkₐ k J (MvPolynomial.X b), IsIntegral k y := by
      rintro _ ⟨b, rfl⟩
      refine ⟨g, hg, ?_⟩
      rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨b, rfl⟩
    have hfin := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _) hint
    have htop : Algebra.adjoin k (Set.range fun b : Fin n =>
        Ideal.Quotient.mkₐ k J (MvPolynomial.X b)) = ⊤ := by
      rw [Set.range_comp' (Ideal.Quotient.mkₐ k J) MvPolynomial.X, ← AlgHom.map_adjoin,
        MvPolynomial.adjoin_range_X, Algebra.map_top, AlgHom.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective k J
    rw [htop] at hfin
    exact Module.Finite.equiv (Subalgebra.topEquiv.toLinearEquiv)
  let φ : (MvPolynomial (Fin n) k ⧸ J) →ₐ[k] CycKLR k Q a ν :=
    Ideal.Quotient.liftₐ J ((mk k Q a ν).comp pol) (by
      intro p hp
      have : J ≤ RingHom.ker ((mk k Q a ν).comp (pol (Q := Q) (ν := ν))).toRingHom := by
        rw [Ideal.span_le]
        rintro _ ⟨b, rfl⟩
        exact hgz b
      exact this hp)
  let T : Perm (Fin n) × Seq ν → CycKLR k Q a ν →ₗ[k] CycKLR k Q a ν := fun wi =>
    LinearMap.mulLeft k (mk k Q a ν (ψw ((fun w => (exists_reduced n w).choose) wi.1))) ∘ₗ
      LinearMap.mulRight k (mk k Q a ν (e wi.2))
  let N : Submodule k (CycKLR k Q a ν) :=
    ⨆ wi, (LinearMap.range φ.toLinearMap).map (T wi)
  have hN : N.FG := Submodule.fg_iSup _ fun wi =>
    ((Module.Finite.fg_top (R := k) (M := MvPolynomial (Fin n) k ⧸ J)).map _).map _ |>
      fun h => by rw [LinearMap.range_eq_map]; exact h
  refine ⟨?_⟩
  convert hN
  refine (eq_top_iff.2 ?_).symm
  have hspan := span_eq_top' (k := k) (Q := Q) (ν := ν) (fun w => (exists_reduced n w).choose)
    (fun w => (exists_reduced n w).choose_spec)
  intro r _
  obtain ⟨r, rfl⟩ := mk_surjective r
  have hr : r ∈ Submodule.span k _ := hspan ▸ Submodule.mem_top
  refine Submodule.span_induction (p := fun r _ => mk k Q a ν r ∈ N) ?_ ?_ ?_ ?_ hr
  · rintro _ ⟨w, u, i, rfl⟩
    refine Submodule.mem_iSup_of_mem (w, i) ⟨φ (Ideal.Quotient.mk J (MvPolynomial.monomial u 1)),
      ⟨Ideal.Quotient.mk J (MvPolynomial.monomial u 1), rfl⟩, ?_⟩
    simp only [T, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, map_mul, mul_assoc]
    rfl
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact N.add_mem hx hy
  · intro c x _ hx; rw [map_smul]; exact N.smul_mem c hx

end CycKLR

end Categorification.KLR
