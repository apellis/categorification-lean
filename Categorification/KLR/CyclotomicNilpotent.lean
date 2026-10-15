/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.CyclotomicFinite
import Categorification.KLR.CyclotomicAction.Restriction
import Categorification.KLR.KL1

/-!
# Dots are nilpotent in undeformed cyclotomic KLR algebras

J. Brundan, A. Kleshchev, *Blocks of cyclotomic Hecke algebras and Khovanov–Lauda algebras*,
arXiv:0808.2032v3, §2.2, Lemma 2.1: in the cyclotomic quotient `R^Λ(ν)` with the undeformed
cyclotomic polynomials `a_j(y) = y^{Λ_j}`, every dot `x_b` is nilpotent.

Brundan–Kleshchev work over a field with the type `A` quiver polynomials
`Q_{ij}(u, v) ∈ {1, ±(v - u), (v - u)(u - v)}`. Here the base ring `k` is any commutative ring,
the index type `I` is arbitrary, and `Q` is any family with the following property: for `i ≠ j`,
`Q_{ij}(0, v) = c v^d` for a unit `c` and some `d` (`hQ0` below). This holds for KL I's `klQ`
(`klQ_eval_zero`), and for every weighted homogeneous `Q_{ij}` with positive dot degrees whose
pure `v`-power coefficient is a unit (the setting of Kang–Kashiwara, arXiv:1102.4677v4, §3.1).

The argument follows Brundan–Kleshchev's induction on the strand, carried out in the commutative
quotient of the polynomial ring of the dots by the annihilator of `e(𝐢) M`
(`KLRAlgebra.annE`). If `x_b^N` kills `M`, then for equal labels `i_b = i_{b+1}` so does
`x_{b+1}^N` (Kang–Kashiwara, Lemma 4.2, `KLRAlgebra.swap_smul_eq_zero`); for distinct labels,
`x_{b+1}^N Q_{i_b i_{b+1}}(x_b, x_{b+1}) e(𝐢) = ψ_b x_b^N ψ_b e(𝐢)` kills `M`, and writing
`Q(x, y) = c y^d + x r(x, y)` gives `(c y^{N+d})^N = (-x y^N r)^N = 0` modulo the annihilator, so
`x_{b+1}^{N(N+d)} e(𝐢)` kills `M`.

Positions are zero-indexed: the paper's `y_1` is `x 0`.

## Main results

* `pow_eq_zero_of_pow_mul_eq_zero`: in a commutative ring, `x^N = 0` and
  `y^N (c y^d + x r) = 0` with `c` a unit give `y^{N(N+d)} = 0`;
* `KLRAlgebra.exists_pow_dots` (Brundan–Kleshchev, Lemma 2.1, on modules): on an `R(ν)`-module
  killed by the cyclotomic elements for `a_j = X^{Λ_j}`, a common power of all dots acts by zero;
* `CycKLR.x_zero_pow_eq_zero`: `x_1^N = 0` in `R^Λ(ν)` for `N = max_{j ∈ ν} Λ_j`;
* `CycKLR.exists_pow_x_eq_zero` (Brundan–Kleshchev, Lemma 2.1): `x_b^N = 0` in `R^Λ(ν)` for
  all strands `b`, for some `N` depending only on `ν`, `Λ` and `Q`;
* `CyclotomicAction.dot_pow_eq_zero`, `CyclotomicAction.dotA_hom_pow_eq_zero`: the dot on
  cyclotomic induction `F_i : R^Λ(β)-mod → R^Λ(δ)-mod` is nilpotent.
-/

namespace Categorification.KLR

open Polynomial Equiv NilHecke TypeA

variable {I : Type*} [DecidableEq I] {k : Type*} [CommRing k]

/-- In a commutative ring, `x^N = 0` and `y^N (c y^d + x r) = 0` with `c` a unit give
`y^{N(N+d)} = 0`. -/
theorem pow_eq_zero_of_pow_mul_eq_zero {A : Type*} [CommRing A] {x y c r : A} (hc : IsUnit c)
    {N d : ℕ} (hx : x ^ N = 0) (hy : y ^ N * (c * y ^ d + x * r) = 0) :
    y ^ (N * (N + d)) = 0 := by
  have h1 : c * y ^ (N + d) = -(x * (y ^ N * r)) := by
    rw [pow_add]; linear_combination hy
  have h2 : c ^ N * y ^ (N * (N + d)) = 0 := by
    calc c ^ N * y ^ (N * (N + d)) = (c * y ^ (N + d)) ^ N := by
          rw [mul_pow, ← pow_mul, mul_comm (N + d)]
      _ = (-(x * (y ^ N * r))) ^ N := by rw [h1]
      _ = 0 := by rw [neg_pow, mul_pow, hx]; ring
  exact (hc.pow N).mul_right_eq_zero.mp h2

/-- Every `q(x, y)` is `q(0, y) + x r(x, y)`. -/
theorem exists_eq_eval_zero_add (q : MvPolynomial (Fin 2) k) :
    ∃ r : MvPolynomial (Fin 2) k,
      q = MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) q +
        MvPolynomial.X 0 * r := by
  set J : Ideal (MvPolynomial (Fin 2) k) := Ideal.span {MvPolynomial.X 0}
  let π := Ideal.Quotient.mkₐ k J
  have hπ : π.comp (MvPolynomial.aeval (![0, MvPolynomial.X 1] :
      Fin 2 → MvPolynomial (Fin 2) k)) = π := by
    refine MvPolynomial.algHom_ext fun t => ?_
    fin_cases t
    · simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
      change π 0 = π (MvPolynomial.X 0)
      rw [map_zero, Ideal.Quotient.mkₐ_eq_mk, eq_comm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    · simp
  have hmem : q - MvPolynomial.aeval (![0, MvPolynomial.X 1] :
      Fin 2 → MvPolynomial (Fin 2) k) q ∈ J := by
    have hq := (DFunLike.congr_fun hπ q).symm
    exact Ideal.Quotient.eq.mp (by simpa [π, Ideal.Quotient.mkₐ_eq_mk] using hq)
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hmem
  exact ⟨r, by rw [← hr]; ring⟩

omit [DecidableEq I] in
/-- KL I's polynomials `klQ` satisfy the hypothesis of this file: `Q_{ij}(0, v)` is `v` or `1`. -/
theorem klQ_eval_zero (Γ : SimpleGraph I) [DecidableRel Γ.Adj] (i j : I) :
    ∃ (c : k) (d : ℕ), IsUnit c ∧
      MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k)
        (klQ (k := k) Γ i j) = MvPolynomial.C c * MvPolynomial.X 1 ^ d := by
  by_cases h : Γ.Adj i j
  · exact ⟨1, 1, isUnit_one, by simp [klQ, h]⟩
  · exact ⟨1, 0, isUnit_one, by simp [klQ, h]⟩

namespace KLRAlgebra

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

local notation "m" => Multiset.card ν

section Module

variable {M : Type*} [AddCommGroup M] [Module (KLRAlgebra k Q ν) M]

theorem mem_annE {i : Seq ν} {p : MvPolynomial (Fin m) k} :
    p ∈ annE (Q := Q) M i ↔ ∀ v : M, (pol p * e i : KLRAlgebra k Q ν) • v = 0 := Iff.rfl

/-- For distinct labels `i_b ≠ i_{b+1}`:
`g(x_{b+1}) Q_{i_b i_{b+1}}(x_b, x_{b+1}) e(𝐢) = ψ_b g(x_b) e(s_b 𝐢) ψ_b`. -/
theorem pol_rename_mul_e_eq (b : ℕ) (hb : b + 1 < m) (i : Seq ν)
    (hi : ¬ i.lbl ⟨b, by omega⟩ = i.lbl ⟨b + 1, hb⟩) (g : k[X]) :
    (pol (MvPolynomial.rename ![(⟨b, by omega⟩ : Fin m), ⟨b + 1, hb⟩]
        (aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) g *
          Q (i.lbl ⟨b, by omega⟩) (i.lbl ⟨b + 1, hb⟩))) * e i : KLRAlgebra k Q ν) =
      ψ b * (pol (aeval (MvPolynomial.X ⟨b, by omega⟩) g) * (e (sadj m b • i) * ψ b)) := by
  let ι : Fin 2 → Fin m := ![⟨b, by omega⟩, ⟨b + 1, hb⟩]
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
  rw [ite_eq_right_of_eq_false _ _ (eq_false hi'), add_zero, swapPol, rename_aeval_X,
    swap_apply_left] at hc
  change (pol (MvPolynomial.rename ι _) * e i : KLRAlgebra k Q ν) = _
  rw [map_mul, map_mul, rename_aeval_X, mul_assoc, hQe]
  have : (ι 1) = ⟨b + 1, hb⟩ := rfl
  rw [this, ← mul_assoc, ← mul_assoc, mul_assoc _ (ψ b) (e i), ψ_mul_e, ← mul_assoc, ← hc]
  noncomm_ring

/-- **Brundan–Kleshchev, Lemma 2.1**, induction step: if `x_b^N` kills `M`, then a power of
`x_{b+1}` kills `M`, provided `Q_{ij}(0, v)` is a unit multiple of a power of `v` for `i ≠ j`. -/
theorem exists_pow_next
    (hQ0 : ∀ i j : I, i ≠ j → ∃ (c : k) (d : ℕ), IsUnit c ∧
      MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q i j) =
        MvPolynomial.C c * MvPolynomial.X 1 ^ d)
    (b : ℕ) (hb : b + 1 < m) (N : ℕ)
    (hN : ∀ v : M, (pol (MvPolynomial.X ⟨b, by omega⟩ ^ N) : KLRAlgebra k Q ν) • v = 0) :
    ∃ N' : ℕ, ∀ v : M, (pol (MvPolynomial.X ⟨b + 1, hb⟩ ^ N') : KLRAlgebra k Q ν) • v = 0 := by
  classical
  have : Fintype (Seq ν) := Fintype.ofFinite _
  have hloc : ∀ i : Seq ν, ∃ n : ℕ,
      (MvPolynomial.X ⟨b + 1, hb⟩ : MvPolynomial (Fin m) k) ^ n ∈ annE (Q := Q) M i := by
    intro i
    by_cases hi : i.lbl ⟨b, by omega⟩ = i.lbl ⟨b + 1, hb⟩
    · refine ⟨N, fun v => ?_⟩
      have := swap_smul_eq_zero (Q := Q) (M := M) b hb hi
        (f := MvPolynomial.X ⟨b, by omega⟩ ^ N) (fun v => by rw [mul_smul, hN]) v
      rwa [swapPol, map_pow, MvPolynomial.rename_X, swap_apply_left] at this
    · obtain ⟨c, d, hc, hQc⟩ := hQ0 _ _ hi
      obtain ⟨r, hr⟩ := exists_eq_eval_zero_add (Q (i.lbl ⟨b, by omega⟩) (i.lbl ⟨b + 1, hb⟩))
      rw [hQc] at hr
      let ι : Fin 2 → Fin m := ![⟨b, by omega⟩, ⟨b + 1, hb⟩]
      set J := annE (Q := Q) M i
      let π := Ideal.Quotient.mk J
      have hπ : ∀ p, p ∈ J ↔ π p = 0 := fun p => Ideal.Quotient.eq_zero_iff_mem.symm
      have hx : π (MvPolynomial.X ⟨b, by omega⟩) ^ N = 0 := by
        rw [← map_pow, ← hπ]
        intro v
        rw [mul_smul, hN]
      have hkey := pol_rename_mul_e_eq (Q := Q) b hb i hi (Polynomial.X ^ N : k[X])
      have hy : π (MvPolynomial.X ⟨b + 1, hb⟩) ^ N *
          (π (MvPolynomial.C c : MvPolynomial (Fin m) k) * π (MvPolynomial.X ⟨b + 1, hb⟩) ^ d +
            π (MvPolynomial.X ⟨b, by omega⟩) * π (MvPolynomial.rename ι r)) = 0 := by
        have hmem : MvPolynomial.rename ι (aeval (MvPolynomial.X 1 : MvPolynomial (Fin 2) k)
            (Polynomial.X ^ N : k[X]) * Q (i.lbl ⟨b, by omega⟩) (i.lbl ⟨b + 1, hb⟩)) ∈ J := by
          intro v
          rw [hkey, mul_smul, mul_smul, map_pow, aeval_X, hN, smul_zero]
        rw [hπ, map_mul, map_pow, aeval_X, hr] at hmem
        simpa [ι, map_mul, map_add, map_pow, MvPolynomial.rename_X] using hmem
      refine ⟨N * (N + d), (hπ _).2 ?_⟩
      rw [map_pow]
      exact pow_eq_zero_of_pow_mul_eq_zero ((hc.map (MvPolynomial.C (σ := Fin m) (R := k))).map π) hx hy
  choose ns hns using hloc
  refine ⟨Finset.univ.sup ns, fun v => smul_eq_zero_of_mul_e _ (fun i v => ?_) v⟩
  have hle : ns i ≤ Finset.univ.sup ns := Finset.le_sup (Finset.mem_univ i)
  have : (MvPolynomial.X ⟨b + 1, hb⟩ : MvPolynomial (Fin m) k) ^ Finset.univ.sup ns ∈
      annE (Q := Q) M i := by
    rw [← Nat.sub_add_cancel hle, pow_add]
    exact Ideal.mul_mem_left _ _ (hns i)
  exact this v

/-- **Brundan–Kleshchev, Lemma 2.1**, first strand: on a module killed by the cyclotomic elements
for `a_j = X^{Λ_j}`, `x_1^N` acts by zero for `N = max_{j ∈ ν} Λ_j`. -/
theorem pow_x_zero_smul (Λ : I → ℕ)
    (hM : ∀ (i : Seq ν) (v : M), cycElt Q (fun j => X ^ Λ j) i • v = 0) (h0 : 0 < m) (v : M) :
    (pol (MvPolynomial.X ⟨0, h0⟩ ^ ν.toFinset.sup Λ) : KLRAlgebra k Q ν) • v = 0 := by
  classical
  refine smul_eq_zero_of_mul_e _ (fun i v => ?_) v
  have hmem : i.lbl ⟨0, h0⟩ ∈ ν.toFinset := Multiset.mem_toFinset.2 (i.mem _)
  have hle : Λ (i.lbl ⟨0, h0⟩) ≤ ν.toFinset.sup Λ := Finset.le_sup hmem
  have hcyc := cycElt_of_pos Q (fun j => X ^ Λ j) i h0
  simp only [map_pow, aeval_X] at hcyc
  rw [map_pow, pol_X, ← Nat.sub_add_cancel hle, pow_add, mul_assoc, ← hcyc, mul_smul, hM,
    smul_zero]

/-- **Brundan–Kleshchev, Lemma 2.1** (arXiv:0808.2032v3), on modules: on an `R(ν)`-module killed
by the cyclotomic elements for `a_j = X^{Λ_j}`, some common power `x_b^N` of all dots acts by
zero, provided `Q_{ij}(0, v)` is a unit multiple of a power of `v` for `i ≠ j`. -/
theorem exists_pow_dots
    (hQ0 : ∀ i j : I, i ≠ j → ∃ (c : k) (d : ℕ), IsUnit c ∧
      MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q i j) =
        MvPolynomial.C c * MvPolynomial.X 1 ^ d)
    (Λ : I → ℕ) (hM : ∀ (i : Seq ν) (v : M), cycElt Q (fun j => X ^ Λ j) i • v = 0) :
    ∃ N : ℕ, ∀ (b : Fin m) (v : M), (pol (MvPolynomial.X b ^ N) : KLRAlgebra k Q ν) • v = 0 := by
  classical
  have step : ∀ (n : ℕ) (hn : n < m), ∃ N : ℕ,
      ∀ v : M, (pol (MvPolynomial.X ⟨n, hn⟩ ^ N) : KLRAlgebra k Q ν) • v = 0 := by
    intro n
    induction n with
    | zero => exact fun hn => ⟨_, pow_x_zero_smul Λ hM hn⟩
    | succ n ih =>
      intro hn
      obtain ⟨N, hN⟩ := ih (by omega)
      exact exists_pow_next hQ0 n hn N hN
  choose Ns hNs using step
  refine ⟨Finset.univ.sup fun b : Fin m => Ns b.1 b.2, fun b v => ?_⟩
  have hle : Ns b.1 b.2 ≤ Finset.univ.sup fun b : Fin m => Ns b.1 b.2 :=
    Finset.le_sup (f := fun b : Fin m => Ns b.1 b.2) (Finset.mem_univ b)
  rw [← Nat.sub_add_cancel hle, pow_add, map_mul, mul_smul, hNs b.1 b.2, smul_zero]

end Module

end KLRAlgebra

open KLRAlgebra

namespace CycKLR

variable {Q : I → I → MvPolynomial (Fin 2) k} {ν : Multiset I}

/-- **Brundan–Kleshchev, Lemma 2.1**, first strand: `x_1^N = 0` in `R^Λ(ν)` for
`a_j = X^{Λ_j}` and `N = max_{j ∈ ν} Λ_j`. Any commutative ring and any `Q`. -/
theorem x_zero_pow_eq_zero (Λ : I → ℕ) (h0 : 0 < Multiset.card ν) :
    (mk k Q (fun j => X ^ Λ j) ν (x ⟨0, h0⟩)) ^ ν.toFinset.sup Λ = 0 := by
  let _ : Module (KLRAlgebra k Q ν) (CycKLR k Q (fun j => X ^ Λ j) ν) :=
    Module.compHom _ (mk k Q (fun j => X ^ Λ j) ν).toRingHom
  have := pow_x_zero_smul (Q := Q) (M := CycKLR k Q (fun j => X ^ Λ j) ν) Λ
    (fun i v => show mk k Q _ ν (cycElt Q _ i) * v = 0 by rw [mk_cycElt, zero_mul]) h0 1
  change mk k Q _ ν _ * 1 = 0 at this
  rwa [mul_one, map_pow, pol_X, map_pow] at this

/-- **Brundan–Kleshchev, Lemma 2.1** (arXiv:0808.2032v3): in the undeformed cyclotomic quotient
`R^Λ(ν)` (`a_j = X^{Λ_j}`), every dot is nilpotent, with a common exponent `N` depending only
on `ν`, `Λ` and `Q`. Any commutative ring `k`; for `i ≠ j`, `Q_{ij}(0, v)` is a unit multiple
of a power of `v` (for instance `klQ`, see `klQ_eval_zero`). -/
theorem exists_pow_x_eq_zero
    (hQ0 : ∀ i j : I, i ≠ j → ∃ (c : k) (d : ℕ), IsUnit c ∧
      MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q i j) =
        MvPolynomial.C c * MvPolynomial.X 1 ^ d)
    (Λ : I → ℕ) :
    ∃ N : ℕ, ∀ b : Fin (Multiset.card ν), (mk k Q (fun j => X ^ Λ j) ν (x b)) ^ N = 0 := by
  let _ : Module (KLRAlgebra k Q ν) (CycKLR k Q (fun j => X ^ Λ j) ν) :=
    Module.compHom _ (mk k Q (fun j => X ^ Λ j) ν).toRingHom
  obtain ⟨N, hN⟩ := exists_pow_dots (Q := Q) (M := CycKLR k Q (fun j => X ^ Λ j) ν) hQ0 Λ
    (fun i v => show mk k Q _ ν (cycElt Q _ i) * v = 0 by rw [mk_cycElt, zero_mul])
  refine ⟨N, fun b => ?_⟩
  have := hN b 1
  change mk k Q _ ν _ * 1 = 0 at this
  rwa [mul_one, map_pow, pol_X, map_pow] at this

end CycKLR

namespace CyclotomicAction

open CategoryTheory

universe u v w

variable {I : Type u} [DecidableEq I] {k : Type v} [CommRing k]
  {Q : I → I → MvPolynomial (Fin 2) k}

/-- Powers of the dot on cyclotomic induction are the element transformations of the powers of
the last dot. -/
theorem dot_pow_succ (a : I → k[X]) (i : I) {β δ : Multiset I} (h : {i} + β = δ) (n : ℕ) :
    ∃ hx : InductionAlong.Intertwines (lastEmb Q a i h) (lastEmb Q a i h)
        (dotElt Q a i h ^ (n + 1)),
      End.of (dot.{u, v, w} Q a i h) ^ (n + 1) =
        InductionAlong.natTrans hx := by
  induction n with
  | zero =>
    refine ⟨by rw [pow_one]; exact intertwines_dotElt Q a i h, ?_⟩
    rw [pow_one]
    exact InductionAlong.natTrans_congr _ (pow_one _).symm
  | succ n ih =>
    obtain ⟨hx, hpow⟩ := ih
    refine ⟨by rw [pow_succ']; exact (intertwines_dotElt Q a i h).mul hx, ?_⟩
    rw [pow_succ, hpow, End.mul_def]
    change InductionAlong.natTrans (intertwines_dotElt Q a i h) ≫ InductionAlong.natTrans hx = _
    rw [InductionAlong.natTrans_comp]
    exact InductionAlong.natTrans_congr _ (pow_succ' _ _).symm

/-- **The dot on cyclotomic induction is nilpotent** (Brundan–Kleshchev, arXiv:0808.2032v3,
Lemma 2.1, applied to the last dot of `R^Λ(δ)`): for `a_j = X^{Λ_j}` and `Q_{ij}(0, v)` a unit
multiple of a power of `v` (`i ≠ j`), some power of `dot : F_i ⟶ F_i` vanishes. -/
theorem dot_pow_eq_zero
    (hQ0 : ∀ i j : I, i ≠ j → ∃ (c : k) (d : ℕ), IsUnit c ∧
      MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q i j) =
        MvPolynomial.C c * MvPolynomial.X 1 ^ d)
    (Λ : I → ℕ) (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    ∃ N : ℕ, End.of (dot.{u, v, w} Q (fun j => X ^ Λ j) i h) ^ N = 0 := by
  obtain ⟨N, hN⟩ := CycKLR.exists_pow_x_eq_zero (ν := δ) hQ0 Λ
  obtain ⟨hx, hpow⟩ := dot_pow_succ.{u, v, w} (Q := Q) (fun j => X ^ Λ j) i h N
  have hz : dotElt Q (fun j => X ^ Λ j) i h ^ (N + 1) = 0 := by
    rw [pow_succ, dotElt, hN, zero_mul]
  refine ⟨N + 1, ?_⟩
  rw [hpow, InductionAlong.natTrans_congr hx hz, InductionAlong.natTrans_zero]

/-- The dot 2-cell `dotA` of `TwoRep.AdditiveCat` is nilpotent (`dot_pow_eq_zero`). -/
theorem dotA_hom_pow_eq_zero
    (hQ0 : ∀ i j : I, i ≠ j → ∃ (c : k) (d : ℕ), IsUnit c ∧
      MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) k) (Q i j) =
        MvPolynomial.C c * MvPolynomial.X 1 ^ d)
    (Λ : I → ℕ) (i : I) {β δ : Multiset I} (h : {i} + β = δ) :
    ∃ N : ℕ, End.of (dotA.{u, v, w} Q (fun j => X ^ Λ j) i h).hom ^ N = 0 := by
  rw [dotA_hom]
  exact dot_pow_eq_zero hQ0 Λ i h

end CyclotomicAction

end Categorification.KLR
