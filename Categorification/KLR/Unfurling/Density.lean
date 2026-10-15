/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Density of coordinatewise polynomial substitutions

Let `k` be a field and, for each `t` in a finite set `T`, let `φ t : σ → k[x]` be a family of
one-variable polynomials whose linear coefficients are all nonzero. The substitution
`x_a ↦ (φ t a)(x_a)` is a `k`-algebra endomorphism `subst (φ t)` of `k[x_a : a ∈ σ]`; it sends the
point `p_t = ((φ t a).coeff 0)_a` to the origin. If the points `p_t` are pairwise distinct, then
for every truncation degree `D` and every family `g : T → k[x]` there is a single polynomial `f`
with `subst (φ t) f ≡ g t` modulo monomials of total degree `≥ D`, simultaneously for all `t`
(`exists_subst_coeff_sub_eq_zero`). Each `subst (φ t)` is moreover injective (`subst_injective`).

In other words, the joint substitution map is surjective onto the product over `t` of the
truncations of `k[x]` at the origin. This is the density statement in the proof of
Webster, arXiv:1603.06311v3, Lemma `lem:gamma-homo` (label; statement in §3.3): the image of the
polynomial part of the homomorphism `γ` is dense in the completed polynomial representation.

## Proof

* `orderIdeal n` is the ideal of polynomials all of whose monomials have total degree `≥ n`;
  `orderIdeal a * orderIdeal b ≤ orderIdeal (a + b)`.
* For one point: `subst φ (x_a - p_a) = x_a · w_a` with `w_a(0) = (φ a).coeff 1 ≠ 0`, so the image
  of `∏ (x_a - p_a)^{c_a}` is `x^c` times a polynomial with nonzero constant term. A downward
  induction on the total degree shows that every polynomial is congruent to an element of the
  image of `subst φ` modulo `orderIdeal D` (`exists_subst_sub_mem_orderIdeal`).
* `subst φ` maps the `D`-th power of the maximal ideal of `p` into `orderIdeal D`; the powers of
  the maximal ideals of distinct points are pairwise coprime, so the Chinese remainder theorem
  (`Ideal.exists_forall_sub_mem_ideal`) glues the local solutions.
* Injectivity: after the translation `x_a ↦ x_a + p_a`, `subst φ` becomes `x_a ↦ x_a · w_a`
  with `w_a(0) ≠ 0`, which keeps a monomial of minimal total degree with a nonzero coefficient.
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial

section OrderIdeal

variable {σ : Type*} {R : Type*} [CommSemiring R]

theorem coeff_mul_eq_zero_of_degree_lt {f g : MvPolynomial σ R} {a b : ℕ}
    (hf : ∀ c : σ →₀ ℕ, c.degree < a → f.coeff c = 0)
    (hg : ∀ c : σ →₀ ℕ, c.degree < b → g.coeff c = 0) (c : σ →₀ ℕ) (hc : c.degree < a + b) :
    (f * g).coeff c = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  have hdeg : x.1.degree + x.2.degree = c.degree := by rw [← map_add, hx]
  by_cases h1 : x.1.degree < a
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

variable (σ R) in
/-- The ideal of polynomials all of whose monomials have total degree at least `n`, i.e. the
`n`-th power of the ideal of the origin (`orderIdeal_one_pow_le` gives one inclusion). -/
def orderIdeal (n : ℕ) : Ideal (MvPolynomial σ R) where
  carrier := {f | ∀ c : σ →₀ ℕ, c.degree < n → f.coeff c = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun hf hg c hc => by simp [hf c hc, hg c hc]
  smul_mem' := fun r f hf c hc =>
    coeff_mul_eq_zero_of_degree_lt (a := 0) (fun _ h => absurd h (Nat.not_lt_zero _)) hf c
      (by omega)

theorem mem_orderIdeal {n : ℕ} {f : MvPolynomial σ R} :
    f ∈ orderIdeal σ R n ↔ ∀ c : σ →₀ ℕ, c.degree < n → f.coeff c = 0 := Iff.rfl

theorem orderIdeal_mul_le (a b : ℕ) :
    orderIdeal σ R a * orderIdeal σ R b ≤ orderIdeal σ R (a + b) :=
  Ideal.mul_le.2 fun _ hf _ hg => coeff_mul_eq_zero_of_degree_lt hf hg

theorem orderIdeal_anti {a b : ℕ} (h : a ≤ b) : orderIdeal σ R b ≤ orderIdeal σ R a :=
  fun _ hf c hc => hf c (lt_of_lt_of_le hc h)

theorem orderIdeal_one_pow_le (n : ℕ) : orderIdeal σ R 1 ^ n ≤ orderIdeal σ R n := by
  induction n with
  | zero => exact fun _ _ _ hc => absurd hc (Nat.not_lt_zero _)
  | succ n ih => rw [pow_succ]; exact (Ideal.mul_mono_left ih).trans (orderIdeal_mul_le n 1)

theorem monomial_mem_orderIdeal (c : σ →₀ ℕ) (r : R) :
    monomial c r ∈ orderIdeal σ R c.degree := by
  classical
  intro d hd
  rw [coeff_monomial, ite_eq_right_iff]
  rintro rfl
  exact absurd hd (lt_irrefl _)

theorem mem_orderIdeal_one_of_constantCoeff {f : MvPolynomial σ R} (hf : constantCoeff f = 0) :
    f ∈ orderIdeal σ R 1 := by
  intro c hc
  rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hc
  rw [hc, ← constantCoeff_eq, hf]

end OrderIdeal

variable {k : Type*} [Field k] {σ : Type*}

/-- The coordinatewise substitution `x_a ↦ (φ a)(x_a)`. -/
noncomputable def subst (φ : σ → Polynomial k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  aeval fun a => Polynomial.aeval (X a) (φ a)

/-- The maximal ideal of the point `p`. -/
noncomputable def pointIdeal (p : σ → k) : Ideal (MvPolynomial σ k) :=
  Ideal.span (Set.range fun a => X a - C (p a))

theorem subst_X_sub_C (φ : σ → Polynomial k) (a : σ) :
    subst φ (X a - C ((φ a).coeff 0)) = X a * Polynomial.aeval (X a) (φ a).divX := by
  have h := congrArg (Polynomial.aeval (R := k) (X a : MvPolynomial σ k))
    (Polynomial.X_mul_divX_add (φ a))
  simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, algebraMap_eq] at h
  simp only [subst, map_sub, aeval_X, aeval_C, algebraMap_eq]
  rw [← h]
  ring

theorem constantCoeff_aeval_X (a : σ) (q : Polynomial k) :
    constantCoeff (Polynomial.aeval (X a : MvPolynomial σ k) q) = q.coeff 0 := by
  simp [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_at_zero]

/-- `subst φ` sends `∏ (x_a - p_a)^{c_a}` to `x^c` times a polynomial with nonzero constant term. -/
theorem exists_subst_prod_eq_monomial_mul (φ : σ → Polynomial k)
    (hφ1 : ∀ a, (φ a).coeff 1 ≠ 0) (c : σ →₀ ℕ) :
    ∃ w : MvPolynomial σ k, constantCoeff w ≠ 0 ∧
      subst φ (c.prod fun a n => (X a - C ((φ a).coeff 0)) ^ n) = monomial c 1 * w := by
  refine ⟨c.prod fun a n => Polynomial.aeval (X a) (φ a).divX ^ n, ?_, ?_⟩
  · rw [Finsupp.prod, map_prod]
    refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
    rw [map_pow, constantCoeff_aeval_X, Polynomial.coeff_divX]
    exact pow_ne_zero _ (hφ1 a)
  · rw [map_finsuppProd, monomial_eq, C_1, one_mul, ← Finsupp.prod_mul]
    simp only [map_pow, subst_X_sub_C, mul_pow]

theorem monomial_mem_range_sup_orderIdeal (φ : σ → Polynomial k)
    (hφ1 : ∀ a, (φ a).coeff 1 ≠ 0) (c : σ →₀ ℕ) :
    ∃ q r, monomial c (1 : k) = subst φ q + r ∧ r ∈ orderIdeal σ k (c.degree + 1) := by
  obtain ⟨w, hw0, hw⟩ := exists_subst_prod_eq_monomial_mul φ hφ1 c
  set w0 := constantCoeff w
  refine ⟨C w0⁻¹ * c.prod fun a n => (X a - C ((φ a).coeff 0)) ^ n,
    -(monomial c 1 * (C w0⁻¹ * w - 1)), ?_, ?_⟩
  · rw [map_mul, hw, algHom_C, algebraMap_eq]
    ring
  · refine (Ideal.neg_mem_iff _).2 (orderIdeal_mul_le _ _ (Ideal.mul_mem_mul
      (monomial_mem_orderIdeal c 1) (mem_orderIdeal_one_of_constantCoeff ?_)))
    rw [map_sub, map_mul, constantCoeff_C, map_one, inv_mul_cancel₀ hw0, sub_self]

/-- Every polynomial is congruent to a substitution `subst φ h` modulo monomials of total degree
`≥ D`. -/
theorem exists_subst_sub_mem_orderIdeal (φ : σ → Polynomial k)
    (hφ1 : ∀ a, (φ a).coeff 1 ≠ 0) (D : ℕ) (g : MvPolynomial σ k) :
    ∃ h, subst φ h - g ∈ orderIdeal σ k D := by
  classical
  let M : Submodule k (MvPolynomial σ k) :=
    LinearMap.range (subst φ).toLinearMap ⊔ (orderIdeal σ k D).restrictScalars k
  -- an ideal `orderIdeal n` lies in `M` once all monomials of degree `≥ n` do
  have hM : ∀ n, (∀ d : σ →₀ ℕ, n ≤ d.degree → monomial d (1 : k) ∈ M) →
      ∀ f ∈ orderIdeal σ k n, f ∈ M := by
    intro n hn f hf
    rw [f.as_sum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hdn : n ≤ d.degree := by
      by_contra hlt
      exact (mem_support_iff.1 hd) (hf d (by omega))
    rw [show monomial d (f.coeff d) = f.coeff d • monomial d (1 : k) by
      rw [smul_monomial, smul_eq_mul, mul_one]]
    exact M.smul_mem _ (hn d hdn)
  have key : ∀ j, ∀ d : σ →₀ ℕ, D ≤ d.degree + j → monomial d (1 : k) ∈ M := by
    intro j
    induction j with
    | zero =>
      intro d hd
      exact Submodule.mem_sup_right (orderIdeal_anti hd (monomial_mem_orderIdeal d 1))
    | succ j ih =>
      intro d hd
      by_cases hd' : D ≤ d.degree + j
      · exact ih d hd'
      obtain ⟨q, r, hqr, hr⟩ := monomial_mem_range_sup_orderIdeal φ hφ1 d
      rw [hqr]
      refine M.add_mem (Submodule.mem_sup_left ⟨q, rfl⟩) (hM _ (fun d' hd'' => ih d' ?_) r hr)
      omega
  have hg : g ∈ M := hM 0 (fun d _ => key D d (by omega)) g (fun _ hc => absurd hc (by omega))
  obtain ⟨y, ⟨h, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 hg
  refine ⟨h, ?_⟩
  rw [← hyz, AlgHom.toLinearMap_apply, sub_add_cancel_left]
  exact (Ideal.neg_mem_iff _).2 hz

theorem map_subst_pointIdeal_pow_le (φ : σ → Polynomial k) (D : ℕ) :
    Ideal.map (subst φ) (pointIdeal fun a => (φ a).coeff 0) ^ D ≤ orderIdeal σ k D := by
  refine (Ideal.pow_right_mono ?_ D).trans (orderIdeal_one_pow_le D)
  rw [pointIdeal, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  refine mem_orderIdeal_one_of_constantCoeff ?_
  rw [subst_X_sub_C, map_mul, constantCoeff_X, zero_mul]

/-- The substitution `x_a ↦ x_a · w_a` is injective when every `w_a` has nonzero constant term:
a monomial of minimal total degree in the support of `g` survives with its coefficient scaled by
`∏ w_a(0)^{c_a}`. -/
theorem aeval_X_mul_eq_zero {w : σ → MvPolynomial σ k} (hw : ∀ a, constantCoeff (w a) ≠ 0)
    {g : MvPolynomial σ k} (hg : aeval (fun a => X a * w a) g = 0) : g = 0 := by
  classical
  by_contra hne
  obtain ⟨d, hd, hmin⟩ := g.support.exists_min_image Finsupp.degree (support_nonempty.2 hne)
  have hsum : aeval (fun a => X a * w a) g =
      ∑ c ∈ g.support, g.coeff c • (monomial c 1 * c.prod fun a n => w a ^ n) := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [aeval_monomial, monomial_eq, C_1, one_mul, ← Finsupp.prod_mul, algebraMap_eq,
      ← smul_eq_C_mul]
    simp only [mul_pow]
  have hcoeff := congrArg (fun p : MvPolynomial σ k => p.coeff d) hg
  simp only [hsum, coeff_sum, coeff_smul, coeff_monomial_mul', one_mul, smul_eq_mul] at hcoeff
  rw [Finset.sum_eq_single d] at hcoeff
  · simp only [le_refl, ↓reduceIte, tsub_self] at hcoeff
    rw [← constantCoeff_eq, Finsupp.prod, map_prod] at hcoeff
    refine mul_ne_zero (mem_support_iff.1 hd) (Finset.prod_ne_zero_iff.2 fun a _ => ?_) hcoeff
    rw [map_pow]
    exact pow_ne_zero _ (hw a)
  · intro c hc hcd
    split_ifs with hle
    · exfalso
      have h1 : c.degree ≤ d.degree := Finsupp.degree_mono hle
      have h2 : (d - c).degree = 0 := by
        have := hmin c hc
        have h3 : (d - c).degree + c.degree = d.degree := by rw [← map_add, tsub_add_cancel_of_le hle]
        omega
      rw [Finsupp.degree_eq_zero_iff, tsub_eq_zero_iff_le] at h2
      exact hcd (le_antisymm hle h2)
    · rw [mul_zero]
  · intro h; exact absurd hd h

/-- A coordinatewise substitution `x_a ↦ (φ a)(x_a)` with nonzero linear coefficients is
injective. -/
theorem subst_injective (φ : σ → Polynomial k) (hφ1 : ∀ a, (φ a).coeff 1 ≠ 0) :
    Function.Injective (subst φ) := by
  refine (injective_iff_map_eq_zero (subst φ)).2 fun f hf => ?_
  set p : σ → k := fun a => (φ a).coeff 0
  have hinv : (aeval fun a => X a - C (p a)).comp (aeval fun a => X a + C (p a)) =
      AlgHom.id k (MvPolynomial σ k) := by
    ext a
    simp
  have hf' : f = aeval (fun a => X a - C (p a)) (aeval (fun a => X a + C (p a)) f) := by
    rw [← AlgHom.comp_apply, hinv, AlgHom.id_apply]
  rw [hf', ← AlgHom.comp_apply, comp_aeval] at hf
  simp only [p, subst_X_sub_C] at hf
  have h0 := aeval_X_mul_eq_zero (fun a => ?_) hf
  · rw [hf', h0, map_zero]
  · rw [constantCoeff_aeval_X, Polynomial.coeff_divX]
    exact hφ1 a

theorem isCoprime_pointIdeal {p q : σ → k} (hpq : p ≠ q) :
    IsCoprime (pointIdeal p) (pointIdeal q) := by
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hpq
  rw [Ideal.isCoprime_iff_sup_eq]
  refine Ideal.eq_top_of_isUnit_mem _
    (Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨a, rfl⟩))
      (Ideal.mem_sup_left (Ideal.subset_span ⟨a, rfl⟩))) ?_
  rw [show X a - C (q a) - (X a - C (p a)) = C (p a - q a) by rw [map_sub]; ring]
  exact (sub_ne_zero.2 ha).isUnit.map C

/-- **Density of polynomial substitution.** For finitely many coordinatewise substitutions
`x_a ↦ (φ t a)(x_a)` with nonzero linear coefficients and pairwise distinct base points
`((φ t a).coeff 0)_a`, every family `g` of polynomials is matched, up to monomials of total
degree `≥ D`, by the substitutions of one polynomial `f`.

Webster, arXiv:1603.06311v3, proof of Lemma `lem:gamma-homo` (label): density of the image of
the polynomial part of `γ` in the completed polynomial representation. -/
theorem exists_subst_coeff_sub_eq_zero {T : Type*} [Finite T] (φ : T → σ → Polynomial k)
    (hφ1 : ∀ t a, (φ t a).coeff 1 ≠ 0) (hφ0 : Function.Injective fun t a => (φ t a).coeff 0)
    (D : ℕ) (g : T → MvPolynomial σ k) :
    ∃ f : MvPolynomial σ k, ∀ t, ∀ c : σ →₀ ℕ, c.degree < D →
      (subst (φ t) f - g t).coeff c = 0 := by
  choose h hh using fun t => exists_subst_sub_mem_orderIdeal (φ t) (hφ1 t) D (g t)
  obtain ⟨f, hf⟩ := Ideal.exists_forall_sub_mem_ideal
    (I := fun t => pointIdeal (fun a => (φ t a).coeff 0) ^ D)
    (fun s t hst => (isCoprime_pointIdeal fun he => hst (hφ0 he)).pow) h
  refine ⟨f, fun t => ?_⟩
  have h1 : subst (φ t) (f - h t) ∈ orderIdeal σ k D := by
    refine map_subst_pointIdeal_pow_le (φ t) D ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hf t)
  have : subst (φ t) f - g t = subst (φ t) (f - h t) + (subst (φ t) (h t) - g t) := by
    rw [map_sub]; ring
  rw [this]
  exact (orderIdeal σ k D).add_mem h1 (hh t)

end Categorification.KLR.Unfurling
