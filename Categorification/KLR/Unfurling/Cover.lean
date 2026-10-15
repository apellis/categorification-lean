/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# The unfurled index set and the factorization of `P_{ij}`

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, §3.3, attaches to
a KLR datum on `I` and a choice of spectra `U_i` (finite sets of nonzero scalars) the unfurled
index set `Ĩ` of pairs `(i, u)` with `u ∈ U_i` (definition with LaTeX label `def:tilde-I`).
After the substitution `x ↦ u (1 + x)^{d_i}`, the polynomials `P_{ij}` factor as a power of the
difference of the two variables times a unit of the power series ring (equation with label
`eq:factorize`); the exponent is the number of arrows between the two vertices of `Ĩ`.

Webster works over an algebraically closed field and reads the exponent off the roots of
`P_{ij}`. Here the factorization is proved over any field, by dehomogenization: a weighted
homogeneous `F(x, y)` of weights `(e₁, e₂)` and degree `D` satisfies
`F(u s^{e₁}, u' t^{e₂}) = t^D f(s / t)` for the one-variable polynomial
`f(r) = F(u r^{e₁}, u')`, and the factor `(s - t)^n` comes from the multiplicity `n` of `1` as
a root of `f`. No invertibility of `lcm(d_i, d_j)` is needed for the factorization; the
invertibility of `d_i` is used only for the linear coefficient of `ϖ_{(i,u)}`.

## Main definitions and results

* `KLR.Unfurling.UnfurlingDatum` : a map `π : J → I` with power series `ϖ_j` (polynomials here)
  and the factorization of `P` after substitution.
* `KLR.Unfurling.exists_aeval_eq_pow_mul` : the factorization for a weighted homogeneous
  polynomial (natural weights); `KLR.Unfurling.exists_aeval_eq_pow_mul_of_int` for integer
  weights `(c e₁, c e₂)`, `c > 0`, as in KLR gradings.
* `KLR.Unfurling.eq_of_pow_mul_eq_pow_mul` : the exponent is unique (order of vanishing).
* `KLR.Unfurling.UnfurlingDatum.ofSpectra` : the datum on `Σ i, U i`.

## Argument order

In this library `P a b (u, v)` has its first variable on a `b`-strand (see the polynomial
representation, `KLR.PolyRep`). Accordingly the factorization field of `UnfurlingDatum`
substitutes `ϖ_j` into the first variable of `P (π j') (π j)` and `ϖ_{j'}` into the second.
-/

open MvPolynomial

namespace Categorification.KLR.Unfurling

/-- The unfurling datum (Webster, arXiv:1603.06311v3, §3.3, around the equation with label
`eq:factorize`, and the definition with label `def:tilde-I`): a map `π : J → I`, for each `j`
a series `ϖ_j(z)` (here a polynomial) with nonzero linear coefficient, whose constant terms
separate the points of each fibre of `π`, and for `π j ≠ π j'` a factorization
`P_{π j', π j}(ϖ_j(x), ϖ_{j'}(y)) = (x - y)^{a_{jj'}} · P°_{jj'}(x, y)` with `P°_{jj'}(0,0) ≠ 0`.
The first variable of `P a b` sits on a `b`-strand, whence the order `P (π j') (π j)`. -/
structure UnfurlingDatum {I : Type*} (k : Type*) [Field k]
    (P : I → I → MvPolynomial (Fin 2) k) (J : Type*) where
  /-- The projection `J → I`. -/
  π : J → I
  /-- The series `ϖ_j(z)`. -/
  pw : J → Polynomial k
  pw_coeff_one : ∀ j, (pw j).coeff 1 ≠ 0
  pw_coeff_zero_inj : ∀ j j', π j = π j' → (pw j).coeff 0 = (pw j').coeff 0 → j = j'
  /-- The number of arrows `a_{jj'}`: the order of vanishing along the diagonal. -/
  arrows : J → J → ℕ
  arrows_of_eq : ∀ j j', π j = π j' → arrows j j' = 0
  /-- The unit factor `P°_{jj'}`. -/
  unit : J → J → MvPolynomial (Fin 2) k
  unit_constantCoeff : ∀ j j', π j ≠ π j' → constantCoeff (unit j j') ≠ 0
  factor : ∀ j j', π j ≠ π j' →
    aeval ![Polynomial.aeval (X 0) (pw j), Polynomial.aeval (X 1) (pw j')] (P (π j') (π j))
      = (X 0 - X 1) ^ arrows j j' * unit j j'

variable {k : Type*} [Field k]

private lemma weight_fin_two {M : Type*} [AddCommMonoid M] (w : Fin 2 → M) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight w d = d 0 • w 0 + d 1 • w 1 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]

private lemma one_add_X_ne_zero (i : Fin 2) : (1 + X i : MvPolynomial (Fin 2) k) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  simp at this

/-- Factorization (Webster, arXiv:1603.06311v3, §3.3, equation with label `eq:factorize`, in
the form used for the unfurled index set): if `F ≠ 0` is weighted homogeneous for positive
weights `(e₁, e₂)` and `u, u' ≠ 0`, then `F(u (1 + x)^{e₁}, u' (1 + y)^{e₂})` is
`(x - y)^n · G` with `G(0, 0) ≠ 0`. Valid over any field. -/
theorem exists_aeval_eq_pow_mul {e₁ e₂ D : ℕ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    {F : MvPolynomial (Fin 2) k} (hF : F ≠ 0) (hhom : F.IsWeightedHomogeneous ![e₁, e₂] D)
    {u u' : k} (hu : u ≠ 0) (hu' : u' ≠ 0) :
    ∃ (n : ℕ) (G : MvPolynomial (Fin 2) k),
      aeval ![C u * (1 + X 0) ^ e₁, C u' * (1 + X 1) ^ e₂] F = (X 0 - X 1) ^ n * G ∧
        constantCoeff G ≠ 0 := by
  classical
  have hD : ∀ d ∈ F.support, d 0 * e₁ + d 1 * e₂ = D := fun d hd => by
    have := hhom (mem_support_iff.mp hd)
    simpa [weight_fin_two] using this
  -- the dehomogenized one-variable polynomial `f(r) = F(u r^{e₁}, u')`
  set f : Polynomial k := ∑ d ∈ F.support,
    Polynomial.monomial (e₁ * d 0) (F.coeff d * u ^ d 0 * u' ^ d 1) with hfdef
  have hf0 : f ≠ 0 := by
    obtain ⟨d, hd⟩ : F.support.Nonempty := by
      rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    intro h
    have hc := congrArg (fun p => Polynomial.coeff p (e₁ * d 0)) h
    simp only [hfdef, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single d] at hc
    · simp only [ite_true] at hc
      exact mul_ne_zero (mul_ne_zero (mem_support_iff.mp hd) (pow_ne_zero _ hu))
        (pow_ne_zero _ hu') hc
    · intro d' hd' hne
      rw [ite_eq_right_iff]
      intro heq
      exfalso
      apply hne
      have h0 : d' 0 = d 0 := Nat.eq_of_mul_eq_mul_left he₁ heq
      have h1 : d' 1 = d 1 := by
        have a := hD d hd; have b := hD d' hd'
        rw [h0] at b
        exact Nat.eq_of_mul_eq_mul_right he₂ (by omega)
      ext i; fin_cases i <;> simp [h0, h1]
    · intro h; exact absurd hd h
  have hfdeg : f.natDegree ≤ D := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    refine (Polynomial.natDegree_monomial_le _).trans ?_
    have := hD d hd
    nlinarith
  -- factor out the root `1`
  set n := f.rootMultiplicity 1
  set g := f /ₘ (Polynomial.X - Polynomial.C 1) ^ n
  have hfg : (Polynomial.X - Polynomial.C 1) ^ n * g = f :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq f 1
  have hg1 : g.eval 1 ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 1 hf0
  have hg0 : g ≠ 0 := by rintro h; simp [h] at hg1
  have hdeg : n + g.natDegree = f.natDegree := by
    have := congrArg Polynomial.natDegree hfg
    rwa [((Polynomial.monic_X_sub_C (1 : k)).pow n).natDegree_mul' hg0,
      (Polynomial.monic_X_sub_C (1 : k)).natDegree_pow, Polynomial.natDegree_X_sub_C,
      mul_one] at this
  have hgdeg : g.natDegree ≤ D - n := by omega
  have hn : n ≤ D := by omega
  set G : MvPolynomial (Fin 2) k := ∑ i ∈ Finset.range (g.natDegree + 1),
    C (g.coeff i) * (1 + X 0) ^ i * (1 + X 1) ^ (D - n - i) with hGdef
  refine ⟨n, G, ?_, ?_⟩
  swap
  · simp only [hGdef, map_sum, map_mul, map_pow, map_add, map_one, constantCoeff_C,
      constantCoeff_X, add_zero, one_pow, mul_one]
    rw [Polynomial.eval_eq_sum_range] at hg1
    simpa using hg1
  -- compare in the fraction field, where `1 + X 1` is invertible
  let K := FractionRing (MvPolynomial (Fin 2) k)
  let φ : MvPolynomial (Fin 2) k →+* K := algebraMap _ K
  have hφ : Function.Injective φ := IsFractionRing.injective _ K
  let ψ : k →+* K := φ.comp C
  set τ : K := φ (1 + X 1) with hτdef
  have hτ : τ ≠ 0 := (map_ne_zero_iff φ hφ).mpr (one_add_X_ne_zero 1)
  set ρ : K := φ (1 + X 0) / τ with hρdef
  have hσ : φ (1 + X 0) = ρ * τ := (div_mul_cancel₀ _ hτ).symm
  clear_value ρ τ
  apply hφ
  have hL : φ (aeval ![C u * (1 + X 0) ^ e₁, C u' * (1 + X 1) ^ e₂] F) =
      τ ^ D * Polynomial.eval₂ ψ ρ f := by
    rw [aeval_def, eval₂_eq', map_sum, hfdef, Polynomial.eval₂_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Polynomial.eval₂_monomial, map_mul, map_pow, algebraMap_eq, hσ, ← hτdef]
    rw [← hD d hd]
    simp only [ψ, RingHom.comp_apply]
    ring
  have hR : φ ((X 0 - X 1) ^ n * G) = τ ^ D * Polynomial.eval₂ ψ ρ f := by
    rw [← hfg, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_X, Polynomial.eval₂_C, map_one,
      Polynomial.eval₂_eq_sum_range (p := g)]
    have hX : (X 0 - X 1 : MvPolynomial (Fin 2) k) = (1 + X 0) - (1 + X 1) := by ring
    rw [map_mul, map_pow, hX, map_sub, hσ, ← hτdef, hGdef, map_sum, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ D - n := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hgdeg
    simp only [map_mul, map_pow, hσ, ← hτdef]
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hi'
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hn
    have : D - n - i = a := by omega
    rw [this, hb]
    rw [hb] at ha
    have hab : b = i + a := by omega
    rw [hab]
    rw [show ρ * τ - τ = (ρ - 1) * τ by ring, mul_pow, mul_pow]
    simp only [ψ, RingHom.comp_apply]
    ring
  rw [hL, hR]

/-- The exponent in `exists_aeval_eq_pow_mul` is unique: it is the order of vanishing along
the diagonal. -/
theorem eq_of_pow_mul_eq_pow_mul {n n' : ℕ} {G G' : MvPolynomial (Fin 2) k}
    (hG : constantCoeff G ≠ 0) (hG' : constantCoeff G' ≠ 0)
    (h : (X 0 - X 1) ^ n * G = (X 0 - X 1) ^ n' * G') : n = n' := by
  have hX : (X 0 - X 1 : MvPolynomial (Fin 2) k) ≠ 0 := by
    exact sub_ne_zero.mpr ((X_injective (σ := Fin 2) (R := k)).ne (by decide))
  have key : ∀ {m m' : ℕ} {H H' : MvPolynomial (Fin 2) k}, constantCoeff H ≠ 0 →
      (X 0 - X 1) ^ m * H = (X 0 - X 1) ^ m' * H' → m ≤ m' → m = m' := by
    intro m m' H H' hH h hle
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [pow_add, mul_assoc] at h
    have h' := mul_left_cancel₀ (pow_ne_zero m hX) h
    rcases c with _ | c
    · rfl
    · exfalso
      apply hH
      rw [h']
      simp [pow_succ]
  rcases le_total n n' with hle | hle
  · exact key hG h hle
  · exact (key hG' h.symm hle).symm

/-- `exists_aeval_eq_pow_mul` for integer weights `(c e₁, c e₂)` with `c > 0`, the form in
which KLR gradings present homogeneity (`deg x_i = 2 d_i`). -/
theorem exists_aeval_eq_pow_mul_of_int {e₁ e₂ : ℕ} (he₁ : 0 < e₁) (he₂ : 0 < e₂) {c D : ℤ}
    (hc : 0 < c) {F : MvPolynomial (Fin 2) k} (hF : F ≠ 0)
    (hhom : F.IsWeightedHomogeneous ![c * e₁, c * e₂] D) {u u' : k} (hu : u ≠ 0)
    (hu' : u' ≠ 0) :
    ∃ (n : ℕ) (G : MvPolynomial (Fin 2) k),
      aeval ![C u * (1 + X 0) ^ e₁, C u' * (1 + X 1) ^ e₂] F = (X 0 - X 1) ^ n * G ∧
        constantCoeff G ≠ 0 := by
  obtain ⟨d, hd⟩ : F.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  refine exists_aeval_eq_pow_mul he₁ he₂ hF (D := d 0 * e₁ + d 1 * e₂) (fun d' hd' => ?_) hu hu'
  have h1 := hhom (mem_support_iff.mp hd)
  have h2 := hhom hd'
  simp only [weight_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] at h1 h2 ⊢
  have : ((d' 0 * e₁ + d' 1 * e₂ : ℕ) : ℤ) * c = ((d 0 * e₁ + d 1 * e₂ : ℕ) : ℤ) * c := by
    push_cast; linear_combination h2 - h1
  exact_mod_cast mul_right_cancel₀ hc.ne' this

namespace UnfurlingDatum

variable {I : Type*} {P : I → I → MvPolynomial (Fin 2) k}

/-- The unfurling datum on `Σ i, U i` (Webster, arXiv:1603.06311v3, definition with label
`def:tilde-I`, and §3.3, equation with label `eq:factorize`): `ϖ_{(i,u)}(z) = u (1 + z)^{d_i}`,
and the arrows and units come from `exists_aeval_eq_pow_mul`. The hypotheses: `d_i > 0` is
invertible in `k`, `0 ∉ U_i`, `P i j ≠ 0` for `i ≠ j`, and `P i j` is weighted homogeneous
for the weights `(d_j, d_i)` (its first variable sits on a `j`-strand). -/
noncomputable def ofSpectra (d : I → ℕ) (hdpos : ∀ i, 0 < d i) (hd : ∀ i, ((d i : ℕ) : k) ≠ 0)
    (U : I → Finset k) (hU : ∀ i, (0 : k) ∉ U i) (hP : ∀ i j, i ≠ j → P i j ≠ 0)
    (hhom : ∀ i j, i ≠ j → ∃ D, (P i j).IsWeightedHomogeneous ![d j, d i] D) :
    UnfurlingDatum k P (Σ i, U i) :=
  haveI := Classical.dec
  let ex : ∀ j j' : (Σ i, U i), j.1 ≠ j'.1 → ∃ (n : ℕ) (G : MvPolynomial (Fin 2) k),
      aeval ![C (j.2 : k) * (1 + X 0) ^ d j.1, C (j'.2 : k) * (1 + X 1) ^ d j'.1]
        (P j'.1 j.1) = (X 0 - X 1) ^ n * G ∧ constantCoeff G ≠ 0 := fun j j' h =>
    exists_aeval_eq_pow_mul (hdpos _) (hdpos _) (hP _ _ (Ne.symm h))
      (hhom _ _ (Ne.symm h)).choose_spec (fun h0 => hU _ (h0 ▸ j.2.2))
      (fun h0 => hU _ (h0 ▸ j'.2.2))
  { π := Sigma.fst
    pw := fun j => Polynomial.C (j.2 : k) * (1 + Polynomial.X) ^ d j.1
    pw_coeff_one := fun j => by
      rw [Polynomial.coeff_C_mul, add_comm, Polynomial.coeff_X_add_one_pow]
      simp only [Nat.choose_one_right]
      exact mul_ne_zero (fun h0 => hU _ (h0 ▸ j.2.2)) (hd _)
    pw_coeff_zero_inj := fun j j' h h0 => by
      obtain ⟨i, u, hu⟩ := j
      obtain ⟨i', u', hu'⟩ := j'
      simp only at h
      subst h
      simp only [Polynomial.coeff_C_mul, add_comm (1 : Polynomial k),
        Polynomial.coeff_X_add_one_pow, Nat.choose_zero_right, Nat.cast_one, mul_one] at h0
      subst h0
      rfl
    arrows := fun j j' => if h : j.1 = j'.1 then 0 else (ex j j' h).choose
    arrows_of_eq := fun j j' h => dite_eq_left_of_eq_true (eq_true h)
    unit := fun j j' => if h : j.1 = j'.1 then 1 else (ex j j' h).choose_spec.choose
    unit_constantCoeff := fun j j' h => by
      simp only [h, ↓reduceDIte]
      exact (ex j j' h).choose_spec.choose_spec.2
    factor := fun j j' h => by
      simp only [h, ↓reduceDIte]
      rw [← (ex j j' h).choose_spec.choose_spec.1]
      congr 2
      funext i
      fin_cases i <;> simp }

end UnfurlingDatum

end Categorification.KLR.Unfurling
