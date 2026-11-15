/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Segment.Perturb
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Segments to an infinitesimally perturbed end point

Let `f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜` be a finite arrangement over an ordered field `𝕜`, let `p, q` be
generic points and let `ρ : ι → ℕ` be injective with positive values. Move the end point to
`q_ε = q + (ε ^ ρ s)_s`. For every sufficiently small `ε > 0`:

* `q_ε` lies in the chamber of `q`;
* the segment from `p` to `q_ε` is simple;
* its word does not depend on `ε`.

Every value `f h (q_ε)` is a polynomial in `ε` with constant term `f h q ≠ 0`, and two crossing
times along the segment agree exactly when a polynomial `pairPoly` in `ε` vanishes. The
coefficient of `ε ^ ρ s` in `pairPoly` is the value at the `s`-th basis vector of the linear part
of `Segment.pairFun`; when distinct hyperplanes are distinct as sets, this linear part is
nonzero, so `pairPoly ≠ 0`. A nonzero polynomial has, for small positive `ε`, the sign of its
lowest coefficient; this fixes both the signs of the values and the order of the crossing
times. No completeness of `𝕜` is used.

This is the general-position input of the straight-line choice of the basis elements in the
basis theorem for weighted KLR algebras (B. Webster, arXiv:1209.2463v4, Theorem 2.8): the bottom
end points are fixed and the top end points are moved by distinct powers of an infinitesimal.

## Main definitions

* `Segment.powVec ρ ε`: the vector `s ↦ ε ^ ρ s`.
* `Segment.perturb ρ q ε`: the point `q + powVec ρ ε`.
* `Segment.StablePerturbation f ρ p q ε₀`: for `0 < ε < ε₀`, the segment from `p` to
  `perturb ρ q ε` is simple, ends in the chamber of `q`, and has a word independent of `ε`.

## Main results

* `Segment.exists_sign_eval`: a nonzero polynomial has constant sign on some interval `(0, δ)`.
* `Segment.exists_stablePerturbation`: such an `ε₀ > 0` exists.
-/

namespace Categorification.WeightedKLR.Segment

open Polynomial

section Poly

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- On `[0, 1]` a polynomial is bounded by the sum of the absolute values of its coefficients. -/
lemma abs_eval_le (R : 𝕜[X]) {ε : 𝕜} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    |R.eval ε| ≤ ∑ i ∈ Finset.range (R.natDegree + 1), |R.coeff i| := by
  rw [eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg h0]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ h0 h1)

/-- A polynomial with nonzero constant term has the sign of that term on some `(0, δ)`. -/
lemma exists_pos_eval_mul_coeff_zero (R : 𝕜[X]) (hR : R.coeff 0 ≠ 0) :
    ∃ δ, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ → 0 < R.eval ε * R.coeff 0 := by
  set S := ∑ i ∈ Finset.range (R.divX.natDegree + 1), |R.divX.coeff i|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc := abs_pos.2 hR
  refine ⟨min 1 (|R.coeff 0| / (S + 1)), lt_min one_pos (div_pos hc (by linarith)),
    fun ε hε hδ => ?_⟩
  have e : R.eval ε = R.coeff 0 + ε * R.divX.eval ε := by
    conv_lhs => rw [← X_mul_divX_add R]
    simp only [eval_add, eval_mul, eval_X, eval_C]
    ring
  have hb := abs_eval_le R.divX hε.le (lt_of_lt_of_le hδ (min_le_left _ _)).le
  have h2 : ε * (S + 1) < |R.coeff 0| :=
    (lt_div_iff₀ (by linarith)).1 (lt_of_lt_of_le hδ (min_le_right _ _))
  have h3 : |ε * R.divX.eval ε| < |R.coeff 0| := by
    rw [abs_mul, abs_of_pos hε]
    nlinarith
  have h4 : |R.coeff 0 * (ε * R.divX.eval ε)| < R.coeff 0 * R.coeff 0 := by
    rw [abs_mul, ← abs_mul_abs_self (R.coeff 0)]
    exact mul_lt_mul_of_pos_left h3 hc
  rw [e]
  nlinarith [neg_abs_le (R.coeff 0 * (ε * R.divX.eval ε))]

/-- A nonzero polynomial has constant sign on some interval `(0, δ)`: the sign of its lowest
coefficient. -/
lemma exists_sign_eval (Q : 𝕜[X]) (hQ : Q ≠ 0) :
    ∃ c δ, c ≠ 0 ∧ 0 < δ ∧ ∀ ε, 0 < ε → ε < δ → 0 < Q.eval ε * c := by
  set m := Q.natTrailingDegree
  obtain ⟨R, hR⟩ : X ^ m ∣ Q :=
    X_pow_dvd_iff.2 fun d hd => coeff_eq_zero_of_lt_natTrailingDegree hd
  have hc : R.coeff 0 = Q.trailingCoeff := by
    have := coeff_X_pow_mul R m 0
    rw [zero_add, ← hR] at this
    exact this.symm
  have hc0 : R.coeff 0 ≠ 0 := by rw [hc]; exact mt trailingCoeff_eq_zero.1 hQ
  obtain ⟨δ, hδ, hpos⟩ := exists_pos_eval_mul_coeff_zero R hc0
  refine ⟨R.coeff 0, δ, hc0, hδ, fun ε hε hεδ => ?_⟩
  rw [hR, eval_mul, eval_pow, eval_X, mul_assoc]
  exact mul_pos (pow_pos hε _) (hpos ε hε hεδ)

end Poly

section Scalar

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

lemma pos_div_iff_pos_mul {x y : 𝕜} (hy : y ≠ 0) : 0 < x / y ↔ 0 < x * y := by
  have : x / y = (x * y) / (y * y) := by field_simp
  rw [this, div_pos_iff_of_pos_right (mul_self_pos.2 hy)]

/-- The order of two crossing times `a / (a - b)` and `a' / (a' - b')`. -/
lemma div_sub_lt_div_sub_iff {a b a' b' : 𝕜} (hab : a * b < 0) (hab' : a' * b' < 0) :
    a / (a - b) < a' / (a' - b') ↔ 0 < (a * b' - a' * b) * (a * a') := by
  have h1 := mul_sub_pos hab
  have h2 := mul_sub_pos hab'
  have n1 := sub_ne_zero_of_mul_neg hab
  have n2 := sub_ne_zero_of_mul_neg hab'
  have e : a' / (a' - b') - a / (a - b) = (a * b' - a' * b) / ((a - b) * (a' - b')) := by
    field_simp; ring
  rw [← sub_pos, e, pos_div_iff_pos_mul (mul_ne_zero n1 n2)]
  have hD : 0 < ((a - b) * (a' - b')) * (a * a') := by nlinarith [mul_pos h1 h2]
  constructor
  · intro h
    rcases lt_or_gt_of_ne (show (a - b) * (a' - b') ≠ 0 from mul_ne_zero n1 n2) with hn | hn
    · have : a * a' < 0 := by nlinarith
      have : a * b' - a' * b < 0 := by nlinarith
      nlinarith
    · have : 0 < a * a' := by nlinarith
      have : 0 < a * b' - a' * b := by nlinarith
      nlinarith
  · intro h
    rcases lt_or_gt_of_ne (show (a - b) * (a' - b') ≠ 0 from mul_ne_zero n1 n2) with hn | hn
    · have : a * a' < 0 := by nlinarith
      have : a * b' - a' * b < 0 := by nlinarith
      nlinarith
    · have : 0 < a * a' := by nlinarith
      have : 0 < a * b' - a' * b := by nlinarith
      nlinarith

end Scalar

variable {ι 𝕜 H : Type*} [Fintype ι] [DecidableEq ι] [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H]

section Perturbation

variable (ρ : ι → ℕ)

/-- The vector `s ↦ ε ^ ρ s`. -/
def powVec (ε : 𝕜) : ι → 𝕜 := fun s => ε ^ ρ s

/-- The point `q` moved by `s ↦ ε ^ ρ s`. -/
def perturb (q : ι → 𝕜) (ε : 𝕜) : ι → 𝕜 := q + powVec ρ ε

/-- The value of `ℓ` at `perturb ρ q ε`, as a polynomial in `ε`. -/
noncomputable def valPoly (ℓ : (ι → 𝕜) →ᵃ[𝕜] 𝕜) (q : ι → 𝕜) : 𝕜[X] :=
  C (ℓ q) + ∑ s, C (ℓ.linear (Pi.single s 1)) * X ^ ρ s

/-- The polynomial in `ε` vanishing exactly when the segment from `p` to `perturb ρ q ε` meets
`f h` and `f g` at the same time. -/
noncomputable def pairPoly (f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜) (p q : ι → 𝕜) (h g : H) : 𝕜[X] :=
  C (f h p) * valPoly ρ (f g) q - C (f g p) * valPoly ρ (f h) q

variable {ρ}

omit [Fintype ι] [DecidableEq ι] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma apply_add (ℓ : (ι → 𝕜) →ᵃ[𝕜] 𝕜) (q v : ι → 𝕜) : ℓ (q + v) = ℓ q + ℓ.linear v := by
  simpa using ℓ.apply_add_smul q v 1

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma eval_valPoly (ℓ : (ι → 𝕜) →ᵃ[𝕜] 𝕜) (q : ι → 𝕜) (ε : 𝕜) :
    (valPoly ρ ℓ q).eval ε = ℓ (perturb ρ q ε) := by
  have hv : powVec ρ ε = ∑ s, (ε ^ ρ s) • (Pi.single s 1 : ι → 𝕜) := by
    rw [← Finset.univ_sum_single (powVec ρ ε)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Pi.single_smul, smul_eq_mul, mul_one]; rfl
  rw [perturb, apply_add, hv, map_sum, valPoly, eval_add, eval_C, eval_finsetSum]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, smul_eq_mul, eval_mul, eval_C, eval_pow, eval_X, mul_comm]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
lemma eval_pairPoly (f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜) (p q : ι → 𝕜) (h g : H) (ε : 𝕜) :
    (pairPoly ρ f p q h g).eval ε =
      f h p * f g (perturb ρ q ε) - f g p * f h (perturb ρ q ε) := by
  simp only [pairPoly, eval_sub, eval_mul, eval_C, eval_valPoly]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma coeff_zero_valPoly (hρ : ∀ s, ρ s ≠ 0) (ℓ : (ι → 𝕜) →ᵃ[𝕜] 𝕜) (q : ι → 𝕜) :
    (valPoly ρ ℓ q).coeff 0 = ℓ q := by
  rw [valPoly, coeff_add, coeff_C_zero, finsetSum_coeff]
  simp [(hρ _).symm]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
lemma coeff_valPoly (hρ : Function.Injective ρ) (hρ0 : ∀ s, ρ s ≠ 0)
    (ℓ : (ι → 𝕜) →ᵃ[𝕜] 𝕜) (q : ι → 𝕜) (s : ι) :
    (valPoly ρ ℓ q).coeff (ρ s) = ℓ.linear (Pi.single s 1) := by
  rw [valPoly, coeff_add, coeff_C_of_ne_zero (hρ0 s), zero_add, finsetSum_coeff]
  simp [hρ.eq_iff]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
lemma coeff_pairPoly (hρ : Function.Injective ρ) (hρ0 : ∀ s, ρ s ≠ 0)
    (f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜) (p q : ι → 𝕜) (h g : H) (s : ι) :
    (pairPoly ρ f p q h g).coeff (ρ s) = (pairFun f p h g).linear (Pi.single s 1) := by
  rw [pairPoly, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_valPoly hρ hρ0,
    coeff_valPoly hρ hρ0, pairFun, AffineMap.sub_linear, AffineMap.smul_linear,
    AffineMap.smul_linear]
  simp

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype H] [DecidableEq H] in
/-- When `f h` and `f g` have a point on one and off the other, `pairPoly` is nonzero. -/
lemma pairPoly_ne_zero (hρ : Function.Injective ρ) (hρ0 : ∀ s, ρ s ≠ 0)
    {f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜} (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0)
    {p : ι → 𝕜} (hp : Generic f p) (q : ι → 𝕜) {h g : H} (hne : h ≠ g) :
    pairPoly ρ f p q h g ≠ 0 := by
  intro hz
  obtain ⟨y, hy⟩ := pairFun_ne_zero hdist hp hne
  have hlin : (pairFun f p h g).linear = 0 := by
    refine LinearMap.pi_ext fun s x => ?_
    have hs : (pairFun f p h g).linear (Pi.single s 1) = 0 := by
      rw [← coeff_pairPoly hρ hρ0 f p q h g s, hz, coeff_zero]
    rw [show (Pi.single s x : ι → 𝕜) = x • Pi.single s 1 by rw [← Pi.single_smul, smul_eq_mul,
      mul_one], map_smul, hs, smul_zero, LinearMap.zero_apply]
  refine hy ?_
  rw [AffineMap.apply_eq_of_linear_eq_zero _ hlin y p, pairFun_apply]
  ring

end Perturbation

variable (f : H → (ι → 𝕜) →ᵃ[𝕜] 𝕜) (ρ : ι → ℕ)

/-- For `0 < ε < ε₀`, the segment from `p` to `perturb ρ q ε` is simple, its end point lies in
the chamber of `q`, and its word does not depend on `ε`. -/
def StablePerturbation (p q : ι → 𝕜) (ε₀ : 𝕜) : Prop :=
  0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
    Simple f p (perturb ρ q ε) ∧ signs f (perturb ρ q ε) = signs f q ∧
      ∀ ε', 0 < ε' → ε' < ε₀ → word f p (perturb ρ q ε) = word f p (perturb ρ q ε')

variable {f ρ}

omit [DecidableEq H] in
/-- **Infinitesimal perturbation of the end point.** For generic `p, q`, an arrangement in which
each hyperplane has a point off any other one, and an injective `ρ` with positive values, the
segment from `p` to `q + (ε ^ ρ s)_s` is simple, ends in the chamber of `q`, and has a word
independent of `ε`, for all sufficiently small `ε > 0`. -/
theorem exists_stablePerturbation (hρ : Function.Injective ρ) (hρ0 : ∀ s, ρ s ≠ 0)
    (hdist : ∀ h g, h ≠ g → ∃ x, f h x = 0 ∧ f g x ≠ 0) {p q : ι → 𝕜} (hp : Generic f p)
    (hq : Generic f q) : ∃ ε₀, StablePerturbation f ρ p q ε₀ := by
  classical
  -- the values at the perturbed point keep their signs
  have A : ∀ h, ∃ δ, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ → 0 < f h (perturb ρ q ε) * f h q := by
    intro h
    obtain ⟨δ, hδ, hpos⟩ := exists_pos_eval_mul_coeff_zero (valPoly ρ (f h) q)
      (by rw [coeff_zero_valPoly hρ0]; exact hq h)
    refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
    have := hpos ε hε hεδ
    rwa [eval_valPoly, coeff_zero_valPoly hρ0] at this
  -- the pair polynomials keep their signs
  have B : ∀ x : H × H, ∃ c δ, 0 < δ ∧ (x.1 ≠ x.2 → c ≠ 0 ∧ ∀ ε, 0 < ε → ε < δ →
      0 < (f x.1 p * f x.2 (perturb ρ q ε) - f x.2 p * f x.1 (perturb ρ q ε)) * c) := by
    intro x
    by_cases hx : x.1 = x.2
    · exact ⟨1, 1, one_pos, fun h => (h hx).elim⟩
    obtain ⟨c, δ, hc, hδ, hpos⟩ :=
      exists_sign_eval _ (pairPoly_ne_zero hρ hρ0 hdist hp q hx)
    refine ⟨c, δ, hδ, fun _ => ⟨hc, fun ε hε hεδ => ?_⟩⟩
    have := hpos ε hε hεδ
    rwa [eval_pairPoly] at this
  choose δA hδA hA using A
  choose cB δB hδB hB using B
  set S : Finset 𝕜 := insert 1 (Finset.univ.image δA ∪ Finset.univ.image δB)
  have hSne : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  set ε₀ := S.min' hSne
  have hε₀ : 0 < ε₀ := by
    change 0 < S.min' hSne
    have hm := S.min'_mem hSne
    rcases Finset.mem_insert.1 hm with hm | hm
    · rw [hm]; exact one_pos
    rcases Finset.mem_union.1 hm with hm | hm
    · obtain ⟨h, -, hm⟩ := Finset.mem_image.1 hm
      rw [← hm]; exact hδA h
    · obtain ⟨x, -, hm⟩ := Finset.mem_image.1 hm
      rw [← hm]; exact hδB x
  have leA : ∀ h, ε₀ ≤ δA h := fun h => S.min'_le _
    (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ h))))
  have leB : ∀ x, ε₀ ≤ δB x := fun x => S.min'_le _
    (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ x))))
  -- consequences at a fixed admissible `ε`
  have hgen : ∀ ε, 0 < ε → ε < ε₀ → Generic f (perturb ρ q ε) ∧
      signs f (perturb ρ q ε) = signs f q := by
    intro ε hε hεε
    have key := fun h => hA h ε hε (lt_of_lt_of_le hεε (leA h))
    refine ⟨fun h e => by simpa [e] using key h, funext fun h => ?_⟩
    simp only [signs]
    exact decide_eq_decide.2 (pos_iff_of_mul_pos (key h))
  have hsep : ∀ ε, 0 < ε → ε < ε₀ → ∀ h,
      Separates f p (perturb ρ q ε) h ↔ Separates f p q h := fun ε hε hεε h =>
    separates_congr_right (p := p) (hgen ε hε hεε).2 h
  have hpair : ∀ ε, 0 < ε → ε < ε₀ → ∀ h g, h ≠ g →
      0 < (f h p * f g (perturb ρ q ε) - f g p * f h (perturb ρ q ε)) * cB (h, g) :=
    fun ε hε hεε h g hne => (hB (h, g) hne).2 ε hε (lt_of_lt_of_le hεε (leB _))
  have hsimple : ∀ ε, 0 < ε → ε < ε₀ → Simple f p (perturb ρ q ε) := by
    intro ε hε hεε
    refine ⟨hp, (hgen ε hε hεε).1, fun h g hh hg hne e => ?_⟩
    rw [crossTime_eq_iff (ne_of_separates hh) (ne_of_separates hg)] at e
    have := hpair ε hε hεε h g hne
    rw [e, sub_self, zero_mul] at this
    exact lt_irrefl _ this
  -- the order of two crossing times does not depend on `ε`
  have horder : ∀ ε, 0 < ε → ε < ε₀ → ∀ ε', 0 < ε' → ε' < ε₀ → ∀ h g,
      Separates f p q h → Separates f p q g → h ≠ g →
      crossTime f p (perturb ρ q ε) h < crossTime f p (perturb ρ q ε) g →
        crossTime f p (perturb ρ q ε') h < crossTime f p (perturb ρ q ε') g := by
    intro ε hε hεε ε' hε' hεε' h g hh hg hne hlt
    have sep := fun ε hε hεε h hh => (separates_iff_mul_neg (hp h) ((hgen ε hε hεε).1 h)).1
      ((hsep ε hε hεε h).2 hh)
    simp only [crossTime] at hlt ⊢
    rw [div_sub_lt_div_sub_iff (sep ε hε hεε h hh) (sep ε hε hεε g hg)] at hlt
    rw [div_sub_lt_div_sub_iff (sep ε' hε' hεε' h hh) (sep ε' hε' hεε' g hg)]
    have h1 := hpair ε hε hεε h g hne
    have h2 := hpair ε' hε' hεε' h g hne
    have hc := (hB (h, g) hne).1
    set N := f h p * f g (perturb ρ q ε) - f g p * f h (perturb ρ q ε)
    set N' := f h p * f g (perturb ρ q ε') - f g p * f h (perturb ρ q ε')
    have hNN : 0 < N * N' := by
      have e : (N * cB (h, g)) * (N' * cB (h, g)) = (N * N') * (cB (h, g) * cB (h, g)) := by
        ring
      have := mul_pos h1 h2
      rw [e] at this
      exact pos_of_mul_pos_left this (mul_self_nonneg _)
    set K := f h p * f g p
    have e : (N' * K) * (N * K) = (N * N') * (K * K) := by ring
    have hK : K ≠ 0 := fun hK => by rw [hK, mul_zero] at hlt; exact lt_irrefl _ hlt
    have := mul_pos hNN (mul_self_pos.2 hK)
    rw [← e] at this
    exact pos_of_mul_pos_left this hlt.le
  refine ⟨ε₀, hε₀, fun ε hε hεε => ⟨hsimple ε hε hεε, (hgen ε hε hεε).2,
    fun ε' hε' hεε' => ?_⟩⟩
  refine (word_eq_of_pairwise (hsimple ε' hε' hεε') ?_ fun h => ?_).symm
  · refine (pairwise_word (hsimple ε hε hεε)).imp_of_mem fun {a b} ha hb hab => ?_
    have ha' := (hsep ε hε hεε _).1 (mem_word.1 ha)
    have hb' := (hsep ε hε hεε _).1 (mem_word.1 hb)
    have hne : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
    exact horder ε hε hεε ε' hε' hεε' _ _ ha' hb' hne hab
  · rw [mem_word, hsep ε hε hεε, hsep ε' hε' hεε']

end Categorification.WeightedKLR.Segment
