/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.GammaHomo
import Categorification.KLR.Unfurling.Generic
import Categorification.KLR.Unfurling.Truncation
import Categorification.KLR.CyclotomicMultFree

/-!
# Triangularity of `γ` on a corner of the unfurled cyclotomic quotient

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the theorem
with label `nondegenerate`, the step showing that a relation acts by zero, at the level of the KLR algebra.

Fix an unfurling datum `D` without arrows (for instance `UnfurlingDatum.ofGeneric`), a weight
`ν̃` of `J` with pairwise distinct labels over `ν`, and `M`. Compose `γ` (Lemma `lem:gamma-homo`,
`Unfurling.gamma`), the projection to the factor `𝖱̂(ν̃)`, and the extension
(`GradingDatum.completionLift`) of the quotient map to the cyclotomic quotient `𝖱^Λ(ν̃)` with
`a_j = y^M` for every label; the dots are nilpotent there. Call the composite `Γ`
(`Unfurling.cycGamma`).

For a lift `t` of `𝐢` (`π ∘ t = 𝐢`) and a reduced word `σ`:

* `Unfurling.corner_cycGamma_ψw_eq_zero`: `e(u • t) Γ(ψ_σ) e(t) = 0` when `ℓ(u) ≥ |σ|` and
  `u ≠ w_σ`. Each crossing is sent to a sum of a crossing and (for strands of the same colour)
  an identity term, and with distinct labels only words of length `≥ ℓ(u)` can connect `t` to
  `u • t`; this is Webster's remark that the image of a diagram for a pairing consists of
  diagrams for that pairing and for pairings with fewer crossings.
* `Unfurling.corner_cycGamma_ψw`: `e(w_σ • t) Γ(ψ_σ) e(t) = ψ_σ U(y) e(t)` with `U` of nonzero
  constant term: only the full word survives, and every crossing contributes a unit factor in
  the dots (Webster's observation that the leading diagram is multiplied by an invertible power
  series).
* `Unfurling.eq_zero_of_cycGamma_mul_e_eq_zero`, `Unfurling.eq_zero_of_cycGamma_eq_zero`: if
  `Γ(∑ c_{w,u} ψ_{ρ w} x^u e(𝐢)) e(t) = 0` (in particular if `Γ(∑ …) = 0`) with all exponents
  `u_a < M`, then all `c_{w,u} = 0`. The series `ϖ_j` are arbitrary (with nonzero linear
  coefficient, as in every unfurling datum): Webster's `u(1 + x)^{d_i}` and the linear series
  `z_j + x` of `UnfurlingDatum.ofGeneric` are both covered. Take `w` of maximal length with a
  nonzero coefficient; in the corner `e(w • t) (·) e(t)` only the terms with this `w` remain,
  and they give `ψ_{ρ w} U(y) f(ϖ_{t_1}(y_1), …) e(t)` with `f = ∑_u c_{w,u} x^u`. The corner
  basis of the cyclotomic quotient (`CycKLR.cornerBasis`, the rank-one computation of the
  source) and the invertibility of `U` modulo `(y_a^M)` reduce this to `f(ϖ(y)) ≡ 0` modulo
  `(y_a^M)`, and `eq_zero_of_aeval_mem_boxIdeal` gives `f = 0`: after the shift
  `x_a ↦ ϖ_a(0) + x_a`, the substitution sends `x^c` to `y^c` times a unit, so the coefficient
  of a minimal exponent `c` survives (this is Webster's "minimal number of dots" step).

Comparison with the source. Webster applies the argument to the 2-category `𝒰` and the
representations `𝒳^{μ₊, μ₋}`, with the bound `m` on the number of dots; here the statement is
for the KLR algebra `R(ν)` and its basis `ψ_{ρ w} x^u e(𝐢)` (KL I, Theorem 2.5), the
representation being the cyclotomic quotient of the unfurled KLR algebra with labels pairwise
distinct and non-adjacent. The field `k` is arbitrary. The unfurled index set `J` is finite
(needed for the extension `GradingDatum.completionLift`); Webster's spectra may be infinite,
but only the finitely many labels of `ν̃` enter the argument. The statement covers one
idempotent `e(𝐢)` at a time; a relation involving several is first multiplied by `e(𝐢)` on the
right.
-/

namespace Categorification.KLR.Unfurling

open MvPolynomial TypeA PolyRep KLRAlgebra GradingDatum Equiv

/-! ### Truncation of power series to a box of exponents -/

section Box

variable {k : Type*} [CommRing k] {n : ℕ}

/-- The exponents `c` with `c_a < N` for every `a`. -/
noncomputable def boxSet (n N : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => N)).filter fun c => ∀ a, c a < N

theorem mem_boxSet {N : ℕ} {c : Fin n →₀ ℕ} : c ∈ boxSet n N ↔ ∀ a, c a < N := by
  rw [boxSet, Finset.mem_filter, Finset.mem_Iic]
  refine ⟨And.right, fun h => ⟨fun a => ?_, h⟩⟩
  rw [Finsupp.equivFunOnFinite_symm_apply_apply]
  exact (h a).le

/-- The truncation of a power series to the monomials `x^c` with `c_a < N` for every `a`. -/
noncomputable def boxTrunc (N : ℕ) (F : MvPowerSeries (Fin n) k) : MvPolynomial (Fin n) k :=
  ∑ c ∈ boxSet n N, monomial c (MvPowerSeries.coeff c F)

theorem coeff_boxTrunc (N : ℕ) (F : MvPowerSeries (Fin n) k) (c : Fin n →₀ ℕ) :
    (boxTrunc N F).coeff c = if ∀ a, c a < N then MvPowerSeries.coeff c F else 0 := by
  classical
  rw [boxTrunc, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [mem_boxSet]

theorem constantCoeff_boxTrunc {N : ℕ} (hN : 0 < N) (F : MvPowerSeries (Fin n) k) :
    constantCoeff (boxTrunc N F) = MvPowerSeries.constantCoeff F := by
  rw [MvPolynomial.constantCoeff_eq, coeff_boxTrunc, ite_eq_left fun _ => by simpa using hN,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

end Box

section Ideal

variable {k : Type*} [Field k]

/-- A polynomial with nonzero constant term is invertible modulo `(y_a^M)`: if `U F` lies in
the ideal, so does `F`. -/
theorem mem_of_mul_mem_boxIdeal {n M : ℕ} {U F : MvPolynomial (Fin n) k}
    (hU : constantCoeff U ≠ 0)
    (h : U * F ∈ boxIdeal (fun _ : Fin n => (Polynomial.X ^ M : Polynomial k))) :
    F ∈ boxIdeal (fun _ : Fin n => (Polynomial.X ^ M : Polynomial k)) := by
  set I := boxIdeal (fun _ : Fin n => (Polynomial.X ^ M : Polynomial k))
  have hX : ∀ q, (X q ^ M : MvPolynomial (Fin n) k) ∈ I := fun q =>
    Ideal.subset_span ⟨q, by simp⟩
  have hnil : ∀ f : MvPolynomial (Fin n) k, constantCoeff f = 0 →
      Ideal.Quotient.mk I f ∈ nilradical _ := by
    intro f hf
    rw [f.as_sum, map_sum]
    refine Ideal.sum_mem _ fun s hs => ?_
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact (mem_support_iff.1 hs) (by rw [← hf, constantCoeff_eq])
    obtain ⟨q, hq⟩ : ∃ q, s q ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hs0 (Finsupp.ext fun q => by simpa using hcon q)
    have hm : monomial s (f.coeff s) = monomial (s - Finsupp.single q 1) (f.coeff s) * X q := by
      rw [X, monomial_mul_monomial, mul_one,
        tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hq))]
    rw [hm, map_mul]
    refine Ideal.mul_mem_left _ _ (mem_nilradical.2 ⟨M, ?_⟩)
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hX q
  have hu : IsUnit (Ideal.Quotient.mk I (C (constantCoeff U))) :=
    IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (C (constantCoeff U)⁻¹)) (by
      rw [← map_mul, ← C_mul, mul_inv_cancel₀ hU, C_1, map_one])
  have hsplit : Ideal.Quotient.mk I U = Ideal.Quotient.mk I (C (constantCoeff U)) +
      Ideal.Quotient.mk I (U - C (constantCoeff U)) := by
    rw [← map_add, add_sub_cancel]
  have hunit : IsUnit (Ideal.Quotient.mk I U) := by
    rw [hsplit]
    exact (mem_nilradical.1 (hnil _ (by simp))).isUnit_add_left_of_commute hu (Commute.all _ _)
  have h0 : Ideal.Quotient.mk I (U * F) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
  rw [map_mul, hunit.mul_right_eq_zero] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

/-- The shift `y_a ↦ y_a - z_a`: if `f(z + y) ∈ (y_a^M)`, then `f ∈ ((y_a - z_a)^M)`. -/
theorem mem_boxIdeal_of_aeval_add_mem {n n' M : ℕ} (hn : n = n') (z : Fin n → k)
    {f : MvPolynomial (Fin n) k}
    (h : aeval (fun a => C (z a) + X (Fin.cast hn a)) f ∈
      boxIdeal (fun _ : Fin n' => (Polynomial.X ^ M : Polynomial k))) :
    f ∈ boxIdeal fun a => (Polynomial.X - Polynomial.C (z a)) ^ M := by
  subst hn
  let σ : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k := aeval fun a => X a - C (z a)
  have hσ : σ.comp (aeval fun a => C (z a) + X (Fin.cast rfl a)) = AlgHom.id k _ := by
    ext a
    simp [σ]
  have hle : boxIdeal (fun _ : Fin n => (Polynomial.X ^ M : Polynomial k)) ≤
      (boxIdeal fun a => (Polynomial.X - Polynomial.C (z a)) ^ M).comap σ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    refine Ideal.subset_span ⟨q, ?_⟩
    simp [σ, MvPolynomial.algebraMap_eq]
  have := hle h
  rwa [Ideal.mem_comap, ← AlgHom.comp_apply, hσ, AlgHom.id_apply] at this

end Ideal

/-! ### Substitution by series with nonzero linear coefficient -/

section Substitution

variable {k : Type*} [Field k] {n : ℕ}

/-- The shift `x_a ↦ z_a + x_a` does not raise the degree in any variable. -/
theorem degreeOf_aeval_C_add_X_le (z : Fin n → k) (f : MvPolynomial (Fin n) k) (b : Fin n) :
    degreeOf b (aeval (fun a => C (z a) + X a) f) ≤ degreeOf b f := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [aeval_monomial, algebraMap_eq]
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  refine (degreeOf_prod_le _ _ _).trans ((Finset.sum_le_sum fun a _ =>
    degreeOf_pow_le _ _ _).trans ?_)
  refine le_trans ?_ (monomial_le_degreeOf b hs)
  have hle : ∀ a, degreeOf b (C (z a) + X a : MvPolynomial (Fin n) k) ≤ if a = b then 1 else 0 := by
    intro a
    refine (degreeOf_add_le _ _ _).trans (max_le (by rw [degreeOf_C]; exact Nat.zero_le _) ?_)
    rw [degreeOf_X]
    split_ifs <;> simp_all [eq_comm]
  calc ∑ a ∈ s.support, s a * degreeOf b (C (z a) + X a : MvPolynomial (Fin n) k)
      ≤ ∑ a ∈ s.support, s a * (if a = b then 1 else 0) :=
        Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (hle a)
    _ ≤ s b := by
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
        split_ifs <;> simp

/-- An element of `(x_a^M)` has no monomial `x^c` with all `c_a < M`. -/
theorem coeff_eq_zero_of_mem_boxIdeal {M : ℕ} {F : MvPolynomial (Fin n) k}
    (hF : F ∈ boxIdeal (fun _ : Fin n => (Polynomial.X ^ M : Polynomial k))) {c : Fin n →₀ ℕ}
    (hc : ∀ a, c a < M) : F.coeff c = 0 := by
  classical
  have hspan : boxIdeal (fun _ : Fin n => (Polynomial.X ^ M : Polynomial k)) =
      Ideal.span ((fun s => monomial s (1 : k)) '' Set.range fun q => Finsupp.single q M) := by
    rw [boxIdeal, ← Set.range_comp]
    congr 2
    funext q
    simp [X_pow_eq_monomial]
  rw [hspan, mem_ideal_span_monomial_image] at hF
  by_contra h0
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hF c (mem_support_iff.2 h0)
  have := hq q
  simp only [Finsupp.single_eq_same] at this
  exact (hc q).not_ge this

/-- The coefficient of a minimal exponent after the substitution `x_a ↦ x_a V_a`. -/
theorem coeff_aeval_X_mul_of_minimal (V : Fin n → MvPolynomial (Fin n) k)
    (f : MvPolynomial (Fin n) k) {c : Fin n →₀ ℕ}
    (hmin : ∀ c' ∈ f.support, c' ≤ c → c' = c) :
    (aeval (fun a => X a * V a) f).coeff c =
      f.coeff c * c.prod fun a e => constantCoeff (V a) ^ e := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  rw [coeff_sum]
  have hterm : ∀ s, aeval (fun a => X a * V a) (monomial s (f.coeff s)) =
      monomial s (f.coeff s) * s.prod fun a e => V a ^ e := by
    intro s
    rw [aeval_monomial, algebraMap_eq, monomial_eq, mul_assoc, ← Finsupp.prod_mul]
    simp only [mul_pow]
  simp only [hterm, coeff_monomial_mul']
  by_cases hc : c ∈ f.support
  · rw [Finset.sum_eq_single c]
    · rw [ite_eq_left_iff.2 fun h => (h le_rfl).elim, tsub_self, ← constantCoeff_eq,
        map_finsuppProd]
      simp only [map_pow]
    · intro s hs hne
      rw [ite_eq_right_iff.2 fun hle => (hne (hmin s hs hle)).elim]
    · intro h; exact (h hc).elim
  · rw [notMem_support_iff.1 hc, zero_mul]
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [ite_eq_right_iff.2 fun hle => (hc (hmin s hs hle ▸ hs)).elim]

/-- **Substitution by series with nonzero linear coefficient is injective modulo `(y_a^M)` on
polynomials of degree `< M` in each variable.** If `φ_a(0)`-shifted variables are replaced by
`φ_a(y_a)` with `φ_a'(0) ≠ 0`, and `f(φ(y)) ∈ (y_a^M)` with `f` supported on exponents `< M`,
then `f = 0`. -/
theorem eq_zero_of_aeval_mem_boxIdeal {n' M : ℕ} (hn : n = n') (φ : Fin n → Polynomial k)
    (hφ : ∀ a, (φ a).coeff 1 ≠ 0) {f : MvPolynomial (Fin n) k}
    (hf : ∀ s, f.coeff s ≠ 0 → ∀ a, s a < M)
    (h : aeval (fun a => Polynomial.aeval (X (Fin.cast hn a)) (φ a)) f ∈
      boxIdeal (fun _ : Fin n' => (Polynomial.X ^ M : Polynomial k))) : f = 0 := by
  classical
  subst hn
  simp only [Fin.cast_eq_self] at h
  by_contra hf0
  -- the shift
  set z : Fin n → k := fun a => (φ a).coeff 0
  have hdvd : ∀ a, Polynomial.X ∣ φ a - Polynomial.C (z a) := fun a =>
    Polynomial.X_dvd_iff.2 (by simp [z])
  choose q hq using hdvd
  have hq0 : ∀ a, (q a).coeff 0 ≠ 0 := by
    intro a
    have := congrArg (fun p : Polynomial k => p.coeff 1) (hq a)
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_mul] at this
    rw [← this]
    simpa using hφ a
  set ft := aeval (fun a => C (z a) + X a) f
  have hback : aeval (fun a => X a - C (z a)) ft = f := by
    rw [← AlgHom.comp_apply, comp_aeval]
    conv_rhs => rw [← aeval_X_left_apply f]
    refine congrArg (fun F => aeval F f) (funext fun a => ?_)
    simp
  have hft0 : ft ≠ 0 := fun h0 => hf0 (by rw [← hback, h0, map_zero])
  -- the substitution factors through the shift
  set V : Fin n → MvPolynomial (Fin n) k := fun a => Polynomial.aeval (X a) (q a)
  have hfac : aeval (fun a => Polynomial.aeval (X a) (φ a)) f = aeval (fun a => X a * V a) ft := by
    rw [← AlgHom.comp_apply, comp_aeval]
    refine congrArg (fun F => aeval F f) (funext fun a => ?_)
    have : φ a = Polynomial.C (z a) + Polynomial.X * q a := by rw [← hq a]; ring
    rw [this]
    simp [V, MvPolynomial.algebraMap_eq]
  -- a minimal exponent of the shifted polynomial
  obtain ⟨c, hcmin⟩ := exists_minimal_of_wellFoundedLT (· ∈ ft.support)
    (support_nonempty.2 hft0)
  have hcs : c ∈ ft.support := hcmin.prop
  have hcbox : ∀ a, c a < M := by
    intro a
    have hM : 0 < M := by
      obtain ⟨s, hs⟩ := support_nonempty.2 hf0
      exact (Nat.zero_le _).trans_lt (hf s (mem_support_iff.1 hs) a)
    calc c a ≤ degreeOf a ft := monomial_le_degreeOf a hcs
      _ ≤ degreeOf a f := degreeOf_aeval_C_add_X_le z f a
      _ < M := (degreeOf_lt_iff hM).2 fun s hs => hf s (mem_support_iff.1 hs) a
  have hcoeff := coeff_aeval_X_mul_of_minimal V ft (c := c) fun c' hc' hle =>
    le_antisymm hle (hcmin.2 hc' hle)
  rw [← hfac, coeff_eq_zero_of_mem_boxIdeal h hcbox] at hcoeff
  refine (mul_ne_zero (mem_support_iff.1 hcs) ?_) hcoeff.symm
  rw [Finsupp.prod]
  refine Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ ?_
  have hcc : ∀ p : Polynomial k,
      constantCoeff (Polynomial.aeval (X a : MvPolynomial (Fin n) k) p) = p.coeff 0 := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, hp, hq, Polynomial.coeff_add]
    | monomial m r =>
      rw [Polynomial.aeval_monomial, map_mul, algebraMap_eq, constantCoeff_C, map_pow,
        constantCoeff_X, Polynomial.coeff_monomial]
      rcases m with _ | m <;> simp
  simp only [V, hcc]
  exact hq0 a

end Substitution

/-- The series of `UnfurlingDatum.ofGeneric` are linear, `ϖ_j(x) = z_j + x`. -/
theorem UnfurlingDatum.ofGeneric_pw_linear {I J k : Type*} [Field k]
    {P : I → I → MvPolynomial (Fin 2) k} (π : J → I) (z : J → k) (hz) (hP) (j : J) :
    (UnfurlingDatum.ofGeneric (P := P) π z hz hP).pw j =
      Polynomial.C (((UnfurlingDatum.ofGeneric (P := P) π z hz hP).pw j).coeff 0) +
        Polynomial.X := by
  simp

theorem wordProd_eq_of_eq {n n' : ℕ} (hn : n = n') {σ τ : List ℕ}
    (h : wordProd n' σ = wordProd n' τ) : wordProd n σ = wordProd n τ := by
  subst hn; exact h

/-! ### The composite `Γ` -/

variable {I J : Type*} [DecidableEq I] [DecidableEq J] {k : Type*} [Field k]
  {P Q : I → I → MvPolynomial (Fin 2) k} (D : UnfurlingDatum k P J)

/-- The cyclotomic quotient `𝖱^Λ(ν̃)` of the unfurled KLR algebra with `a_j = y^M` for
every label `j`. -/
abbrev UnfCyc (ν' : Multiset J) (M : ℕ) : Type _ :=
  CycKLR k (unfQ (k := k) D.arrows) (fun _ => Polynomial.X ^ M) ν'

/-- The quotient map `𝖱(ν̃) → 𝖱^Λ(ν̃)`. -/
noncomputable abbrev cycMk (ν' : Multiset J) (M : ℕ) : UnfKLR D ν' →ₐ[k] UnfCyc D ν' M :=
  CycKLR.mk k _ _ ν'

omit [DecidableEq I] [DecidableEq J] in
/-- Without arrows, the unfurled parameters are `Q = 1`. -/
theorem unfQ_eq_one (harr : ∀ a b, D.arrows a b = 0) (a b : J) :
    unfQ (k := k) D.arrows a b = 1 := by
  simp [unfQ, unfP, harr]

variable (harr : ∀ a b, D.arrows a b = 0) {ν : Multiset I} {ν' : Multiset J}
  (hν : ν'.map D.π = ν) (hnd : ν'.Nodup) (M : ℕ)

local notation "m'" => Multiset.card ν'

omit [DecidableEq I] in
include harr hnd in
/-- The dots satisfy `y_a^M = 0` in `𝖱^Λ(ν̃)`: the labels are pairwise distinct and
non-adjacent, so the cyclotomic relation holds on every strand. -/
theorem cycMk_pol_X_pow (a : Fin m') : cycMk D ν' M (pol (X a ^ M)) = 0 := by
  rw [← mul_one (pol _), ← sum_e, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have := CycKLR.mk_aeval_x_mul_e_of_nodup (a := fun _ => Polynomial.X ^ M) hnd
    (fun i _ j _ _ => unfQ_eq_one D harr i j) s a
  simpa [map_pow, pol_X] using this

/-- The extension `𝖱̂(ν̃) → 𝖱^Λ(ν̃)` of the quotient map to the completion. -/
noncomputable def cycLift : UnfCompl D ν' →ₐ[k] UnfCyc D ν' M :=
  (unfGrading (k := k) D.arrows).completionLift (cycMk D ν' M) (cycMk_pol_X_pow D harr hnd M)

omit [DecidableEq I] in
variable {D} in
theorem cycLift_toC (r : UnfKLR D ν') : cycLift D harr hnd M (toC D r) = cycMk D ν' M r :=
  completionLift_toCompletion _ _ _ r

variable (hPQ : ∀ a b, a ≠ b → Q a b = P b a * rename ![1, 0] (P a b))

/-- **The composite `Γ : R(ν) → 𝖱^Λ(ν̃)`**: `γ` (Webster, Lemma label `lem:gamma-homo`),
the projection to the factor `𝖱̂(ν̃)`, and the extension of the cyclotomic quotient map to the
completion. -/
noncomputable def cycGamma : KLRAlgebra k Q ν →ₐ[k] UnfCyc D ν' M :=
  (cycLift D harr hnd M).comp
    ((Pi.evalAlgHom k (fun ν'' : Lift D ν => UnfCompl D ν''.1) ⟨ν', hν⟩).comp (gamma D hPQ))

local notation "E" s:max => cycMk D ν' M (e s)
local notation "Γ" => cycGamma D harr hν hnd M hPQ
local notation "Φ" => cycLift D harr hnd M

theorem cycGamma_gen (g : Gen ν) :
    Γ (KLRAlgebra.mk k Q ν (FreeAlgebra.ι k g)) = Φ (genImage D hν g) := by
  simp only [cycGamma, AlgHom.comp_apply, gamma_mk, Pi.evalAlgHom_apply]
  rw [freeGamma, FreeAlgebra.lift_ι_apply]

/-! ### Products with idempotents -/

omit [DecidableEq I] in
theorem cycMk_e_mul_e (s t : Seq ν') : E s * E t = if s = t then E s else 0 := by
  simp only [← map_mul, e_mul_e]
  split_ifs <;> simp

omit [DecidableEq I] in
/-- Inserting `1 = ∑_s e(s)` between two factors. -/
theorem mul_eq_sum_e (X Y : UnfCyc D ν' M) : X * Y = ∑ s, X * E s * (E s * Y) := by
  have h1 : ∑ s, E s = 1 := by rw [← map_sum, sum_e, map_one]
  calc X * Y = X * (∑ s, E s) * Y := by rw [h1, mul_one]
    _ = ∑ s, X * E s * (E s * Y) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      have : E s * E s = E s := by rw [← map_mul, e_mul_self]
      rw [← mul_assoc (X * E s) (E s) Y, mul_assoc X (E s) (E s), this]

/-! ### Power series in the dots -/

omit [DecidableEq I] in
/-- On the summand `t`, a power series in the dots is sent to its truncation. -/
theorem cycLift_serU {N : ℕ} (hN : M ≤ N) (t : Seq ν') (F : MvPowerSeries (Fin m') k) :
    Φ (serU D t F) = cycMk D ν' M (pol (boxTrunc N F) * e t) := by
  set T := boxTrunc N F
  have hsplit : serU D t F = serU D t (↑T) + serU D t (F - ↑T) := by
    rw [serU, serU, serU, ← seriesAt_add, add_sub_cancel]
  rw [hsplit, map_add, serU, seriesAt_coe, cycLift_toC, add_eq_left]
  rw [cycLift, completionLift_apply, truncSum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [coeff_seriesAt, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : ∀ a, c a < N
  · rw [map_sub, MvPolynomial.coeff_coe, coeff_boxTrunc, ite_eq_left hc, sub_self,
      zero_smul, map_zero]
  · simp only [not_forall, not_lt] at hc
    obtain ⟨a, ha⟩ := hc
    have hu : monomial c (1 : k) = monomial (c - Finsupp.single a M) 1 * X a ^ M := by
      rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul,
        tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (hN.trans ha))]
    rw [map_smul, hu, map_mul, map_mul, map_mul, cycMk_pol_X_pow D harr hnd M, mul_zero, zero_mul,
      smul_zero]

/-! ### Images of the generators -/

theorem cycGamma_e (i : Seq ν) : Γ (e i) = ∑ t with down D.π hν t = i, E t := by
  rw [e, fe, cycGamma_gen, genImage, map_sum]
  simp only [cycLift_toC]

theorem cycGamma_x (a : Fin (Multiset.card ν)) :
    Γ (x a) = ∑ t, cycMk D ν' M (pol (pwAt D.pw (t.lbl (Fin.cast (card_eq D.π hν) a))
      (Fin.cast (card_eq D.π hν) a)) * e t) := by
  rw [x, fx, cycGamma_gen, genImage, map_sum]
  simp only [cycLift_toC]

theorem cycGamma_ψ {j : ℕ} (h : j + 1 < Multiset.card ν) :
    Γ (ψ j) = ∑ t, Φ (crossImage D hν h t) := by
  rw [ψ, fψ, cycGamma_gen, genImage, dite_eq_left h, map_sum]

theorem cycGamma_e_mul_e {i : Seq ν} {t : Seq ν'} (ht : down D.π hν t = i) :
    Γ (e i) * E t = E t := by
  rw [cycGamma_e, Finset.sum_mul]
  simp only [cycMk_e_mul_e]
  rw [Finset.sum_ite_eq']
  simp [ht]

omit [DecidableEq I] in
theorem cycMk_e_mul_pol_e (t : Seq ν') (f : MvPolynomial (Fin m') k) :
    E t * cycMk D ν' M (pol f * e t) = cycMk D ν' M (pol f * e t) := by
  rw [← map_mul, ← mul_assoc, (e_commute_pol t f).eq, mul_assoc, e_mul_self]

theorem cycGamma_x_mul_e (a : Fin (Multiset.card ν)) (t : Seq ν') :
    Γ (x a) * E t = cycMk D ν' M (pol (substAt D.π D.pw hν t (X a)) * e t) := by
  rw [cycGamma_x, Finset.sum_mul]
  simp only [← map_mul, mul_assoc, e_mul_e]
  simp only [mul_ite, mul_zero, apply_ite (cycMk D ν' M), map_zero]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), substAt, aeval_X]

theorem cycGamma_pol_mul_e (f : MvPolynomial (Fin (Multiset.card ν)) k) (t : Seq ν') :
    Γ (pol f) * E t = cycMk D ν' M (pol (substAt D.π D.pw hν t f) * e t) := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    rw [algHom_C, AlgHom.commutes, algHom_C, AlgHom.commutes, map_mul, AlgHom.commutes]
  | add f g hf hg => rw [map_add, map_add, add_mul, hf, hg, map_add, map_add, add_mul, map_add]
  | mul_X f a hf =>
    have hE : ∀ g, (e t * (pol g * e t) : UnfKLR D ν') = pol g * e t := fun g => by
      rw [← mul_assoc, (e_commute_pol t g).eq, mul_assoc, e_mul_self]
    rw [map_mul, map_mul, pol_X, mul_assoc, cycGamma_x_mul_e, ← cycMk_e_mul_pol_e, ← mul_assoc,
      hf, ← map_mul, map_mul (substAt D.π D.pw hν t), map_mul (pol (Q := unfQ (k := k) D.arrows)),
      mul_assoc, hE, mul_assoc]

/-! ### Crossings -/

omit [DecidableEq I] in
/-- `e(t) ψ_j e(s)` is `ψ_j e(s)` if `s_j • s = t`, and zero otherwise. -/
theorem e_mul_ψ_mul_e (j : ℕ) (t s : Seq ν') :
    (e t * ψ j * e s : UnfKLR D ν') = if sadj m' j • s = t then ψ j * e s else 0 := by
  rw [mul_assoc, ψ_mul_e, ← mul_assoc, e_mul_e]
  split_ifs with h1 h2 h2
  · rw [h1]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rw [zero_mul]

theorem toC_e_mul_crossImage {j : ℕ} (h : j + 1 < Multiset.card ν) (t t' : Seq ν') :
    toC D (e t) * crossImage D hν h t' = if t = t' then crossImage D hν h t' else 0 := by
  unfold crossImage
  simp only
  split_ifs with hc hab htt htt htt
  · rw [← mul_assoc, serU, toCompletion_e_mul_seriesAt, ite_eq_left htt]
  · rw [← mul_assoc, serU, toCompletion_e_mul_seriesAt, ite_eq_right htt, zero_mul]
  · rw [← mul_assoc, serU, toCompletion_e_mul_seriesAt, ite_eq_left htt]
  · rw [← mul_assoc, serU, toCompletion_e_mul_seriesAt, ite_eq_right htt, zero_mul]
  · rw [← map_mul, ← mul_assoc, ← mul_assoc, (e_commute_pol t _).eq, mul_assoc _ (e t), htt,
      e_mul_self]
  · rw [← map_mul, ← mul_assoc, ← mul_assoc, (e_commute_pol t _).eq, mul_assoc _ (e t),
      e_mul_e, ite_eq_right htt, mul_zero, zero_mul, map_zero]

theorem e_mul_cycGamma_ψ {j : ℕ} (h : j + 1 < Multiset.card ν) (t : Seq ν') :
    E t * Γ (ψ j) = Φ (crossImage D hν h t) := by
  rw [cycGamma_ψ D harr hν hnd M hPQ h, Finset.mul_sum]
  have : ∀ t', E t * Φ (crossImage D hν h t') =
      if t = t' then Φ (crossImage D hν h t') else 0 := fun t' => by
    show cycMk D ν' M (e t) * _ = _
    rw [← cycLift_toC harr hnd M, ← map_mul, toC_e_mul_crossImage]
    split_ifs <;> simp
  simp only [this]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

include hnd in
omit [DecidableEq J] in
theorem sadj_smul_ne {j : ℕ} (h : j + 1 < m') (t : Seq ν') : sadj m' j • t ≠ t := by
  intro he
  have h1 : sadj m' j = 1 := NonInteracting.smul_left_injective hnd t (by rw [he, one_smul])
  have h2 := sadj_apply_left h
  rw [h1] at h2
  have := congrArg Fin.val h2
  simp at this

/-- The corner `e(t) Γ(ψ_j) e(s)`: an identity term (for strands of the same colour) and a
crossing term with a factor of nonzero constant term. -/
theorem corner_cycGamma_ψ {j : ℕ} (h : j + 1 < Multiset.card ν) (t : Seq ν') :
    ∃ c d : MvPolynomial (Fin m') k, constantCoeff c ≠ 0 ∧ ∀ s, E t * Γ (ψ j) * E s =
      (if s = t then cycMk D ν' M (pol d * e s) else 0) +
        (if sadj m' j • s = t then cycMk D ν' M (pol c * ψ j * e s) else 0) := by
  have h' := lt_card_of_lt D hν h
  rw [e_mul_cycGamma_ψ D harr hν hnd M hPQ h]
  unfold crossImage
  simp only
  split_ifs with hc hab
  · exact absurd hab (KLRAlgebra.lbl_ne_lbl_succ hnd t h')
  · set F := (↑(pwAt D.pw (t.lbl (posL D hν h)) (posL D hν h) -
        pwAt D.pw (t.lbl (posR D hν h)) (posR D hν h)) :
        MvPowerSeries (Fin m') k).invOfUnit
      (Units.mk0 ((D.pw (t.lbl (posL D hν h))).coeff 0 - (D.pw (t.lbl (posR D hν h))).coeff 0)
        (sub_ne_zero.2 fun e => hab (D.pw_coeff_zero_inj _ _ hc e)))
    refine ⟨-boxTrunc (M + 1) F, boxTrunc (M + 1) F, ?_, fun s => ?_⟩
    · rw [map_neg, constantCoeff_boxTrunc (Nat.succ_pos M), neg_ne_zero]
      simp only [F, MvPowerSeries.constantCoeff_invOfUnit]
      exact Units.ne_zero _
    · rw [map_mul, cycLift_serU D harr hnd M (N := M + 1) (by omega), cycLift_toC, ← map_mul,
        ← map_mul]
      have key : (pol (boxTrunc (M + 1) F) * e t * (e t - ψ j) * e s : UnfKLR D ν') =
          pol (boxTrunc (M + 1) F) * (e t * e t * e s) -
            pol (boxTrunc (M + 1) F) * (e t * ψ j * e s) := by noncomm_ring
      rw [key, e_mul_self, e_mul_e, e_mul_ψ_mul_e]
      by_cases h1 : s = t
      · subst h1
        simp only [sadj_smul_ne hnd h' s, ite_true, ite_false, mul_zero, sub_zero, add_zero]
      · have h1' : ¬t = s := fun e => h1 e.symm
        by_cases h2 : sadj m' j • s = t
        · simp only [h1, h1', h2, ite_true, ite_false, mul_zero, zero_sub, zero_add, map_neg,
            neg_mul, mul_assoc]
        · simp only [h1, h1', h2, ite_false, mul_zero, sub_zero, map_zero, add_zero]
  · refine ⟨rename ![posL D hν h, posR D hν h]
      (D.unit (t.lbl (posL D hν h)) (t.lbl (posR D hν h))), 0, ?_, fun s => ?_⟩
    · rw [constantCoeff_rename]; exact D.unit_constantCoeff _ _ hc
    · rw [cycLift_toC, ← map_mul]
      have key : ∀ g : MvPolynomial (Fin m') k, (pol g * e t * ψ j * e s : UnfKLR D ν') =
          pol g * (e t * ψ j * e s) := fun g => by noncomm_ring
      rw [key, e_mul_ψ_mul_e]
      by_cases h1 : s = t
      · subst h1
        simp only [sadj_smul_ne hnd h' s, ite_true, ite_false, mul_zero, zero_mul, map_zero,
          add_zero]
      · by_cases h2 : sadj m' j • s = t
        · simp only [h1, h2, ite_true, ite_false, map_zero, zero_mul, zero_add, mul_assoc]
        · simp only [h1, h2, ite_false, mul_zero, map_zero, add_zero]

theorem corner_cycGamma_ψ_eq_zero {j : ℕ} (h : j + 1 < Multiset.card ν) {t s : Seq ν'}
    (h1 : s ≠ t) (h2 : sadj m' j • s ≠ t) : E t * Γ (ψ j) * E s = 0 := by
  obtain ⟨c, d, -, hcd⟩ := corner_cycGamma_ψ D harr hν hnd M hPQ h t
  rw [hcd, ite_eq_right h1, ite_eq_right h2, add_zero]

theorem corner_cycGamma_ψ_lead {j : ℕ} (h : j + 1 < Multiset.card ν) (t : Seq ν') :
    ∃ c : MvPolynomial (Fin m') k, constantCoeff c ≠ 0 ∧
      E t * Γ (ψ j) * E (sadj m' j • t) = cycMk D ν' M (pol c * ψ j * e (sadj m' j • t)) := by
  obtain ⟨c, d, hc, hcd⟩ := corner_cycGamma_ψ D harr hν hnd M hPQ h t
  refine ⟨c, hc, ?_⟩
  rw [hcd, ite_eq_right (sadj_smul_ne hnd (lt_card_of_lt D hν h) t), zero_add, smul_smul,
    sadj_mul_self, one_smul, ite_eq_left rfl]

/-! ### Words of crossings -/

/-- **Lower terms vanish.** `e(u • s) Γ(ψ_σ) e(s) = 0` when `ℓ(u) ≥ |σ|` and `u ≠ w_σ`. -/
theorem corner_cycGamma_ψw_eq_zero {σ : List ℕ} (hσ : ValidWord m' σ) (s : Seq ν')
    {u : Perm (Fin m')} (hl : σ.length ≤ length m' u) (hu : u ≠ wordProd m' σ) :
    E (u • s) * Γ (ψw σ) * E s = 0 := by
  induction σ generalizing u with
  | nil =>
    rw [ψw_nil, map_one, mul_one, cycMk_e_mul_e, ite_eq_right]
    intro he
    exact hu (NonInteracting.smul_left_injective hnd s (by rw [he, wordProd_nil, one_smul]))
  | cons j σ ih =>
    have hj : j + 1 < m' := hσ j (by simp)
    have hv : ValidWord m' σ := fun l hl => hσ l (by simp [hl])
    have h : j + 1 < Multiset.card ν := by rw [card_eq D.π hν]; exact hj
    rw [ψw_cons, map_mul, ← mul_assoc, mul_assoc _ _ (E s), mul_eq_sum_e]
    refine Finset.sum_eq_zero fun s'' _ => ?_
    rw [← mul_assoc (E s'')]
    have hlen : length m' (wordProd m' σ) ≤ σ.length := length_wordProd_le hv
    simp only [List.length_cons] at hl
    by_cases h1 : s'' = u • s
    · rw [h1, ih hv (by omega) (fun he => by rw [he] at hl; omega), mul_zero]
    by_cases h2 : sadj m' j • s'' = u • s
    · have hs : s'' = (sadj m' j * u) • s := by
        rw [mul_smul, ← h2, smul_smul, sadj_mul_self, one_smul]
      have hl' := length_sadj_mul_le j (sadj m' j * u)
      rw [← mul_assoc, sadj_mul_self, one_mul] at hl'
      rw [hs, ih hv (by omega) (fun he => hu (by
        rw [wordProd_cons', ← he, ← mul_assoc, sadj_mul_self, one_mul])), mul_zero]
    · rw [corner_cycGamma_ψ_eq_zero D harr hν hnd M hPQ h h1 h2, zero_mul]

/-- **The leading term.** For a reduced word `σ`, `e(w_σ • s) Γ(ψ_σ) e(s) = ψ_σ U(y) e(s)` with
`U` of nonzero constant term. -/
theorem corner_cycGamma_ψw {σ : List ℕ} (hσ : IsReduced m' σ) (s : Seq ν') :
    ∃ U : MvPolynomial (Fin m') k, constantCoeff U ≠ 0 ∧
      E (wordProd m' σ • s) * Γ (ψw σ) * E s = cycMk D ν' M (ψw σ * pol U * e s) := by
  induction σ with
  | nil =>
    refine ⟨1, by simp, ?_⟩
    rw [ψw_nil, map_one, mul_one, wordProd_nil, one_smul, cycMk_e_mul_e, ite_eq_left rfl,
      ψw_nil, map_one, one_mul, one_mul]
  | cons j σ ih =>
    obtain ⟨hσ', hlen⟩ := PolyRep.Indep.isReduced_tail hσ
    have hj : j + 1 < m' := hσ.1 j (by simp)
    have h : j + 1 < Multiset.card ν := by rw [card_eq D.π hν]; exact hj
    obtain ⟨U', hU', hlead⟩ := ih hσ'
    set v := wordProd m' σ
    set t := (sadj m' j * v) • s
    have ht : sadj m' j • t = v • s := by rw [smul_smul, ← mul_assoc, sadj_mul_self, one_mul]
    obtain ⟨c, hc, hcl⟩ := corner_cycGamma_ψ_lead D harr hν hnd M hPQ h t
    rw [ht] at hcl
    refine ⟨rename ⇑(wordProd m' (j :: σ))⁻¹ c * U', ?_, ?_⟩
    · rw [map_mul, constantCoeff_rename]; exact mul_ne_zero hc hU'
    rw [wordProd_cons', ψw_cons, map_mul, ← mul_assoc, mul_assoc _ _ (E s), mul_eq_sum_e,
      Finset.sum_eq_single (v • s)]
    · rw [← mul_assoc (E (v • s)), hcl, hlead, ← map_mul]
      congr 1
      have hE : (e s * pol U' * e s : UnfKLR D ν') = pol U' * e s := by
        rw [(e_commute_pol s U').eq, mul_assoc, e_mul_self]
      have hP := pol_mul_ψw_of_nodup (Q := unfQ (k := k) D.arrows) hnd c (j :: σ)
      rw [wordProd_cons'] at hP
      calc pol c * ψ j * e (v • s) * (ψw σ * pol U' * e s)
          = pol c * ψ j * (e (v • s) * ψw σ) * pol U' * e s := by noncomm_ring
        _ = (pol c * ψw (j :: σ)) * (e s * pol U' * e s) := by
          rw [e_mul_ψw, inv_smul_smul, ψw_cons]; noncomm_ring
        _ = _ := by rw [hP, hE, map_mul]; noncomm_ring
    · intro s'' _ hs''
      rw [← mul_assoc (E s'')]
      by_cases h1 : s'' = t
      · rw [h1, corner_cycGamma_ψw_eq_zero D harr hν hnd M hPQ hσ'.1 s (u := sadj m' j * v)
          (by rw [hlen]; omega) (fun he => by
            have := congrArg (· • s) he
            exact sadj_smul_ne hnd hj (v • s) (by rw [smul_smul]; exact this)), mul_zero]
      · have h2 : sadj m' j • s'' ≠ t := fun he => hs'' (by
          rw [← he, smul_smul, sadj_mul_self, one_smul] at ht; exact ht)
        rw [corner_cycGamma_ψ_eq_zero D harr hν hnd M hPQ h h1 h2, zero_mul]
    · intro h0; exact absurd (Finset.mem_univ _) h0

/-! ### Triangularity -/

/-- `e(s) Γ(ψ_σ f(x) e(𝐢)) e(t) = e(s) Γ(ψ_σ) e(t) · f(ϖ_t(y)) e(t)` for a lift `t` of `𝐢`. -/
theorem corner_cycGamma_std {i : Seq ν} {t : Seq ν'} (ht : down D.π hν t = i) (s : Seq ν')
    (σ : List ℕ) (f : MvPolynomial (Fin (Multiset.card ν)) k) :
    E s * Γ (ψw σ * pol f * e i) * E t =
      E s * Γ (ψw σ) * E t * cycMk D ν' M (pol (substAt D.π D.pw hν t f) * e t) := by
  calc E s * Γ (ψw σ * pol f * e i) * E t = E s * Γ (ψw σ) * (Γ (pol f) * (Γ (e i) * E t)) := by
        rw [map_mul, map_mul]; noncomm_ring
    _ = _ := by
        rw [cycGamma_e_mul_e D harr hν hnd M hPQ ht, cycGamma_pol_mul_e, mul_assoc _ (E t),
          cycMk_e_mul_pol_e]

omit [DecidableEq I] in
include harr hnd in
/-- In the corner `e(w_σ • t) 𝖱^Λ(ν̃) e(t)`, `ψ_σ F(y) e(t) = 0` forces `F ∈ (y_a^M)` (the
corner basis `CycKLR.cornerBasis`). -/
theorem mem_boxIdeal_of_cycMk_eq_zero {σ : List ℕ} (hσ : IsReduced m' σ) (t : Seq ν')
    {F : MvPolynomial (Fin m') k} (hF : cycMk D ν' M (ψw σ * pol F * e t) = 0) :
    F ∈ boxIdeal (fun _ : Fin m' => (Polynomial.X ^ M : Polynomial k)) := by
  classical
  have hQ : ∀ i ∈ ν', ∀ j ∈ ν', i ≠ j → unfQ (k := k) D.arrows i j = 1 :=
    fun i _ j _ _ => unfQ_eq_one D harr i j
  have ha : ∀ j : J, ((fun _ : J => (Polynomial.X ^ M : Polynomial k)) j).Monic :=
    fun _ => Polynomial.monic_X_pow M
  obtain ⟨G, hG, hFG⟩ := exists_boxSupported_sub_mem
    (fun q : Fin m' => (fun _ : J => (Polynomial.X ^ M : Polynomial k)) (t.lbl q))
    (fun q => ha (t.lbl q)) F
  have h1 : cycMk D ν' M (pol (F - G) * e t) = 0 := CycKLR.mk_pol_mul_e_eq_zero hnd hQ t hFG
  have hG0 : cycMk D ν' M (ψw σ * pol G * e t) = 0 := by
    have : (ψw σ * pol F * e t : UnfKLR D ν') =
        ψw σ * pol G * e t + ψw σ * (pol (F - G) * e t) := by
      rw [map_sub]; noncomm_ring
    rw [this, map_add, map_mul (cycMk D ν' M) (ψw σ), h1, mul_zero, add_zero] at hF
    exact hF
  let w := wordProd m' σ
  let ρ' : Perm (Fin m') → List ℕ := fun v => if v = w then σ else (exists_reduced m' v).choose
  have hρ' : ∀ v, IsReduced m' (ρ' v) ∧ wordProd m' (ρ' v) = v := by
    intro v
    by_cases hv : v = w
    · simp only [ρ', hv, ite_true]; exact ⟨hσ, rfl⟩
    · simp only [ρ', hv, ite_false]; exact (exists_reduced m' v).choose_spec
  have hli := CycKLR.linearIndependent_cornerElt
    (a := fun _ : J => (Polynomial.X ^ M : Polynomial k)) hnd hQ ha ρ' hρ' t w
  have hρw : ρ' w = σ := by simp [ρ']
  have hGsum : G = ∑ c : CycKLR.DotExp (fun _ : J => (Polynomial.X ^ M : Polynomial k)) t,
      monomial (CycKLR.dotExp c) (G.coeff (CycKLR.dotExp c)) := by
    ext s
    rw [coeff_sum]
    simp only [coeff_monomial]
    by_cases hs : ∀ q, s q < ((fun _ : J => (Polynomial.X ^ M : Polynomial k)) (t.lbl q)).natDegree
    · let c0 : CycKLR.DotExp (fun _ : J => (Polynomial.X ^ M : Polynomial k)) t :=
        fun q => ⟨s q, hs q⟩
      have hc0 : CycKLR.dotExp c0 = s := Finsupp.ext fun q => rfl
      rw [Finset.sum_eq_single c0 (fun c _ hc => ite_eq_right (fun h =>
        hc (CycKLR.dotExp_injective (h.trans hc0.symm)))) (by simp), hc0, ite_eq_left rfl]
    · rw [Finset.sum_eq_zero fun c _ => ite_eq_right fun h => hs fun q => by
        rw [← h]; exact (c q).isLt]
      by_contra hne
      exact hs (hG s hne)
  have hsum : ∑ c, G.coeff (CycKLR.dotExp c) • CycKLR.cornerElt (Q := unfQ (k := k) D.arrows)
      (fun _ : J => (Polynomial.X ^ M : Polynomial k)) ρ' t w c = 0 := by
    rw [← hG0]
    conv_rhs => rw [hGsum]
    simp only [CycKLR.cornerElt, hρw, map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show monomial (CycKLR.dotExp c) (G.coeff (CycKLR.dotExp c)) =
        G.coeff (CycKLR.dotExp c) • monomial (CycKLR.dotExp c) (1 : k) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, mul_smul_comm, smul_mul_assoc, map_smul]
  have hc := Fintype.linearIndependent_iff.1 hli _ hsum
  have hG' : G = 0 := by
    rw [hGsum]
    exact Finset.sum_eq_zero fun c _ => by rw [hc c, monomial_zero]
  rw [hG', sub_zero] at hFG
  exact hFG

omit [DecidableEq I] [DecidableEq J] in
/-- For linear series `ϖ_j(x) = z_j + x`, the substitution is `x_a ↦ z_{t_a} + y_a`. -/
theorem substAt_eq_of_linear
    (hlin : ∀ j, D.pw j = Polynomial.C ((D.pw j).coeff 0) + Polynomial.X) (t : Seq ν') :
    substAt D.π D.pw hν t = aeval fun a =>
      C ((D.pw (t.lbl (Fin.cast (card_eq D.π hν) a))).coeff 0) +
        X (Fin.cast (card_eq D.π hν) a) := by
  unfold substAt
  congr 1
  funext a
  rw [pwAt]
  conv_lhs => rw [hlin]
  simp [MvPolynomial.algebraMap_eq]

/-- **Triangularity of `Γ` on one column** (Webster, arXiv:1603.06311v3, proof of the theorem
with label `nondegenerate`, the step showing that a relation acts by zero, for the KLR algebra).
Let `D` have no arrows (for instance `UnfurlingDatum.ofGeneric`; the series are arbitrary), let
the labels of `ν̃` be pairwise distinct, and let `t` lift `𝐢`. If
`Γ(∑_{(w,u) ∈ S} c_{w,u} ψ_{ρ w} x^u e(𝐢)) e(t) = 0` in the cyclotomic quotient with
`a_j = y^M`, for reduced words `ρ w` and exponents `u_a < M`, then every `c_{w,u}` vanishes.
Only the column `e(t)` is used: this is the morphism out of the summand `Ẽ_t 𝕍` of `E_𝐢 𝕍` in
the source. -/
theorem eq_zero_of_cycGamma_mul_e_eq_zero
    {i : Seq ν} {t : Seq ν'} (ht : down D.π hν t = i)
    (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
    (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)
    (S : Finset (Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)))
    (c : Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ) → k)
    (hS : ∀ p ∈ S, ∀ a, p.2 a < M)
    (h0 : Γ (∑ p ∈ S, c p • (ψw (ρ p.1) * pol (monomial p.2 1) * e i)) * E t = 0) :
    ∀ p ∈ S, c p = 0 := by
  classical
  have hm : Multiset.card ν = m' := card_eq D.π hν
  have hred : ∀ w, IsReduced m' (ρ w) := fun w => by rw [← hm]; exact (hρ w).1
  have hinj : ∀ w w', wordProd m' (ρ w) = wordProd m' (ρ w') → w = w' := by
    intro w w' h
    rw [← (hρ w).2, ← (hρ w').2]
    exact wordProd_eq_of_eq hm h
  by_contra hne
  obtain ⟨p1, hp1S, hp1⟩ : ∃ p ∈ S, c p ≠ 0 := by simpa using hne
  obtain ⟨p0, hp0, hmax⟩ := (S.filter fun p => c p ≠ 0).exists_max_image
    (fun p => (ρ p.1).length) ⟨p1, Finset.mem_filter.2 ⟨hp1S, hp1⟩⟩
  obtain ⟨hp0S, hp0c⟩ := Finset.mem_filter.1 hp0
  set w0 := wordProd m' (ρ p0.1)
  obtain ⟨U, hU, hlead⟩ := corner_cycGamma_ψw D harr hν hnd M hPQ (hred p0.1) t
  have hcorner : E (w0 • t) * Γ (∑ p ∈ S, c p • (ψw (ρ p.1) * pol (monomial p.2 1) * e i)) *
      E t = 0 := by rw [mul_assoc, h0, mul_zero]
  rw [map_sum, Finset.mul_sum, Finset.sum_mul] at hcorner
  simp only [map_smul, mul_smul_comm, smul_mul_assoc,
    corner_cycGamma_std D harr hν hnd M hPQ ht] at hcorner
  have hrest : ∀ p ∈ S.filter (fun p => ¬p.1 = p0.1), c p • (E (w0 • t) * Γ (ψw (ρ p.1)) * E t *
      cycMk D ν' M (pol (substAt D.π D.pw hν t (monomial p.2 1)) * e t)) = 0 := by
    intro p hp
    obtain ⟨hpS, hpne⟩ := Finset.mem_filter.1 hp
    by_cases hcp : c p = 0
    · rw [hcp, zero_smul]
    · have hl := hmax p (Finset.mem_filter.2 ⟨hpS, hcp⟩)
      rw [corner_cycGamma_ψw_eq_zero D harr hν hnd M hPQ (hred p.1).1 t (u := w0)
        (hl.trans (hred p0.1).2.le) (fun he => hpne (hinj _ _ he.symm)), zero_mul, smul_zero]
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p.1 = p0.1), Finset.sum_eq_zero hrest,
    add_zero] at hcorner
  have hS1 : ∀ p ∈ S.filter (fun p => p.1 = p0.1), c p • (E (w0 • t) * Γ (ψw (ρ p.1)) * E t *
      cycMk D ν' M (pol (substAt D.π D.pw hν t (monomial p.2 1)) * e t)) =
      c p • cycMk D ν' M (ψw (ρ p0.1) *
        pol (U * substAt D.π D.pw hν t (monomial p.2 1)) * e t) := by
    intro p hp
    have hE : ∀ g, (e t * (pol g * e t) : UnfKLR D ν') = pol g * e t := fun g => by
      rw [← mul_assoc, (e_commute_pol t g).eq, mul_assoc, e_mul_self]
    rw [(Finset.mem_filter.1 hp).2, hlead, ← map_mul, map_mul (pol (Q := unfQ (k := k) D.arrows)),
      mul_assoc _ (e t), hE]
    congr 2
    noncomm_ring
  rw [Finset.sum_congr rfl hS1] at hcorner
  set f := ∑ p ∈ S.filter (fun p => p.1 = p0.1), c p • monomial p.2 (1 : k) with hf
  have hcomb : cycMk D ν' M (ψw (ρ p0.1) * pol (U * substAt D.π D.pw hν t f) * e t) = 0 := by
    rw [← hcorner, hf]
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul, map_smul, mul_smul_comm, smul_mul_assoc]
  have h1 := mem_boxIdeal_of_cycMk_eq_zero D harr hnd M (hred p0.1) t hcomb
  have h2 := mem_of_mul_mem_boxIdeal hU h1
  have hboxf : ∀ s, f.coeff s ≠ 0 → ∀ a, s a < M := by
    intro s hs a
    rw [hf, coeff_sum] at hs
    obtain ⟨p, hp, hps⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    rw [coeff_smul, coeff_monomial] at hps
    split_ifs at hps with hpe
    · rw [← hpe]
      exact hS p (Finset.mem_filter.1 hp).1 a
    · simp at hps
  have hf0 := eq_zero_of_aeval_mem_boxIdeal hm (fun a => D.pw (t.lbl (Fin.cast hm a)))
    (fun a => D.pw_coeff_one _) hboxf h2
  have hcoeff : f.coeff p0.2 = 0 := by rw [hf0]; simp
  rw [hf, coeff_sum, Finset.sum_eq_single p0] at hcoeff
  · rw [coeff_smul, coeff_monomial, ite_eq_left rfl, smul_eq_mul, mul_one] at hcoeff
    exact hp0c hcoeff
  · intro p hp hne
    rw [coeff_smul, coeff_monomial, ite_eq_right fun he => hne (Prod.ext
      (Finset.mem_filter.1 hp).2 he), smul_zero]
  · intro hn
    exact (hn (Finset.mem_filter.2 ⟨hp0S, rfl⟩)).elim

/-- **Triangularity of `Γ`** (Webster, arXiv:1603.06311v3, proof of the theorem with label
`nondegenerate`, the step showing that a relation acts by zero, for the KLR algebra). Let `D` have no arrows
(the series are arbitrary), let the labels of `ν̃`
be pairwise distinct, and let `t` lift `𝐢`. If
`Γ(∑_{(w,u) ∈ S} c_{w,u} ψ_{ρ w} x^u e(𝐢)) = 0` in the cyclotomic quotient with `a_j = y^M`,
for reduced words `ρ w` and exponents `u_a < M`, then every `c_{w,u}` vanishes. -/
theorem eq_zero_of_cycGamma_eq_zero
    {i : Seq ν} {t : Seq ν'} (ht : down D.π hν t = i)
    (ρ : Perm (Fin (Multiset.card ν)) → List ℕ)
    (hρ : ∀ w, IsReduced (Multiset.card ν) (ρ w) ∧ wordProd (Multiset.card ν) (ρ w) = w)
    (S : Finset (Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ)))
    (c : Perm (Fin (Multiset.card ν)) × (Fin (Multiset.card ν) →₀ ℕ) → k)
    (hS : ∀ p ∈ S, ∀ a, p.2 a < M)
    (h0 : Γ (∑ p ∈ S, c p • (ψw (ρ p.1) * pol (monomial p.2 1) * e i)) = 0) :
    ∀ p ∈ S, c p = 0 :=
  eq_zero_of_cycGamma_mul_e_eq_zero D harr hν hnd M hPQ ht ρ hρ S c hS
    (by rw [h0, zero_mul])

end Categorification.KLR.Unfurling
