/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Flag.Cohomology

/-!
# Truncated polynomial rings, and ring maps out of `H_k` in bounded degree

Auxiliary material for the nondegeneracy argument of Khovanov–Lauda III (arXiv:0807.3250v1,
§6.4, TeX `sln-2008-ArXiv.tex` l. 9598–9790: "Injectivity is established by showing that for each
`M ∈ ℕ` there exists some large `N` such that … act by linearly independent operators").

KL III compare the cohomology rings `H_k` of partial flag varieties with polynomial rings "for
large `N`". We make this precise with ring maps out of `H_k` into a *truncated* polynomial ring:

* `highIdeal K w D` is the ideal of `K[σ]` spanned by the monomials of weight `> D` (for a weight
  function `w : σ → ℕ`), and `Tr K w D = K[σ] / highIdeal` is the truncated polynomial ring. A
  polynomial all of whose monomials have weight `≤ D` vanishes in `Tr` only if it is zero
  (`eq_zero_of_mkT_eq_zero`).
* `sc : Tr →ₐ Tr[t]` is the *grading series*: `sc (x) = ∑_n x_n t^n`, `x_n` the weight-`n` part of
  `x`; it is a ring map, and `(sc x).coeff n = 0` for `n > D` (`coeff_sc_of_lt`).
* `hLift`: given elements `x_0, …, x_{n-1} ∈ Tr` (the *total Chern classes* of the blocks) with
  augmentation `1` and `∏_j x_j = 1`, and block sizes `d_j ≥ D`, there is a `K`-algebra map
  `H_k → Tr` sending the generator `x(k)_{j,α}` of KL III (5.2) to the weight-`α` part of `x_j`
  (`hLift_x`) and the dual generator `x̄(k)_{j,α}` to the weight-`α` part of `∏_{j' ≠ j} x_{j'}`
  (`hLift_xbar`). This is the precise form of "in degrees `≤ D`, `H_k` is a polynomial ring".
-/

noncomputable section

namespace Categorification.Flag.Indep

open MvPolynomial

universe u

section Trunc

variable (K : Type u) [Field K] {σ : Type} (w : σ → ℕ) (D : ℕ)

/-- The ideal of `K[σ]` spanned by the monomials of weight `> D`. -/
def highIdeal : Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun s => monomial s (1 : K)) '' {s | D < Finsupp.weight w s})

/-- **The truncated polynomial ring** `K[σ] / (monomials of weight > D)`. -/
abbrev Tr : Type u := MvPolynomial σ K ⧸ highIdeal K w D

/-- The quotient map `K[σ] → Tr`. -/
def mkT : MvPolynomial σ K →ₐ[K] Tr K w D := Ideal.Quotient.mkₐ K _

variable {K w D}

theorem weight_mono {s t : σ →₀ ℕ} (h : s ≤ t) : Finsupp.weight w s ≤ Finsupp.weight w t := by
  obtain ⟨u, rfl⟩ := le_iff_exists_add.1 h
  rw [map_add]; exact Nat.le_add_right _ _

theorem mem_highIdeal_iff (p : MvPolynomial σ K) :
    p ∈ highIdeal K w D ↔ ∀ s ∈ p.support, D < Finsupp.weight w s := by
  rw [highIdeal, mem_ideal_span_monomial_image]
  refine ⟨fun h s hs => ?_, fun h s hs => ⟨s, h s hs, le_rfl⟩⟩
  obtain ⟨t, ht, hts⟩ := h s hs
  exact lt_of_lt_of_le ht (weight_mono hts)

theorem mkT_eq_zero_iff (p : MvPolynomial σ K) :
    mkT K w D p = 0 ↔ ∀ s ∈ p.support, D < Finsupp.weight w s := by
  rw [mkT, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, mem_highIdeal_iff]

/-- A polynomial whose monomials all have weight `≤ D` is zero if it vanishes in `Tr`. -/
theorem eq_zero_of_mkT_eq_zero {p : MvPolynomial σ K}
    (hp : ∀ s ∈ p.support, Finsupp.weight w s ≤ D) (h : mkT K w D p = 0) : p = 0 := by
  rw [mkT_eq_zero_iff] at h
  by_contra hne
  obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.1 hne)
  exact absurd (hp s hs) (not_le.2 (h s hs))

theorem mkT_surjective : Function.Surjective (mkT K w D) :=
  Ideal.Quotient.mkₐ_surjective K _

instance : Nontrivial (Tr K w D) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : mkT K w D 1 = 0 := by rw [map_one]; exact h.symm
  rw [mkT_eq_zero_iff] at h'
  have := h' 0 (MvPolynomial.mem_support_iff.2 (by simp))
  simp at this

/-! ### The grading series -/

variable (K w)

/-- The grading series on polynomials: `x_v ↦ x_v t^{w v}`. -/
def sc0 : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun v => Polynomial.C (X v) * Polynomial.X ^ w v

variable {K w}

theorem sc0_X (v : σ) : sc0 K w (X v) = Polynomial.C (X v) * Polynomial.X ^ w v := aeval_X _ _

theorem sc0_monomial (s : σ →₀ ℕ) (c : K) :
    sc0 K w (monomial s c) = Polynomial.C (monomial s c) * Polynomial.X ^ Finsupp.weight w s := by
  induction s using Finsupp.induction generalizing c with
  | zero =>
    rw [map_zero, pow_zero, mul_one, monomial_zero', sc0, aeval_C]
    rfl
  | single_add v e s _ _ ih =>
    rw [monomial_single_add, map_mul, ih, map_pow, sc0_X, map_mul, map_add,
      Finsupp.weight_single, smul_eq_mul, map_pow]
    ring

theorem coeff_sc0 (p : MvPolynomial σ K) (n : ℕ) :
    (sc0 K w p).coeff n = weightedHomogeneousComponent w n p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [sc0_monomial, Polynomial.coeff_C_mul_X_pow, weightedHomogeneousComponent_apply]
    by_cases hc : c = 0
    · subst hc; simp
    rw [support_monomial, ite_eq_right hc]
    by_cases hn : n = Finsupp.weight w s
    · subst hn
      simp [Finset.filter_singleton]
    · rw [ite_eq_right hn, Finset.filter_singleton, ite_eq_right (Ne.symm hn), Finset.sum_empty]
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, map_add]

theorem sc0_kill (a : MvPolynomial σ K) (ha : a ∈ highIdeal K w D) :
    Polynomial.mapAlgHom (mkT K w D) (sc0 K w a) = 0 := by
  ext n
  rw [Polynomial.coe_mapAlgHom, Polynomial.coeff_map, coeff_sc0, Polynomial.coeff_zero]
  change mkT K w D _ = 0
  rw [mkT_eq_zero_iff]
  intro s hs
  classical
  rw [MvPolynomial.mem_support_iff, coeff_weightedHomogeneousComponent] at hs
  split_ifs at hs with h
  · exact (mem_highIdeal_iff a).1 ha s (MvPolynomial.mem_support_iff.2 hs)
  · exact absurd rfl hs

variable (K w D)

/-- **The grading series** `sc : Tr → Tr[t]`, `x ↦ ∑_n x_n t^n`. -/
def sc : Tr K w D →ₐ[K] Polynomial (Tr K w D) :=
  Ideal.Quotient.liftₐ _ ((Polynomial.mapAlgHom (mkT K w D)).comp (sc0 K w)) fun a ha => by
    rw [AlgHom.comp_apply]; exact sc0_kill a ha

variable {K w D}

theorem sc_mkT (p : MvPolynomial σ K) :
    sc K w D (mkT K w D p) = (sc0 K w p).map (mkT K w D).toRingHom := rfl

theorem coeff_sc_mkT (p : MvPolynomial σ K) (n : ℕ) :
    (sc K w D (mkT K w D p)).coeff n = mkT K w D (weightedHomogeneousComponent w n p) := by
  rw [sc_mkT, Polynomial.coeff_map, coeff_sc0]; rfl

/-- The components of weight `> D` vanish in `Tr`. -/
theorem coeff_sc_of_lt (y : Tr K w D) {n : ℕ} (hn : D < n) : (sc K w D y).coeff n = 0 := by
  obtain ⟨p, rfl⟩ := mkT_surjective y
  rw [coeff_sc_mkT, mkT_eq_zero_iff]
  intro s hs
  have := weightedHomogeneousComponent_isWeightedHomogeneous (R := K) (w := w) n p
    (Finsupp.mem_support_iff.1 hs)
  rw [this]; exact hn

theorem natDegree_sc_le (y : Tr K w D) : (sc K w D y).natDegree ≤ D :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun n hn => coeff_sc_of_lt y (by exact_mod_cast hn)

theorem sc_X (v : σ) :
    sc K w D (mkT K w D (X v)) = Polynomial.C (mkT K w D (X v)) * Polynomial.X ^ w v := by
  rw [sc_mkT, sc0, aeval_X, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C]
  rfl

/-! ### Augmentation -/

theorem constantCoeff_kill (a : MvPolynomial σ K) (ha : a ∈ highIdeal K w D) :
    constantCoeff a = 0 := by
  by_contra h0
  have := (mem_highIdeal_iff a).1 ha 0 (MvPolynomial.mem_support_iff.2 h0)
  simp at this

variable (K w D)

/-- The augmentation `Tr → K` (the constant coefficient). -/
def aug : Tr K w D →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ (aeval fun _ => (0 : K)) fun a ha => by
    rw [aeval_zero', constantCoeff_kill a ha, map_zero]

variable {K w D}

theorem aug_mkT (p : MvPolynomial σ K) : aug K w D (mkT K w D p) = constantCoeff p := by
  change aeval (fun _ => (0 : K)) p = _
  rw [aeval_zero']; rfl

/-- For positive weights, the weight-`0` part of `y` is its augmentation. -/
theorem coeff_sc_zero (hw : ∀ v, 0 < w v) (y : Tr K w D) :
    (sc K w D y).coeff 0 = algebraMap K _ (aug K w D y) := by
  obtain ⟨p, rfl⟩ := mkT_surjective y
  rw [coeff_sc_mkT, weightedHomogeneousComponent_zero _ fun v => (hw v).ne', aug_mkT,
    ← constantCoeff_eq]
  rw [mkT, Ideal.Quotient.mkₐ_eq_mk]
  rfl

/-! ### Nilpotence of the augmentation ideal -/

/-- The polynomials all of whose monomials have weight `≥ k`. -/
def WeightGe (k : ℕ) (p : MvPolynomial σ K) : Prop := ∀ s ∈ p.support, k ≤ Finsupp.weight w s

omit [Field K] in
theorem WeightGe.mul [Field K] {k l : ℕ} {p q : MvPolynomial σ K} (hp : WeightGe (w := w) k p)
    (hq : WeightGe (w := w) l q) : WeightGe (w := w) (k + l) (p * q) := by
  classical
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul p q hs)
  rw [map_add]; exact Nat.add_le_add (hp a ha) (hq b hb)

theorem weightGe_pow {p : MvPolynomial σ K} (hp : WeightGe (w := w) 1 p) :
    ∀ n, WeightGe (w := w) n (p ^ n)
  | 0 => fun _ _ => Nat.zero_le _
  | n + 1 => by rw [pow_succ]; exact (weightGe_pow hp n).mul hp

/-- For positive weights, every element of augmentation `0` satisfies `y^{D+1} = 0`. -/
theorem pow_eq_zero_of_aug (hw : ∀ v, 0 < w v) {y : Tr K w D} (hy : aug K w D y = 0) :
    y ^ (D + 1) = 0 := by
  obtain ⟨p, rfl⟩ := mkT_surjective y
  rw [aug_mkT] at hy
  have h1 : WeightGe (w := w) 1 p := by
    intro s hs
    by_contra h
    have hs0 : s = 0 := by
      ext v
      by_contra hv
      apply h
      have : Finsupp.weight w (Finsupp.single v (s v)) ≤ Finsupp.weight w s :=
        weight_mono (Finsupp.single_le_iff.2 le_rfl)
      rw [Finsupp.weight_single, smul_eq_mul] at this
      have := hw v
      have : 1 ≤ s v := Nat.one_le_iff_ne_zero.2 hv
      nlinarith
    subst hs0
    exact (MvPolynomial.mem_support_iff.1 hs) hy
  rw [← map_pow, mkT_eq_zero_iff]
  intro s hs
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self D) (weightGe_pow h1 (D + 1) s hs)

/-- The inverse of `1 + y` for `y` of augmentation `0`: `∑_{f ≤ D} (-y)^f`. -/
def invOne (y : Tr K w D) : Tr K w D := ∑ f ∈ Finset.range (D + 1), (-y) ^ f

theorem one_add_mul_invOne (hw : ∀ v, 0 < w v) {y : Tr K w D} (hy : aug K w D y = 0) :
    (1 + y) * invOne y = 1 := by
  have h := mul_neg_geom_sum (-y) (D + 1)
  rw [sub_neg_eq_add, neg_pow y (D + 1), pow_eq_zero_of_aug hw hy, mul_zero, sub_zero] at h
  exact h

theorem aug_invOne (hw : ∀ v, 0 < w v) {y : Tr K w D} (hy : aug K w D y = 0) :
    aug K w D (invOne y) = 1 := by
  have h := congrArg (aug K w D) (one_add_mul_invOne hw hy)
  rwa [map_mul, map_add, hy, map_one, add_zero, one_mul] at h

end Trunc

/-! ## Ring maps out of `H_k` -/

section HLift

variable {K : Type u} [Field K] {σ : Type} {w : σ → ℕ} {D : ℕ} {n : ℕ}

/-- **Ring maps `H_k → Tr` from total Chern classes.** Given `x : Fin n → Tr` with augmentation
`1` (for positive weights: `(sc x_j)_0 = 1`) and `∏_j x_j = 1`, and block sizes `d_j ≥ D`, the
generator `x(k)_{j,α}` of KL III (5.2) is sent to the weight-`α` part of `x_j`. -/
def hLift (d : Fin n → ℕ) (hd : ∀ j, D ≤ d j) (x : Fin n → Tr K w D)
    (h0 : ∀ j, (sc K w D (x j)).coeff 0 = 1) (hprod : ∏ j, x j = 1) : H K d →ₐ[K] Tr K w D :=
  Ideal.Quotient.liftₐ _ (aeval fun g : Gen d => (sc K w D (x g.1)).coeff (g.2 + 1)) fun a ha => by
    have key : ∀ j, (blockSeries K d j).map
        (aeval fun g : Gen d => (sc K w D (x g.1)).coeff (g.2 + 1)).toRingHom = sc K w D (x j) := by
      intro j
      ext α
      rw [Polynomial.coeff_map, coeff_blockSeries]
      by_cases hα : α ≤ d j
      · rcases α with _ | a
        · rw [xgen_zero, map_one, h0]
        · rw [xgen_succ (by omega)]
          simp
      · rw [xgen_eq_zero (by omega), map_zero, coeff_sc_of_lt _ (by have := hd j; omega)]
    have htot : (totalSeries K d).map
        (aeval fun g : Gen d => (sc K w D (x g.1)).coeff (g.2 + 1)).toRingHom = 1 := by
      rw [totalSeries, Polynomial.map_prod]
      simp only [key]
      rw [← map_prod, hprod, map_one]
    refine Submodule.span_induction (p := fun a _ => (aeval fun g : Gen d =>
      (sc K w D (x g.1)).coeff (g.2 + 1)) a = 0) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨r, rfl⟩
      have := congrArg (fun p => Polynomial.coeff p (r + 1)) htot
      simp only [Polynomial.coeff_map, Polynomial.coeff_one, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe] at this
      rw [ite_eq_right (Nat.succ_ne_zero r)] at this
      exact this
    · exact map_zero _
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro c a _ ha; rw [smul_eq_mul, map_mul, ha, mul_zero]

variable (d : Fin n → ℕ) (hd : ∀ j, D ≤ d j) (x : Fin n → Tr K w D)
  (h0 : ∀ j, (sc K w D (x j)).coeff 0 = 1) (hprod : ∏ j, x j = 1)

theorem hLift_mkH (p : MvPolynomial (Gen d) K) :
    hLift d hd x h0 hprod (mkH K d p) =
      aeval (fun g : Gen d => (sc K w D (x g.1)).coeff (g.2 + 1)) p := rfl

/-- `x(k)_{j,α} ↦` the weight-`α` part of `x_j`, for every `α`. -/
theorem hLift_x (j : Fin n) (α : ℕ) :
    hLift d hd x h0 hprod (Flag.x K d j α) = (sc K w D (x j)).coeff α := by
  rw [Flag.x, hLift_mkH]
  by_cases hα : α ≤ d j
  · rcases α with _ | a
    · rw [xgen_zero, map_one, h0]
    · rw [xgen_succ (by omega)]; simp
  · rw [xgen_eq_zero (by omega), map_zero, coeff_sc_of_lt _ (by have := hd j; omega)]

/-- `x̄(k)_{j,α} ↦` the weight-`α` part of `∏_{j' ≠ j} x_{j'}`. -/
theorem hLift_xbar (j : Fin n) (α : ℕ) :
    hLift d hd x h0 hprod (Flag.xbar K d j α) =
      (sc K w D (∏ j' ∈ Finset.univ.erase j, x j')).coeff α := by
  have key : ∀ j, (blockSeries K d j).map
      (aeval fun g : Gen d => (sc K w D (x g.1)).coeff (g.2 + 1)).toRingHom = sc K w D (x j) := by
    intro j
    ext β
    rw [Polynomial.coeff_map, coeff_blockSeries]
    by_cases hβ : β ≤ d j
    · rcases β with _ | a
      · rw [xgen_zero, map_one, h0]
      · rw [xgen_succ (by omega)]
        simp
    · rw [xgen_eq_zero (by omega), map_zero, coeff_sc_of_lt _ (by have := hd j; omega)]
  rw [Flag.xbar, hLift_mkH, map_prod]
  have := congrArg (fun p => Polynomial.coeff p α)
    (Polynomial.map_prod (aeval fun g : Gen d => (sc K w D (x g.1)).coeff (g.2 + 1)).toRingHom
      (fun j' => blockSeries K d j') (Finset.univ.erase j))
  simp only [key, Polynomial.coeff_map] at this
  rw [dualSeries, ← this]; rfl

end HLift

end Categorification.Flag.Indep

end
