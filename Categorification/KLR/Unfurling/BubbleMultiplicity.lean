/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.KLR.Unfurling.BubbleValues

/-!
# Bubble values on labels with multiplicities

B. Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`. On the generating object of the representation used there,
the bubbles of the colour `i` act by the coefficients of a product
`∏_{π j = i} (1 - z_j t)^{m_j}`. Here `j` runs over the labels over `i` that occur in the
dominant weight, `z_j` is the value of the label, and the integer `m_j` is its level, with sign
`+` or `-` according to the side `Ĩ₊` or `Ĩ₋` of the label. The labels that carry strands have
level at least the number of bubble variables in play, so multiplicities `> 1` occur.

This file shows that the first coefficients of these products are algebraically independent. The
hypotheses are that the values `z_j` are algebraically independent and that every colour has
enough labels of level one, all with the same sign. The proof specializes the values of the other
labels to `0` and reduces to the level-one case `algebraicIndependent_bubValue` (any
characteristic).

## Main definitions and results

* `oneSubUnit a`: the unit `1 - a t` of `R⟦t⟧`.
* `multSeries π m z i = ∏_{π j = i} (1 - z_j t)^{m_j}` and its coefficients `multVal`.
* `algebraicIndependent_multVal`: the coefficients `multVal π m z i (n + 1)`, `n < N`, are
  algebraically independent over `k`.
-/

open PowerSeries

namespace Categorification.KLR.Unfurling

section Series

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The unit `1 - a t` of `R⟦t⟧`. -/
noncomputable def oneSubUnit (a : R) : (PowerSeries R)ˣ :=
  (isUnit_iff_constantCoeff.2 (by simp) : IsUnit (1 - C a * X : PowerSeries R)).unit

@[simp] theorem coe_oneSubUnit (a : R) : (oneSubUnit a : PowerSeries R) = 1 - C a * X := rfl

theorem map_oneSubUnit (f : R →+* S) (a : R) :
    Units.map (map f : PowerSeries R →* PowerSeries S) (oneSubUnit a) = oneSubUnit (f a) := by
  ext1
  simp [map_C, map_X]

@[simp] theorem oneSubUnit_zero : oneSubUnit (0 : R) = 1 := by
  ext1
  simp

variable {I J : Type*} [Fintype J] [DecidableEq I] (π : J → I)

/-- `∏_{π j = i} (1 - z_j t)^{m_j}`. -/
noncomputable def multSeries (m : J → ℤ) (z : J → R) (i : I) : PowerSeries R :=
  ((∏ j ∈ labelsOver π i, oneSubUnit (z j) ^ m j : (PowerSeries R)ˣ) : PowerSeries R)

/-- The coefficient of `t^r` in `∏_{π j = i} (1 - z_j t)^{m_j}`. -/
noncomputable def multVal (m : J → ℤ) (z : J → R) (i : I) (r : ℕ) : R :=
  coeff r (multSeries π m z i)

theorem map_multSeries (f : R →+* S) (m : J → ℤ) (z : J → R) (i : I) :
    map f (multSeries π m z i) = multSeries π m (f ∘ z) i := by
  have h := congrArg Units.val
    (map_prod (Units.map (map f : PowerSeries R →* PowerSeries S))
      (fun j => oneSubUnit (z j) ^ m j) (labelsOver π i))
  simp only [map_zpow, map_oneSubUnit, Units.coe_map, MonoidHom.coe_coe] at h
  simpa only [multSeries, Function.comp_apply] using h

theorem map_multVal (f : R →+* S) (m : J → ℤ) (z : J → R) (i : I) (r : ℕ) :
    f (multVal π m z i r) = multVal π m (f ∘ z) i r := by
  rw [multVal, multVal, ← map_multSeries, coeff_map]

omit [Fintype J] in
/-- `∏_{j ∈ s} (1 - z_j t) = ∑_r (-1)^r e_r(z_s) t^r`. -/
theorem prod_oneSubUnit_eq_mk (s : Finset J) (z : J → R) :
    ((∏ j ∈ s, oneSubUnit (z j) : (PowerSeries R)ˣ) : PowerSeries R) =
      mk fun r => (-1) ^ r * (s.val.map z).esymm r := by
  classical
  rw [Units.coe_prod]
  simp only [coe_oneSubUnit, sub_eq_add_neg, Finset.prod_one_add]
  ext r
  rw [map_sum, coeff_mk, Finset.esymm_map_val, Finset.mul_sum]
  have hterm : ∀ t ∈ s.powerset, coeff r (∏ j ∈ t, -(C (z j) * X)) =
      if t.card = r then (-1) ^ r * ∏ j ∈ t, z j else 0 := by
    intro t _
    rw [show (∏ j ∈ t, -(C (z j) * X) : PowerSeries R) =
        C ((-1) ^ t.card * ∏ j ∈ t, z j) * X ^ t.card by
      rw [Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const, map_mul, map_pow,
        map_neg, map_one, map_prod]
      ring]
    rw [coeff_C_mul_X_pow]
    by_cases h : r = t.card
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.powersetCard_eq_filter]

end Series

section Independence

variable {I J : Type*} [Fintype J] [DecidableEq I] (π : J → I) {k : Type*} [Field k]
  {L : Type*} [Field L] [Algebra k L]

/-- For labels of level one and sign `c`, the coefficients of `∏ (1 - z_j t)^{±1}` are the
values `bubValue` with the scalars `ε_i = -1` (sign `+`) and `ε_i = 1` (sign `-`). -/
theorem multVal_eq_bubValue {m : J → ℤ} (c : I → Bool) (z : J → L)
    (hm : ∀ j, m j = if c (π j) then 1 else -1) (p : I × ℕ) :
    multVal π m z p.1 (p.2 + 1) =
      bubValue π c (fun i => if c i then (-1 : k) else 1) z p := by
  obtain ⟨i, n⟩ := p
  set u : (PowerSeries L)ˣ := ∏ j ∈ labelsOver π i, oneSubUnit (z j)
  have he : (u : PowerSeries L) = elemSeries π z i := by
    rw [prod_oneSubUnit_eq_mk]
    rfl
  have hprod : (∏ j ∈ labelsOver π i, oneSubUnit (z j) ^ m j : (PowerSeries L)ˣ) =
      u ^ (if c i then (1 : ℤ) else -1) := by
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hm j, (mem_labelsOver π).1 hj]
  have hc0 : constantCoeff (u : PowerSeries L) ≠ 0 :=
    (isUnit_iff_constantCoeff.1 u.isUnit).ne_zero
  simp only [multVal, multSeries, hprod, bubValue]
  cases hci : c i
  · have hinv : ((u ^ (-1 : ℤ) : (PowerSeries L)ˣ) : PowerSeries L) = (elemSeries π z i)⁻¹ := by
      rw [← he, eq_inv_iff_mul_eq_one hc0, zpow_neg_one, Units.inv_mul]
    simp only [Bool.false_eq_true, ↓reduceIte, hinv, map_one, one_pow, one_mul, compVal]
  · simp only [↓reduceIte, zpow_one, he, elemSeries, coeff_mk, map_neg, map_one]

variable (m : J → ℤ)

/-- **The coefficients of `∏_{π j = i} (1 - z_j t)^{m_j}` are generic.** Suppose the values `z_j`
are algebraically independent over `k`, and every colour has at least `N` labels in `G`, where
`G` is a set of labels of level `m_j = ±1` whose sign `c` depends only on the colour. Then the
coefficients of `t^{n+1}`, `n < N`, over all colours are algebraically independent over `k`
(any characteristic). -/
theorem algebraicIndependent_multVal {z : J → L} (hz : AlgebraicIndependent k z) (G : Finset J)
    (c : I → Bool) (hG : ∀ j ∈ G, m j = if c (π j) then 1 else -1) {N : ℕ}
    (hN : ∀ i, N ≤ (labelsOver (fun j : G => π j) i).card) :
    AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} => multVal π m z p.1.1 (p.1.2 + 1) := by
  classical
  let x' : {p : I × ℕ // p.2 < N} → MvPolynomial J k := fun p =>
    multVal π m (MvPolynomial.X : J → MvPolynomial J k) p.1.1 (p.1.2 + 1)
  have hx : (fun p : {p : I × ℕ // p.2 < N} => multVal π m z p.1.1 (p.1.2 + 1)) =
      MvPolynomial.aeval (R := k) z ∘ x' := by
    funext p
    simp only [Function.comp_apply, x']
    rw [← AlgHom.coe_toRingHom, map_multVal]
    congr 1
    funext j
    simp
  rw [hx]
  refine AlgebraicIndependent.map' ?_ (algebraicIndependent_iff_injective_aeval.1 hz)
  let zG : J → L := fun j => if j ∈ G then z j else 0
  refine AlgebraicIndependent.of_comp (MvPolynomial.aeval (R := k) zG) ?_
  have hsub : ∀ i, (labelsOver (fun j : G => π j) i).map (Function.Embedding.subtype _) =
      (labelsOver π i).filter (· ∈ G) := by
    intro i
    ext j
    simp only [Finset.mem_map, mem_labelsOver, Finset.mem_filter, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨j', hj', rfl⟩
      exact ⟨hj', j'.2⟩
    · rintro ⟨hj, hjG⟩
      exact ⟨⟨j, hjG⟩, hj, rfl⟩
  have hval : ∀ i r, multVal π m zG i r =
      multVal (fun j : G => π j) (fun j => m j) (fun j => z j) i r := by
    intro i r
    simp only [multVal, multSeries]
    congr 2
    rw [← Finset.prod_filter_of_ne (p := (· ∈ G)) (fun j _ h => by
      by_contra hj
      simp [zG, hj] at h), ← hsub, Finset.prod_map]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [zG, j.2]
  have hcomp : (MvPolynomial.aeval (R := k) zG) ∘ x' = fun p =>
      bubValue (fun j : G => π j) c (fun i => if c i then (-1 : k) else 1) (fun j => z j) p.1 := by
    funext p
    simp only [Function.comp_apply, x']
    rw [← AlgHom.coe_toRingHom, map_multVal]
    have : ⇑(↑(MvPolynomial.aeval (R := k) zG) : MvPolynomial J k →+* L) ∘ MvPolynomial.X =
        zG := by
      funext j
      simp
    rw [this, hval]
    exact multVal_eq_bubValue _ c _ (fun j : G => hG j.1 j.2) p.1
  rw [hcomp]
  refine algebraicIndependent_bubValue _ c (fun i => ?_) (hz.comp _ Subtype.val_injective) hN
  split_ifs <;> simp

end Independence

end Categorification.KLR.Unfurling
