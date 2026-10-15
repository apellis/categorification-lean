/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Diagrams.KL3.EndOne
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Bubble values on generic level-one labels

Webster, *Unfurling Khovanov–Lauda–Rouquier algebras*, arXiv:1603.06311v3, proof of the
theorem with label `nondegenerate`: the bubbles act on the generating object of the
cyclotomic representation through symmetric functions of the independent values `z` carried
by the labels, and are therefore "generic". The source leaves this step implicit; this file
proves the algebraic independence that the field `bub_indep` of `UnfurledEval` asks for.

Setting: finitely many labels `J` with colours `π : J → I`, each of level one and carrying one
value `z_j ∈ L` (undeformed cyclotomic quotient `a = y^M`). For a colour `i` write
`e_r(i)`, `h_r(i)` for the elementary and complete symmetric functions of the values on the
labels over `i`, so that `∑_r (-1)^r e_r(i) t^r = ∏_{π j = i} (1 - z_j t)` and
`∑_r h_r(i) t^r` is its inverse.

## Main results

* `algebraicIndependent_esymmOver`: in `k[x_j : j ∈ J]`, the elementary symmetric
  polynomials `e_r` of the variables over each colour, `1 ≤ r ≤` (number of labels over it), are
  algebraically independent (all colours together; any field `k`). The proof is a transcendence
  degree count: they are `|J|` elements over which every `x_j` is integral.
* `algebraicIndependent_of_range_subset_adjoin`: `n` elements whose algebra contains `n`
  algebraically independent elements are algebraically independent.
* `algebraicIndependent_elemVal`: if the `z_j` are algebraically independent over `k` and every
  colour has at least `N` labels, the values `e_{n+1}(i)`, `n < N`, are algebraically
  independent.
* `bubValue`, `algebraicIndependent_bubValue`: the same for the values
  `ε_i^{n+1} e_{n+1}(i)` or `ε_i^{n+1} h_{n+1}(i)` (the choice of `e` or `h` and the nonzero
  scalars `ε_i ∈ k` may depend on the colour, to match the orientation and sign conventions of
  the bubbles).
* `bubEval`, `bubEval_indep`: the corresponding homomorphism `Π_λ → L`, with exactly the
  independence statement of the field `bub_indep` of `UnfurledEval`.
-/

open Cardinal

namespace Categorification.KLR.Unfurling

section Adjoin

variable {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]

/-- Finitely many elements whose generated algebra contains as many algebraically independent
elements are algebraically independent (a transcendence degree count). -/
theorem algebraicIndependent_of_range_subset_adjoin {ι : Type*} [Finite ι] {x y : ι → A}
    (hy : AlgebraicIndependent k y) (hyx : Set.range y ⊆ Algebra.adjoin k (Set.range x)) :
    AlgebraicIndependent k x := by
  set S := Algebra.adjoin k (Set.range x)
  let x' : ι → S := fun i => ⟨x i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let y' : ι → S := fun i => ⟨y i, hyx ⟨i, rfl⟩⟩
  have hy' : AlgebraicIndependent k y' := AlgebraicIndependent.of_comp S.val hy
  have htop : Algebra.adjoin k (Set.range x') = ⊤ := by
    apply Subalgebra.map_injective (f := S.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, ← Set.range_comp]
    rfl
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x')) S := by
    refine ⟨fun s => ?_⟩
    have hs : s ∈ Algebra.adjoin k (Set.range x') := htop ▸ Algebra.mem_top
    exact isAlgebraic_algebraMap (⟨s, hs⟩ : Algebra.adjoin k (Set.range x'))
  have hb := Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite k x'
    hy'.lift_cardinalMk_le_trdeg
  exact hb.1.map' (f := S.val) Subtype.val_injective

end Adjoin

section Polynomials

variable {I J : Type*} [Fintype J] [DecidableEq I] (π : J → I)

/-- The labels over the colour `i`. -/
def labelsOver (i : I) : Finset J := Finset.univ.filter (π · = i)

theorem mem_labelsOver {i : I} {j : J} : j ∈ labelsOver π i ↔ π j = i := by simp [labelsOver]

/-- The position of `j` among the labels over its colour. -/
noncomputable def labelRank (j : J) : ℕ :=
  ((labelsOver π (π j)).equivFin ⟨j, (mem_labelsOver π).2 rfl⟩ : ℕ)

theorem labelRank_eq (j : J) (i : I) (h : π j = i) :
    labelRank π j = ((labelsOver π i).equivFin ⟨j, (mem_labelsOver π).2 h⟩ : ℕ) := by
  subst h; rfl

/-- The label of position `r` over the colour `i`, for `r` below the number of labels over `i`. -/
noncomputable def labelOfRank (i : I) (r : ℕ) (hr : r < (labelsOver π i).card) : J :=
  (labelsOver π i).equivFin.symm ⟨r, hr⟩

theorem π_labelOfRank (i : I) (r : ℕ) (hr) : π (labelOfRank π i r hr) = i :=
  (mem_labelsOver π).1 ((labelsOver π i).equivFin.symm ⟨r, hr⟩).2

theorem labelRank_labelOfRank (i : I) (r : ℕ) (hr) :
    labelRank π (labelOfRank π i r hr) = r := by
  rw [labelRank_eq π _ i (π_labelOfRank π i r hr)]
  simp [labelOfRank]

variable (k : Type*) [Field k]

open MvPolynomial in
/-- The elementary symmetric polynomial of degree `r` in the variables over `i`. -/
noncomputable def esymmOver (i : I) (r : ℕ) : MvPolynomial J k :=
  ((labelsOver π i).val.map X).esymm r

open MvPolynomial in
/-- Each variable `x_j` is integral over the algebra generated by the `e_r` of the variables over
each colour: it is a root of `∏_{π j' = π j} (T - x_{j'})`. -/
theorem isIntegral_X_adjoin_esymmOver (j : J) :
    IsIntegral (Algebra.adjoin k (Set.range fun j => esymmOver π k (π j) (labelRank π j + 1)))
      (X j : MvPolynomial J k) := by
  set S := Algebra.adjoin k (Set.range fun j => esymmOver π k (π j) (labelRank π j + 1))
  set s : Multiset (MvPolynomial J k) := (labelsOver π (π j)).val.map X
  have key : ∀ r, r ≤ Multiset.card s → s.esymm r ∈ S := by
    intro r hr
    rcases r with _ | r
    · rw [Multiset.esymm_zero]; exact S.one_mem
    · have hr' : r < (labelsOver π (π j)).card := by
        simpa [s] using hr
      apply Algebra.subset_adjoin
      refine ⟨labelOfRank π (π j) r hr', ?_⟩
      simp only [labelRank_labelOfRank, π_labelOfRank, esymmOver, s]
  set p := (s.map fun t => Polynomial.X - Polynomial.C t).prod
  have hmon : p.Monic := Polynomial.monic_multiset_prod_of_monic _ _
    fun t _ => Polynomial.monic_X_sub_C t
  have hlifts : p ∈ Polynomial.lifts (algebraMap S (MvPolynomial J k)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨p.coeff n, ?_⟩, rfl⟩
    by_cases hn : n ≤ Multiset.card s
    · rw [Multiset.prod_X_sub_C_coeff s hn]
      exact S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) (key _ (Nat.sub_le _ _))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      · exact S.zero_mem
      · rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]; omega
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hmon
  refine ⟨q, hqm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hq, Polynomial.eval_multiset_prod]
  apply Multiset.prod_eq_zero
  rw [Multiset.map_map]
  refine Multiset.mem_map.2 ⟨X j, Multiset.mem_map_of_mem _ ?_, by simp⟩
  exact (labelsOver π (π j)).mem_def.1 ((mem_labelsOver π).2 rfl)

open MvPolynomial in
/-- The elementary symmetric polynomials of the variables over each colour, of degrees from `1`
to the number of variables over that colour, are algebraically independent. -/
theorem algebraicIndependent_esymmOver :
    AlgebraicIndependent k fun j : J => esymmOver π k (π j) (labelRank π j + 1) := by
  set S := Algebra.adjoin k (Set.range fun j => esymmOver π k (π j) (labelRank π j + 1))
  have hint : Algebra.IsIntegral S (MvPolynomial J k) := by
    refine ⟨fun a => ?_⟩
    have : (integralClosure S (MvPolynomial J k)).restrictScalars k = ⊤ := by
      rw [eq_top_iff, ← adjoin_range_X, Algebra.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      exact isIntegral_X_adjoin_esymmOver π k j
    have ha : a ∈ (integralClosure S (MvPolynomial J k)).restrictScalars k :=
      this ▸ Algebra.mem_top
    exact ha
  have := Algebra.IsIntegral.isAlgebraic (R := S) (A := MvPolynomial J k)
  refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite k _ ?_).1
  rw [MvPolynomial.trdeg_of_isDomain]
  simp


end Polynomials

section Values

variable {I J : Type*} [Fintype J] [DecidableEq I] (π : J → I) {k : Type*} [Field k]
  {L : Type*} [Field L] [Algebra k L]

/-- `e_r` of the values `z` on the labels over `i`. -/
noncomputable def elemVal (z : J → L) (i : I) (r : ℕ) : L :=
  ((labelsOver π i).val.map z).esymm r

/-- `∑_r (-1)^r e_r t^r = ∏_{π j = i} (1 - z_j t)`. -/
noncomputable def elemSeries (z : J → L) (i : I) : PowerSeries L :=
  PowerSeries.mk fun r => (-1) ^ r * elemVal π z i r

/-- `h_r` of the values `z` on the labels over `i`: the coefficients of
`∏_{π j = i} (1 - z_j t)⁻¹`. -/
noncomputable def compVal (z : J → L) (i : I) (r : ℕ) : L :=
  PowerSeries.coeff r (elemSeries π z i)⁻¹

theorem aeval_esymmOver (z : J → L) (i : I) (r : ℕ) :
    MvPolynomial.aeval z (esymmOver π k i r) = elemVal π z i r := by
  simp only [esymmOver, elemVal, Finset.esymm_map_val, map_sum, map_prod, MvPolynomial.aeval_X]

theorem compVal_zero (z : J → L) (i : I) : compVal π z i 0 = 1 := by
  simp [compVal, elemSeries, elemVal]

theorem sum_elemVal_mul_compVal (z : J → L) (i : I) (n : ℕ) :
    (-1) ^ (n + 1) * elemVal π z i (n + 1) +
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        (-1) ^ p.1 * elemVal π z i p.1 * compVal π z i (p.2 + 1) = 0 := by
  have h1 : elemSeries π z i * (elemSeries π z i)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by simp [elemSeries, elemVal])
  have := congrArg (PowerSeries.coeff (n + 1)) h1
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ'] at this
  change PowerSeries.coeff (n + 1) (elemSeries π z i) * compVal π z i 0 +
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 (elemSeries π z i) *
      compVal π z i (p.2 + 1) = PowerSeries.coeff (n + 1) 1 at this
  rw [compVal_zero, mul_one, PowerSeries.coeff_one] at this
  simp only [n.succ_ne_zero, ↓reduceIte] at this
  simpa only [elemSeries, PowerSeries.coeff_mk] using this

/-- The `e_r` over `i` lie in any subalgebra containing the `h_b`, `1 ≤ b ≤ r`. -/
theorem elemVal_mem_of_compVal_mem (z : J → L) (i : I) (T : Subalgebra k L) (n : ℕ)
    (hT : ∀ b, b ≤ n → compVal π z i (b + 1) ∈ T) :
    ∀ m ≤ n + 1, elemVal π z i m ∈ T := by
  intro m hm
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · simp [elemVal]
    · have h := sum_elemVal_mul_compVal π z i m
      have hs : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m,
          (-1) ^ p.1 * elemVal π z i p.1 * compVal π z i (p.2 + 1) ∈ T := by
        refine T.sum_mem fun p hp => ?_
        have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
        exact T.mul_mem (T.mul_mem (T.pow_mem (T.neg_mem T.one_mem) _)
          (ih _ (by omega) (by omega))) (hT _ (by omega))
      have he : elemVal π z i (m + 1) = -(-1) ^ (m + 1) *
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, (-1) ^ p.1 * elemVal π z i p.1 *
            compVal π z i (p.2 + 1) := by
        have hu : ((-1 : L) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
          rw [← mul_pow]; simp
        linear_combination (-1) ^ (m + 1) * h - elemVal π z i (m + 1) * hu
      rw [he]
      exact T.mul_mem (T.neg_mem (T.pow_mem (T.neg_mem T.one_mem) _)) hs


/-- Distinct pairs `(i, n)`, `n < N`, give distinct labels `labelOfRank π i n`. -/
theorem injective_labelOfRank {N : ℕ} (hN : ∀ i, N ≤ (labelsOver π i).card) :
    Function.Injective fun p : {p : I × ℕ // p.2 < N} =>
      labelOfRank π p.1.1 p.1.2 (lt_of_lt_of_le p.2 (hN _)) := by
  intro p q h
  have h1 := congrArg π h
  have h2 := congrArg (labelRank π) h
  simp only [π_labelOfRank, labelRank_labelOfRank] at h1 h2
  exact Subtype.ext (Prod.ext h1 h2)

/-- The `e_{n+1}(i)`, `n < N`, of algebraically independent values, when every colour has at
least `N` labels, are algebraically independent over `k`. -/
theorem algebraicIndependent_elemVal {z : J → L} (hz : AlgebraicIndependent k z) {N : ℕ}
    (hN : ∀ i, N ≤ (labelsOver π i).card) :
    AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} => elemVal π z p.1.1 (p.1.2 + 1) := by
  let φ : {p : I × ℕ // p.2 < N} → J := fun p =>
    labelOfRank π p.1.1 p.1.2 (lt_of_lt_of_le p.2 (hN _))
  have hφ : Function.Injective φ := injective_labelOfRank π hN
  have := ((algebraicIndependent_esymmOver π k).map'
    (f := MvPolynomial.aeval z) (algebraicIndependent_iff_injective_aeval.1 hz)).comp φ hφ
  convert this using 1
  funext p
  simp only [Function.comp_apply, φ, π_labelOfRank, labelRank_labelOfRank, aeval_esymmOver]

/-- The value of the bubble variable `(i, n)`: `ε_i^{n+1} e_{n+1}(i)` if `c i`, and
`ε_i^{n+1} h_{n+1}(i)` otherwise. -/
noncomputable def bubValue (c : I → Bool) (ε : I → k) (z : J → L) (p : I × ℕ) : L :=
  algebraMap k L (ε p.1) ^ (p.2 + 1) *
    if c p.1 then elemVal π z p.1 (p.2 + 1) else compVal π z p.1 (p.2 + 1)

/-- **The bubble values are algebraically independent** in the indices `< N`, when the `z_j`
are algebraically independent over `k`, every colour has at least `N` labels and the scalars
`ε_i` are nonzero (any characteristic). -/
theorem algebraicIndependent_bubValue (c : I → Bool) {ε : I → k} (hε : ∀ i, ε i ≠ 0)
    {z : J → L} (hz : AlgebraicIndependent k z) {N : ℕ}
    (hN : ∀ i, N ≤ (labelsOver π i).card) :
    AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} => bubValue π c ε z p.1 := by
  have : Finite {p : I × ℕ // p.2 < N} := .of_injective _ (injective_labelOfRank π hN)
  refine algebraicIndependent_of_range_subset_adjoin (algebraicIndependent_elemVal π hz hN) ?_
  rintro _ ⟨⟨⟨i, n⟩, hn⟩, rfl⟩
  set T := Algebra.adjoin k (Set.range fun p : {p : I × ℕ // p.2 < N} => bubValue π c ε z p.1)
  have hsym : ∀ b < N,
      (if c i then elemVal π z i (b + 1) else compVal π z i (b + 1)) ∈ T := by
    intro b hb
    have hx : bubValue π c ε z (i, b) ∈ T := Algebra.subset_adjoin ⟨⟨(i, b), hb⟩, rfl⟩
    have hu : algebraMap k L (ε i)⁻¹ ^ (b + 1) * bubValue π c ε z (i, b) ∈ T :=
      T.mul_mem (T.pow_mem (T.algebraMap_mem _) _) hx
    convert hu using 1
    simp only [bubValue, ← mul_assoc, ← mul_pow, ← map_mul, inv_mul_cancel₀ (hε i),
      map_one, one_pow, one_mul]
  cases hc : c i
  · refine elemVal_mem_of_compVal_mem π z i T n (fun b hb => ?_) _ le_rfl
    simpa [hc] using hsym b (by omega)
  · simpa [hc] using hsym n hn

/-- The action of the bubbles on the generating object: the variable `(i, n)` of `Π_λ` acts by
`bubValue`. -/
noncomputable def bubEval (c : I → Bool) (ε : I → k) (z : J → L) :
    KL3.Diagram.PiLam I k →ₐ[k] L :=
  MvPolynomial.aeval (bubValue π c ε z)

/-- `bubEval` satisfies the independence required by the field `bub_indep` of
`UnfurledEval`. -/
theorem bubEval_indep (c : I → Bool) {ε : I → k} (hε : ∀ i, ε i ≠ 0)
    {z : J → L} (hz : AlgebraicIndependent k z) {N : ℕ}
    (hN : ∀ i, N ≤ (labelsOver π i).card) :
    AlgebraicIndependent k fun p : {p : I × ℕ // p.2 < N} =>
      bubEval π c ε z (MvPolynomial.X p.1) := by
  simpa [bubEval] using algebraicIndependent_bubValue π c hε hz hN

end Values

end Categorification.KLR.Unfurling
