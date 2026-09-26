/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.Algebra.Graded.Tensor
import Categorification.Algebra.Graded.HomogeneousBasis

/-!
# Graded dimension of a tensor product; the tensor product of graded algebras

For `ℤ`-graded vector spaces `M = ⨁ ℳ i` and `N = ⨁ 𝒩 j` over a field `k`, with
finite-dimensional pieces vanishing in sufficiently negative degrees, the tensor product
`M ⊗[k] N` with the grading `tensorGrading ℳ 𝒩` (`(M ⊗ N)_d = ⨁_{i + j = d} M_i ⊗ N_j`) again has
a graded dimension, and

`gdim (M ⊗ N) = gdim M · gdim N`.

This is the identity `gdim (V ⊗ W) = gdim V gdim W` used throughout Khovanov–Lauda I
(arXiv:0803.4121v2, §2.5, §3.1), e.g. for the pairing on `K₀(R(ν) ⊗ R(ν'))`.

We also record that the tensor product grading of two graded algebras is a graded algebra
(`SetLike.GradedMonoid` instance `tensorGrading_gradedMonoid`), so that `A ⊗[k] B` with
`tensorGrading 𝒜 ℬ` carries the `K₀` and `HOM`-form constructions of
`Categorification.Algebra.Graded.K0` and `…HomForm`.

## Main results

* `Graded.tensorGrading_gradedMonoid`, `Graded.tensorGrading_gradedAlgebra` :
  `(A ⊗ B, tensorGrading 𝒜 ℬ)` is a graded algebra.
* `Graded.hasGdim_tensorGrading` : `HasGdim (tensorGrading ℳ 𝒩)`.
* `Graded.finrank_tensorGrading` : `dim (M ⊗ N)_d = ∑_{a ≤ i ≤ d - b} dim M_i · dim N_{d - i}`
  for lower bounds `a`, `b` of the gradings.
* `Graded.gdim_tensorGrading` : `gdim (M ⊗ N) = gdim M * gdim N`.
* `Graded.coeff_mul_eq_sum_Icc` : the coefficient formula for products of Laurent series whose
  supports are bounded below by `a` and `b`.

The proof uses the homogeneous basis of `M ⊗ N` obtained from homogeneous bases of `M` and `N`
(`DirectSum.IsInternal.collectedBasis`, `Basis.tensorProduct`).
-/

noncomputable section

namespace Categorification.Graded

open DirectSum Module
open scoped TensorProduct

/-! ### Graded algebras -/

section GradedAlgebra

variable {ι k A B : Type*} [AddCommMonoid ι] [CommRing k] [Ring A] [Algebra k A] [Ring B]
  [Algebra k B] (𝒜 : ι → Submodule k A) (ℬ : ι → Submodule k B)

/-- The tensor product grading of two graded algebras is multiplicative. -/
instance tensorGrading_gradedMonoid [SetLike.GradedMonoid 𝒜] [SetLike.GradedMonoid ℬ] :
    SetLike.GradedMonoid (tensorGrading 𝒜 ℬ) where
  one_mem := by
    have h := tmul_mem_tensorGrading (k := k) (SetLike.GradedOne.one_mem (A := 𝒜))
      (SetLike.GradedOne.one_mem (A := ℬ))
    rw [add_zero] at h
    exact h
  mul_mem i j x y hx hy := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i₁, i₂, a, b, rfl, ha, hb, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j₁, j₂, a', b', rfl, ha', hb', rfl⟩ := hy
        rw [Algebra.TensorProduct.tmul_mul_tmul, add_add_add_comm]
        exact tmul_mem_tensorGrading (SetLike.GradedMul.mul_mem ha ha')
          (SetLike.GradedMul.mul_mem hb hb')
      | zero => rw [mul_zero]; exact zero_mem _
      | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
      | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
    | zero => rw [zero_mul]; exact zero_mem _
    | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-- The tensor product of two graded algebras, graded by `tensorGrading`, is a graded algebra. -/
instance tensorGrading_gradedAlgebra [DecidableEq ι] [GradedAlgebra 𝒜] [GradedAlgebra ℬ] :
    GradedAlgebra (tensorGrading 𝒜 ℬ) where
  toGradedMonoid := tensorGrading_gradedMonoid 𝒜 ℬ
  toDecomposition := tensorDecomposition 𝒜 ℬ

end GradedAlgebra

/-! ### Coefficients of products of Laurent series -/

/-- The `q^d`-coefficient of a product of Laurent series supported in degrees `≥ a` and `≥ b`
is the finite sum `∑_{a ≤ i ≤ d - b} x_i y_{d - i}`. -/
theorem coeff_mul_eq_sum_Icc (x y : LaurentSeries ℤ) {a b : ℤ} (hx : ∀ i, x.coeff i ≠ 0 → a ≤ i)
    (hy : ∀ j, y.coeff j ≠ 0 → b ≤ j) (d : ℤ) :
    (x * y).coeff d = ∑ i ∈ Finset.Icc a (d - b), x.coeff i * y.coeff (d - i) := by
  classical
  rw [HahnSeries.coeff_mul]
  have hinj : Set.InjOn (fun i : ℤ => (i, d - i)) (Finset.Icc a (d - b) : Set ℤ) :=
    fun i _ j _ h => (Prod.mk.inj h).1
  rw [← Finset.sum_image (f := fun p : ℤ × ℤ => x.coeff p.1 * y.coeff p.2) hinj]
  refine Finset.sum_subset ?_ ?_
  · intro p hp
    rw [Finset.mem_addAntidiagonal] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    have ha := hx _ h1
    have hb := hy _ h2
    rw [Finset.mem_image]
    exact ⟨p.1, Finset.mem_Icc.2 ⟨ha, by omega⟩, Prod.ext rfl (by simp; omega)⟩
  · intro p _ hp
    by_contra h
    apply hp
    rw [Finset.mem_addAntidiagonal]
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 ‹p ∈ _›
    refine ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h, by simp⟩

/-! ### Graded dimension of a tensor product -/

section TensorGdim

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  (ℳ : ℤ → Submodule k M) (𝒩 : ℤ → Submodule k N) [Decomposition ℳ] [Decomposition 𝒩]
  [HasGdim ℳ] [HasGdim 𝒩]

/-- A homogeneous basis of `M`, collected from bases of the pieces. -/
def homBasis : Basis (Σ i : ℤ, Fin (finrank k (ℳ i))) k M :=
  (Decomposition.isInternal ℳ).collectedBasis fun i => Module.finBasis k (ℳ i)

theorem homBasis_mem (x : Σ i : ℤ, Fin (finrank k (ℳ i))) : homBasis ℳ x ∈ ℳ x.1 := by
  rw [homBasis, DirectSum.IsInternal.collectedBasis_coe]
  exact (Module.finBasis k (ℳ x.1) x.2).2

/-- The homogeneous basis `b_x ⊗ c_y` of `M ⊗ N`. -/
def tensorHomBasis :
    Basis ((Σ i : ℤ, Fin (finrank k (ℳ i))) × (Σ j : ℤ, Fin (finrank k (𝒩 j)))) k (M ⊗[k] N) :=
  (homBasis ℳ).tensorProduct (homBasis 𝒩)

omit [Decomposition ℳ] [Decomposition 𝒩] [HasGdim ℳ] [HasGdim 𝒩] in
/-- The degree `x.1 + y.1` of the basis element `b_x ⊗ c_y`. -/
def tensorHomDeg (p : (Σ i : ℤ, Fin (finrank k (ℳ i))) × (Σ j : ℤ, Fin (finrank k (𝒩 j)))) : ℤ :=
  p.1.1 + p.2.1

theorem tensorHomBasis_mem (p : (Σ i : ℤ, Fin (finrank k (ℳ i))) ×
    (Σ j : ℤ, Fin (finrank k (𝒩 j)))) :
    tensorHomBasis ℳ 𝒩 p ∈ tensorGrading ℳ 𝒩 (tensorHomDeg ℳ 𝒩 p) := by
  rw [tensorHomBasis, Basis.tensorProduct_apply]
  exact tmul_mem_tensorGrading (homBasis_mem ℳ p.1) (homBasis_mem 𝒩 p.2)

omit [Decomposition ℳ] [HasGdim ℳ] in
variable {ℳ} in
theorem le_of_finrank_ne_zero {a : ℤ} (ha : a ∈ lowerBounds {d | ℳ d ≠ ⊥}) {i : ℤ}
    (h : finrank k (ℳ i) ≠ 0) : a ≤ i := by
  refine ha fun hbot => h ?_
  rw [hbot]; exact finrank_bot k M

omit [Decomposition ℳ] [HasGdim ℳ] in
variable {ℳ} in
theorem le_of_fin {a : ℤ} (ha : a ∈ lowerBounds {d | ℳ d ≠ ⊥})
    (x : Σ i : ℤ, Fin (finrank k (ℳ i))) : a ≤ x.1 :=
  le_of_finrank_ne_zero ha (Fin.pos x.2).ne'

omit [Decomposition ℳ] [Decomposition 𝒩] [HasGdim ℳ] [HasGdim 𝒩] in
/-- The basis indices of degree `d`, parametrized by `a ≤ i ≤ d - b` and bases of `M_i`,
`N_{d - i}`. -/
def tensorHomDegMap (d : ℤ) {a b : ℤ} :
    (Σ i : Finset.Icc a (d - b), Fin (finrank k (ℳ i)) × Fin (finrank k (𝒩 (d - i)))) →
      {p | p ∈ Set.univ ∧ tensorHomDeg ℳ 𝒩 p = d} :=
  fun q => ⟨(⟨q.1, q.2.1⟩, ⟨d - q.1, q.2.2⟩), trivial, by simp [tensorHomDeg]⟩

omit [Decomposition ℳ] [Decomposition 𝒩] [HasGdim ℳ] [HasGdim 𝒩] in
theorem tensorHomDegMap_bijective {a b : ℤ} (ha : a ∈ lowerBounds {d | ℳ d ≠ ⊥})
    (hb : b ∈ lowerBounds {d | 𝒩 d ≠ ⊥}) (d : ℤ) :
    Function.Bijective (tensorHomDegMap ℳ 𝒩 d (a := a) (b := b)) := by
  constructor
  · rintro ⟨⟨i, hi⟩, x, y⟩ ⟨⟨i', hi'⟩, x', y'⟩ h
    simp only [tensorHomDegMap, Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.1 h1
    have hy := (Sigma.mk.inj_iff.1 h2).2
    rw [eq_of_heq hx, eq_of_heq hy]
  · rintro ⟨⟨⟨i, x⟩, ⟨j, y⟩⟩, -, hij⟩
    simp only [tensorHomDeg] at hij
    obtain rfl : j = d - i := by omega
    have hi : i ∈ Finset.Icc a (d - b) :=
      Finset.mem_Icc.2 ⟨le_of_fin ha ⟨i, x⟩, by
        have := le_of_fin hb ⟨d - i, y⟩; simp at this; omega⟩
    exact ⟨⟨⟨i, hi⟩, x, y⟩, rfl⟩

omit [Decomposition ℳ] [Decomposition 𝒩] [HasGdim ℳ] [HasGdim 𝒩] in
theorem finite_tensorHomDeg {a b : ℤ} (ha : a ∈ lowerBounds {d | ℳ d ≠ ⊥})
    (hb : b ∈ lowerBounds {d | 𝒩 d ≠ ⊥}) (d : ℤ) :
    {p | p ∈ Set.univ ∧ tensorHomDeg ℳ 𝒩 p = d}.Finite :=
  Set.finite_coe_iff.1
    (Finite.of_equiv _ (Equiv.ofBijective _ (tensorHomDegMap_bijective ℳ 𝒩 ha hb d)))

omit [Decomposition ℳ] [Decomposition 𝒩] [HasGdim ℳ] [HasGdim 𝒩] in
/-- The basis elements of `M ⊗ N` of degree `d` are counted by
`∑_{a ≤ i ≤ d - b} dim M_i · dim N_{d - i}`. -/
theorem card_tensorHomDeg_eq {a b : ℤ} (ha : a ∈ lowerBounds {d | ℳ d ≠ ⊥})
    (hb : b ∈ lowerBounds {d | 𝒩 d ≠ ⊥}) (d : ℤ) :
    Nat.card {p | p ∈ Set.univ ∧ tensorHomDeg ℳ 𝒩 p = d} =
      ∑ i ∈ Finset.Icc a (d - b), finrank k (ℳ i) * finrank k (𝒩 (d - i)) := by
  classical
  rw [← Nat.card_congr (Equiv.ofBijective _ (tensorHomDegMap_bijective ℳ 𝒩 ha hb d)),
    Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact Finset.sum_coe_sort (Finset.Icc a (d - b))
    (fun i => finrank k (ℳ i) * finrank k (𝒩 (d - i)))

theorem tensorGrading_eq_inf_span (d : ℤ) :
    tensorGrading ℳ 𝒩 d =
      tensorGrading ℳ 𝒩 d ⊓ Submodule.span k (tensorHomBasis ℳ 𝒩 '' Set.univ) := by
  rw [Set.image_univ, Basis.span_eq, inf_top_eq]

omit [Decomposition ℳ] [Decomposition 𝒩] [HasGdim ℳ] [HasGdim 𝒩] in
theorem bddBelow_tensorHomDeg {a b : ℤ} (ha : a ∈ lowerBounds {d | ℳ d ≠ ⊥})
    (hb : b ∈ lowerBounds {d | 𝒩 d ≠ ⊥}) :
    BddBelow (tensorHomDeg ℳ 𝒩 '' Set.univ) :=
  ⟨a + b, by
    rintro _ ⟨p, -, rfl⟩
    exact add_le_add (le_of_fin ha p.1) (le_of_fin hb p.2)⟩

/-- **The tensor product of graded vector spaces with graded dimensions has a graded
dimension.** -/
instance hasGdim_tensorGrading : HasGdim (tensorGrading ℳ 𝒩) := by
  obtain ⟨a, ha⟩ := HasGdim.bddBelow (ℳ := ℳ)
  obtain ⟨b, hb⟩ := HasGdim.bddBelow (ℳ := 𝒩)
  have h := hasGdim_inf_span (tensorGrading ℳ 𝒩) (tensorHomDeg ℳ 𝒩) (tensorHomBasis_mem ℳ 𝒩)
    Set.univ (finite_tensorHomDeg ℳ 𝒩 ha hb) (bddBelow_tensorHomDeg ℳ 𝒩 ha hb)
  have he : (fun d => tensorGrading ℳ 𝒩 d ⊓
      Submodule.span k (tensorHomBasis ℳ 𝒩 '' Set.univ)) = tensorGrading ℳ 𝒩 :=
    funext fun d => (tensorGrading_eq_inf_span ℳ 𝒩 d).symm
  rwa [he] at h

/-- `dim (M ⊗ N)_d = ∑_{a ≤ i ≤ d - b} dim M_i · dim N_{d - i}`. -/
theorem finrank_tensorGrading {a b : ℤ} (ha : a ∈ lowerBounds {d | ℳ d ≠ ⊥})
    (hb : b ∈ lowerBounds {d | 𝒩 d ≠ ⊥}) (d : ℤ) :
    finrank k (tensorGrading ℳ 𝒩 d) =
      ∑ i ∈ Finset.Icc a (d - b), finrank k (ℳ i) * finrank k (𝒩 (d - i)) := by
  have h := finrank_inf_span (tensorGrading ℳ 𝒩) (tensorHomDeg ℳ 𝒩)
    (tensorHomBasis ℳ 𝒩).linearIndependent (tensorHomBasis_mem ℳ 𝒩) Set.univ d
    (finite_tensorHomDeg ℳ 𝒩 ha hb d)
  rw [← tensorGrading_eq_inf_span] at h
  rw [h, card_tensorHomDeg_eq ℳ 𝒩 ha hb d]

/-- **`gdim (M ⊗ N) = gdim M · gdim N`.** -/
theorem gdim_tensorGrading : gdim (tensorGrading ℳ 𝒩) = gdim ℳ * gdim 𝒩 := by
  obtain ⟨a, ha⟩ := HasGdim.bddBelow (ℳ := ℳ)
  obtain ⟨b, hb⟩ := HasGdim.bddBelow (ℳ := 𝒩)
  ext d
  rw [coeff_gdim, finrank_tensorGrading ℳ 𝒩 ha hb d,
    coeff_mul_eq_sum_Icc (gdim ℳ) (gdim 𝒩) (a := a) (b := b) _ _ d]
  · push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_gdim, coeff_gdim]
  · intro i hi
    rw [coeff_gdim] at hi
    exact le_of_finrank_ne_zero ha (by exact_mod_cast hi)
  · intro j hj
    rw [coeff_gdim] at hj
    exact le_of_finrank_ne_zero hb (by exact_mod_cast hj)

end TensorGdim

end Categorification.Graded
