/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Basis

/-!
# The basis theorem for Webster's weighted KLR algebra

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, Theorem 2.8 (the
basis theorem), for Webster's algebra itself.

Webster's weighted KLR algebra has an idempotent for each (equivalence class of) loading, that
is, for each rank-ordered chamber. The gallery algebra `GalleryAlgebra k Γ ν` has an idempotent
`e C` for every full chamber `C`, including those in which strands of one colour are out of rank
order; Webster's algebra is here its corner over the rank-ordered chambers:

  `weightedKLR k Γ ν = eB * GalleryAlgebra k Γ ν * eB`, `eB = ∑_{C rank-ordered} e C`,

with `e D * GalleryAlgebra k Γ ν * e C` (`cornerSpace D C`) the space of diagrams from the
loading `C` at the bottom to the loading `D` at the top. As a ring, it is Mathlib's corner
`IsIdempotentElem.Corner` of `eB` (`WeightedKLRAlgebra`, `mem_weightedKLR_iff_mem_corner`).

## Translation of the basis to Webster's indexing

The basis of the gallery algebra (`basisOfSegments`) consists of the elements
`r g E * segGallery P C E * poly (y^m)`: the straight-line gallery from `C` to `E`, during which
strands keep their labels, followed by the relabelling `g : C → g • E`. Since
`e D' * (r g E * segGallery P C E * poly (y^m)) * e C'` is this element if `D' = g • E` and
`C' = C` and `0` otherwise (`e_mul_basisElt_mul_e`), the corner `e D * A * e C` has the basis of
the elements with bottom chamber `C` and `g • E = D`. For given `C`, `D` and `g` there is exactly
one such `E`, namely `g⁻¹ • D`, so the basis of `e D * A * e C` is indexed by the
colour-preserving permutations `g` and the monomials `m` (`cornerBasis`):

  `b(g, m) = r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)`.

A strand is a pair `(i, a)`: colour `i` and rank `a` among the strands of colour `i`. In the
rank-ordered chamber `C` at the bottom, strand `(i, a)` is the `a`-th strand of colour `i` from
the left. Along the gallery it keeps its label; relabelling by `g` puts `g (i, a)` where `(i, a)`
was (`act g p = p ∘ g⁻¹`). In the rank-ordered chamber `D` at the top, strand `(i, b)` is the
`b`-th strand of colour `i` from the left. So the strand that starts as the `a`-th strand of
colour `i` at the bottom ends as the `(g (i, a)).2`-th strand of colour `i` at the top. Webster's
permutation `π` (strand starting at position `j` of the bottom loading ends at position `π(j)`
of the top loading) is therefore `g` read through the identification of the positions of a
loading with pairs (colour, rank within the colour): `π` is colour preserving, and every
colour-preserving `π` arises from exactly one `g`. The basis element `b(g, m)` is Webster's
`b_π y^m`: Webster's fixed diagram `b_π` wiring the two loadings according to `π` (here the
straight-line gallery, which fixes a choice of `b_π`), with the monomial `y^m` in the dots at the
bottom. Webster states Theorem 2.8 as: `e_i W e_j` is a free module over `k[y_1, …, y_m]` with
free basis the `b_π`, without naming the side; `cornerPolyEquiv` proves it for the action of the
polynomials at the bottom (right multiplication), and `cornerBasis` is the resulting `k`-basis.

The hypotheses are those of `basisOfSegments`: Webster's condition (†), no loops of weight `0`,
symmetric loop polynomials, and wall and loop polynomials that are non-zero-divisors; `P` is any
choice of simple segments between the full chambers.

Rank-ordered full chambers are the image of Webster's chambers `Chamber Γ ν` under the injective
map `Chamber.toFull`; `chamberBasis` states the block form for `c d : Chamber Γ ν`. The basis of
the whole algebra (`weightedKLRBasis`) is indexed by rank-ordered full chambers (Webster's
loadings, bottom and top), colour-preserving permutations and monomials.

## Main definitions

* `GalleryAlgebra.cornerSpace D C`: the space `e D * A * e C`.
* `GalleryAlgebra.rankIdem`: the idempotent `∑_{C rank-ordered} e C`.
* `GalleryAlgebra.weightedKLR`, `GalleryAlgebra.WeightedKLRAlgebra`: Webster's algebra, as a
  submodule and as a ring.

## Main results

* `GalleryAlgebra.cornerBasis`: the basis of `e D * A * e C`, indexed by `(g, m)`.
* `GalleryAlgebra.chamberBasis`: the same for Webster's chambers.
* `GalleryAlgebra.weightedKLRBasis`: the basis of Webster's algebra.
* `GalleryAlgebra.cornerPolyEquiv`: `e D * A * e C` is free as a right module over the
  polynomials in the dots, on the elements `b(g, 1)`.
-/

namespace Categorification.WeightedKLR

open MvPolynomial FullChamber Segment

/-! ### Ranges of projections fixing part of a basis -/

section Projection

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem span_basis_fixed_eq_range (b : Module.Basis ι R M) (π : M →ₗ[R] M) (p : ι → Prop)
    [DecidablePred p] (h : ∀ i, π (b i) = if p i then b i else 0) :
    Submodule.span R (Set.range (b ∘ Subtype.val : {i // p i} → M)) = LinearMap.range π := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    exact ⟨b i, by rw [h, ite_eq_left_iff.2 fun h' => (h' hi).elim]; rfl⟩
  · rw [LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [h]
    split_ifs with hi
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · exact Submodule.zero_mem _

/-- If a linear map sends each vector of a basis either to itself or to zero, its range has the
basis of the fixed vectors. -/
noncomputable def basisRangeOfApply (b : Module.Basis ι R M) (π : M →ₗ[R] M) (p : ι → Prop)
    [DecidablePred p] (h : ∀ i, π (b i) = if p i then b i else 0) :
    Module.Basis {i // p i} R (LinearMap.range π) :=
  (Module.Basis.span (b.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (span_basis_fixed_eq_range b π p h))

@[simp]
theorem basisRangeOfApply_apply (b : Module.Basis ι R M) (π : M →ₗ[R] M) (p : ι → Prop)
    [DecidablePred p] (h : ∀ i, π (b i) = if p i then b i else 0) (i : {i // p i}) :
    (basisRangeOfApply b π p h i : M) = b i := by
  simp [basisRangeOfApply, Module.Basis.span_apply]

end Projection

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

/-! ### Corners -/

variable (k) in
/-- The linear map `x ↦ a * x * b`. -/
noncomputable def sandwich (a b : GalleryAlgebra k Γ ν) :
    GalleryAlgebra k Γ ν →ₗ[k] GalleryAlgebra k Γ ν :=
  LinearMap.mulLeft k a ∘ₗ LinearMap.mulRight k b

@[simp]
theorem sandwich_apply (a b x : GalleryAlgebra k Γ ν) : sandwich k a b x = a * x * b := by
  simp [sandwich, mul_assoc]

variable (k) in
/-- The space `e D * A * e C` of elements from the full chamber `C` (bottom) to the full chamber
`D` (top). -/
noncomputable abbrev cornerSpace (D C : FullChamber Γ ν) : Submodule k (GalleryAlgebra k Γ ν) :=
  LinearMap.range (sandwich k (e D) (e C))

theorem mem_cornerSpace_iff {D C : FullChamber Γ ν} {x : GalleryAlgebra k Γ ν} :
    x ∈ cornerSpace k D C ↔ e D * x * e C = x := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [sandwich_apply, ← mul_assoc, ← mul_assoc, e_mul_e, ite_eq_left rfl, mul_assoc _ _ (e C),
      mul_assoc _ _ (e C), e_mul_e, ite_eq_left rfl, ← mul_assoc]
  · intro h; exact ⟨x, by rw [sandwich_apply, h]⟩

variable (k Γ ν) in
/-- The idempotent `∑_{C rank-ordered} e C` of Webster's algebra. -/
noncomputable def rankIdem : GalleryAlgebra k Γ ν :=
  ∑ C ∈ Finset.univ.filter FullChamber.IsRankOrdered, e C

theorem rankIdem_mul_e (C : FullChamber Γ ν) :
    (rankIdem k Γ ν * e C : GalleryAlgebra k Γ ν) = if C.IsRankOrdered then e C else 0 := by
  simp only [rankIdem, Finset.sum_mul, e_mul_e]
  rw [Finset.sum_ite_eq']
  simp

theorem e_mul_rankIdem (C : FullChamber Γ ν) :
    (e C * rankIdem k Γ ν : GalleryAlgebra k Γ ν) = if C.IsRankOrdered then e C else 0 := by
  simp only [rankIdem, Finset.mul_sum, e_mul_e]
  rw [Finset.sum_ite_eq]
  simp

theorem isIdempotentElem_rankIdem : IsIdempotentElem (rankIdem k Γ ν) := by
  unfold IsIdempotentElem
  nth_rw 2 [rankIdem]
  rw [Finset.mul_sum]
  simp only [rankIdem_mul_e]
  exact Finset.sum_congr rfl fun C hC =>
    ite_eq_left_iff.2 fun h => (h (Finset.mem_filter.1 hC).2).elim

variable (k Γ ν) in
/-- Webster's weighted KLR algebra, as the subspace `eB * A * eB` of the gallery algebra,
`eB = rankIdem`. -/
noncomputable abbrev weightedKLR : Submodule k (GalleryAlgebra k Γ ν) :=
  LinearMap.range (sandwich k (rankIdem k Γ ν) (rankIdem k Γ ν))

variable (k Γ ν) in
/-- Webster's weighted KLR algebra, as a ring: the corner of the gallery algebra at the
idempotent `rankIdem`, with unit `rankIdem`. -/
abbrev WeightedKLRAlgebra : Type _ := (isIdempotentElem_rankIdem (k := k) (Γ := Γ) (ν := ν)).Corner

theorem mem_weightedKLR_iff_mem_corner {x : GalleryAlgebra k Γ ν} :
    x ∈ weightedKLR k Γ ν ↔ x ∈ Subsemigroup.corner (rankIdem k Γ ν) := by
  show _ ↔ x ∈ Set.range (fun y => rankIdem k Γ ν * y * rankIdem k Γ ν)
  simp only [weightedKLR, LinearMap.mem_range, sandwich_apply, Set.mem_range]

/-! ### Idempotents on the basis elements -/

attribute [local instance] ColPerm.fintype

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}

theorem basisElt_mul_e (C E C' : FullChamber Γ ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    basisElt k P C E g m * e C' = if C' = C then basisElt k P C E g m else 0 := by
  rw [basisElt, mul_assoc, ← e_mul_poly, ← mul_assoc, mul_assoc (r g E),
    ← galList_mul_e C, mul_assoc _ (e C), e_mul_e]
  split_ifs with h₁ h₂ h₂
  · rw [galList_mul_e]
  · exact (h₂ h₁.symm).elim
  · exact (h₁ h₂.symm).elim
  · rw [mul_zero, mul_zero, zero_mul]

theorem e_mul_basisElt (D' C E : FullChamber Γ ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    e D' * basisElt k P C E g m = if D' = g • E then basisElt k P C E g m else 0 := by
  rw [basisElt, mul_assoc (r g E), ← mul_assoc (e D'), e_mul_r]
  split_ifs
  · rfl
  · rw [zero_mul]

/-- `e D' * b * e C'` for a basis element `b = r g E * segGallery P C E * poly (y^m)`: it is `b`
if `D' = g • E` and `C' = C`, and `0` otherwise. -/
theorem e_mul_basisElt_mul_e (D' C' C E : FullChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    e D' * basisElt k P C E g m * e C' =
      if D' = g • E ∧ C' = C then basisElt k P C E g m else 0 := by
  rw [mul_assoc, basisElt_mul_e]
  split_ifs with h₁ h₂ h₂
  · simp only [e_mul_basisElt, h₂.1, ite_true]
  · rw [e_mul_basisElt, ite_eq_right_iff.2 fun h => (h₂ ⟨h, h₁⟩).elim]
  · exact (h₁ h₂.2).elim
  · rw [mul_zero]

theorem rankIdem_mul_basisElt_mul_rankIdem (C E : FullChamber Γ ν) (g : ColPerm ν)
    (m : Strand ν →₀ ℕ) :
    rankIdem k Γ ν * basisElt k P C E g m * rankIdem k Γ ν =
      if (g • E).IsRankOrdered ∧ C.IsRankOrdered then basisElt k P C E g m else 0 := by
  have hR : basisElt k P C E g m * rankIdem k Γ ν =
      if C.IsRankOrdered then basisElt k P C E g m else 0 := by
    simp only [rankIdem, Finset.mul_sum, basisElt_mul_e]
    rw [Finset.sum_ite_eq']
    simp
  have hL : rankIdem k Γ ν * basisElt k P C E g m =
      if (g • E).IsRankOrdered then basisElt k P C E g m else 0 := by
    simp only [rankIdem, Finset.sum_mul, e_mul_basisElt]
    rw [Finset.sum_ite_eq']
    simp
  rw [mul_assoc, hR]
  by_cases h₁ : C.IsRankOrdered <;> by_cases h₂ : (g • E).IsRankOrdered <;> simp [h₁, h₂, hL]

/-! ### The basis of a corner -/

section Basis

variable (hP : ∀ C E, IsChamberSegment C E (P C E))
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- The indices `(C', E, g, m)` of the gallery basis with bottom chamber `C` and top chamber
`g • E = D`, identified with the pairs `(g, m)` by `E = g⁻¹ • D`. -/
def cornerIndexEquiv (D C : FullChamber Γ ν) :
    {i : FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ) //
      D = i.2.2.1 • i.2.1 ∧ C = i.1} ≃ ColPerm ν × (Strand ν →₀ ℕ) where
  toFun i := (i.1.2.2.1, i.1.2.2.2)
  invFun gm := ⟨(C, gm.1⁻¹ • D, gm.1, gm.2), by simp⟩
  left_inv := by
    rintro ⟨⟨C', E, g, m⟩, hD, hC⟩
    simp only at hD hC
    subst hD hC
    simp
  right_inv _ := rfl

/-- **Webster, Theorem 2.8 (basis theorem)**, for the space `e D * A * e C` of elements from the
full chamber `C` to the full chamber `D`: the elements
`r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)`, for `g` a colour-preserving permutation
and `m` a monomial, form a `k`-basis. For rank-ordered `C`, `D`, the permutation `g` is
Webster's `π` (see the module docstring). -/
noncomputable def cornerBasis (D C : FullChamber Γ ν) :
    Module.Basis (ColPerm ν × (Strand ν →₀ ℕ)) k (cornerSpace k D C) :=
  (basisRangeOfApply (basisOfSegments hP hD hZ hΓ hW hL) (sandwich k (e D) (e C)) _
    fun i => by
      rw [basisOfSegments_apply, sandwich_apply]
      exact e_mul_basisElt_mul_e D C i.1 i.2.1 i.2.2.1 i.2.2.2).reindex
    (cornerIndexEquiv D C)

@[simp]
theorem cornerBasis_apply (D C : FullChamber Γ ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    (cornerBasis hP hD hZ hΓ hW hL D C (g, m) : GalleryAlgebra k Γ ν) =
      r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (monomial m 1) := by
  simp only [cornerBasis, Module.Basis.reindex_apply, basisRangeOfApply_apply]
  exact basisOfSegments_apply hP hD hZ hΓ hW hL C (g⁻¹ • D) g m

/-- **Webster, Theorem 2.8 (basis theorem)**, in Webster's form: for chambers (loadings) `c` at
the bottom and `d` at the top, the space `e d * A * e c` has the `k`-basis
`b_π y^m = r π (π⁻¹ • d) * segGallery P c (π⁻¹ • d) * poly (y^m)`, one element for each
colour-preserving permutation `π` of the strands (the strand of colour `i` and rank `a` at the
bottom ends with rank `(π (i, a)).2` among the strands of colour `i` at the top) and each
monomial `y^m` in the dots at the bottom. -/
noncomputable def chamberBasis (d c : Chamber Γ ν) :
    Module.Basis (ColPerm ν × (Strand ν →₀ ℕ)) k (cornerSpace k d.toFull c.toFull) :=
  cornerBasis hP hD hZ hΓ hW hL d.toFull c.toFull

@[simp]
theorem chamberBasis_apply (d c : Chamber Γ ν) (π : ColPerm ν) (m : Strand ν →₀ ℕ) :
    (chamberBasis hP hD hZ hΓ hW hL d c (π, m) : GalleryAlgebra k Γ ν) =
      r π (π⁻¹ • d.toFull) * segGallery P c.toFull (π⁻¹ • d.toFull) * poly (monomial m 1) :=
  cornerBasis_apply hP hD hZ hΓ hW hL _ _ π m

variable (Γ ν) in
/-- The rank-ordered full chambers: Webster's loadings. -/
abbrev RankChamber : Type _ := {C : FullChamber Γ ν // C.IsRankOrdered}

/-- The indices of the gallery basis with rank-ordered bottom and top chambers, identified with
`(C, D, g, m)` (bottom chamber, top chamber, permutation, monomial) by `E = g⁻¹ • D`. -/
def weightedKLRIndexEquiv :
    {i : FullChamber Γ ν × FullChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ) //
      (i.2.2.1 • i.2.1).IsRankOrdered ∧ i.1.IsRankOrdered} ≃
      RankChamber Γ ν × RankChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ) where
  toFun i := (⟨i.1.1, i.2.2⟩, ⟨i.1.2.2.1 • i.1.2.1, i.2.1⟩, i.1.2.2.1, i.1.2.2.2)
  invFun x := ⟨(x.1.1, x.2.2.1⁻¹ • x.2.1.1, x.2.2.1, x.2.2.2), by simpa using ⟨x.2.1.2, x.1.2⟩⟩
  left_inv := by
    rintro ⟨⟨C, E, g, m⟩, h⟩
    simp
  right_inv := by
    rintro ⟨C, D, g, m⟩
    simp

/-- **Webster, Theorem 2.8 (basis theorem)** for Webster's weighted KLR algebra
`eB * A * eB`: the elements `r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D) * poly (y^m)`, for
rank-ordered chambers `C` (bottom) and `D` (top), colour-preserving permutations `g` (Webster's
`π`) and monomials `m`, form a `k`-basis. -/
noncomputable def weightedKLRBasis :
    Module.Basis (RankChamber Γ ν × RankChamber Γ ν × ColPerm ν × (Strand ν →₀ ℕ)) k
      (weightedKLR k Γ ν) :=
  (basisRangeOfApply (basisOfSegments hP hD hZ hΓ hW hL)
    (sandwich k (rankIdem k Γ ν) (rankIdem k Γ ν)) _
    fun i => by
      rw [basisOfSegments_apply, sandwich_apply]
      exact rankIdem_mul_basisElt_mul_rankIdem i.1 i.2.1 i.2.2.1 i.2.2.2).reindex
    weightedKLRIndexEquiv

@[simp]
theorem weightedKLRBasis_apply (C D : RankChamber Γ ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    (weightedKLRBasis hP hD hZ hΓ hW hL (C, D, g, m) : GalleryAlgebra k Γ ν) =
      r g (g⁻¹ • D.1) * segGallery P C.1 (g⁻¹ • D.1) * poly (monomial m 1) := by
  simp only [weightedKLRBasis, Module.Basis.reindex_apply, basisRangeOfApply_apply]
  exact basisOfSegments_apply hP hD hZ hΓ hW hL C.1 (g⁻¹ • D.1) g m

/-! ### Freeness over the polynomials in the dots -/

variable (P) in
/-- The element `b(g, 1) = r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D)` of `e D * A * e C`:
Webster's `b_π` for `π = g`. -/
noncomputable def cornerElt (D C : FullChamber Γ ν) (g : ColPerm ν) : GalleryAlgebra k Γ ν :=
  r g (g⁻¹ • D) * segGallery P C (g⁻¹ • D)

/-- **Webster, Theorem 2.8**, as freeness over the polynomials in the dots at the bottom: every
element of `e D * A * e C` is `∑_g b(g, 1) * poly (f g)` for unique polynomials `f g`. -/
noncomputable def cornerPolyEquiv (D C : FullChamber Γ ν) :
    (ColPerm ν → PolyRing ν k) ≃ₗ[k] cornerSpace k D C :=
  LinearEquiv.piCongrRight (fun _ => (basisMonomials (Strand ν) k).repr) ≪≫ₗ
    (Finsupp.linearEquivFunOnFinite k _ (ColPerm ν)).symm ≪≫ₗ
    (Finsupp.curryLinearEquiv k).symm ≪≫ₗ (cornerBasis hP hD hZ hΓ hW hL D C).repr.symm

theorem cornerPolyEquiv_apply (D C : FullChamber Γ ν) (f : ColPerm ν → PolyRing ν k) :
    (cornerPolyEquiv hP hD hZ hΓ hW hL D C f : GalleryAlgebra k Γ ν) =
      ∑ g, cornerElt P D C g * poly (f g) := by
  have key : (cornerSpace k D C).subtype ∘ₗ (cornerPolyEquiv hP hD hZ hΓ hW hL D C).toLinearMap =
      ∑ g, LinearMap.mulLeft k (cornerElt P D C g) ∘ₗ (polyHom k Γ ν).toLinearMap ∘ₗ
        LinearMap.proj g := by
    refine LinearMap.pi_ext' fun g => (basisMonomials (Strand ν) k).ext fun m => ?_
    classical
    have e1 : (LinearEquiv.piCongrRight fun _ => (basisMonomials (Strand ν) k).repr)
        (Pi.single g (monomial m 1)) = Pi.single g (Finsupp.single m (1 : k)) := by
      ext g' : 1
      by_cases h : g' = g
      · subst h
        simp only [LinearEquiv.piCongrRight_apply, Pi.single_eq_same]
        rw [← (basisMonomials (Strand ν) k).repr_self m, coe_basisMonomials]
      · simp [h]
    have rhs : ∑ c, cornerElt P D C c * poly (Pi.single (M := fun _ => PolyRing ν k) g
        (monomial m (1 : k)) c) = cornerElt P D C g * poly (monomial m 1) := by
      rw [Finset.sum_eq_single g (fun c _ hc => by
        rw [Pi.single_eq_of_ne hc, ← polyHom_apply, map_zero, mul_zero])
        (by simp), Pi.single_eq_same]
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.proj_apply, AlgHom.toLinearMap_apply, polyHom_apply, LinearMap.mulLeft_apply,
      LinearMap.coe_single, coe_basisMonomials]
    rw [rhs]
    simp only [LinearEquiv.coe_coe, Submodule.coe_subtype, cornerPolyEquiv,
      LinearEquiv.trans_apply, e1, Finsupp.linearEquivFunOnFinite_symm_single,
      Finsupp.curryLinearEquiv_symm_apply, Finsupp.uncurry_single,
      Module.Basis.repr_symm_single_one, cornerBasis_apply, cornerElt]
  simpa using congrArg (fun φ => φ f) key

end Basis

end GalleryAlgebra

end Categorification.WeightedKLR
