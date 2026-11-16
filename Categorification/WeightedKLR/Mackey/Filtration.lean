/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.GalleryBasis.Corner
import Categorification.WeightedKLR.Mackey.ShuffleType

/-!
# The shuffle-type filtration of a corner of the weighted KLR algebra

The Mackey filtration of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, §2.4 (proof of Theorem 2.19, which follows Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18), on the space `e D * A * e C` of diagrams from a
rank-ordered full chamber `C` to a rank-ordered full chamber `D`.

For a set `S` of shuffle types (functions `I → ℕ`), `mackeyFilt D C S` is the span of the
elements `b(g, m)` of the basis of Theorem 2.8 (`cornerBasis`) whose relabelling `g` has shuffle
type in `S`. When `S` is a lower set this span has an intrinsic description
(`mem_mackeyFilt_iff`): an element of `e D * A * e C` lies in it exactly when its operator in
the polynomial representation, from the copy of `C` to the copy of `D` (`blockOp`), is supported
in the relabellings of shuffle type in `S`. The proof is the triangularity of the basis
(`isSupported_basisOp_shuffleLE`) together with a leading-term argument relative to the support
(`IsSupported.eq_zero_of_sum`).

The intrinsic description gives the module structure: multiplying on the left by an element of
`e D' * A * e D` whose operator only involves relabellings preserving the first block at the top,
or on the right by an element of `e C * A * e C'` whose operator only involves relabellings
preserving the second block at the bottom, preserves the filtration (`mul_mem_mackeyFilt`,
`mackeyFilt_mul_mem`).

## Main definitions

* `GalleryAlgebra.blockOp k hΓ D C z`: the operator of `z` in the polynomial representation from
  the copy of `C` to the copy of `D`.
* `GalleryAlgebra.mackeyFilt D C S`: the span of the basis elements of shuffle type in `S`.

## Main results

* `IsSupported.eq_zero_of_sum`: leading terms relative to a support.
* `GalleryAlgebra.mem_mackeyFilt_iff`: the intrinsic description of the filtration.
* `GalleryAlgebra.mackeyFiltBasis`: the basis of each step of the filtration.
* `GalleryAlgebra.mackeyFilt_univ`, `GalleryAlgebra.mackeyFilt_mono`: the filtration is
  increasing and exhausts `e D * A * e C`.
* `GalleryAlgebra.mul_mem_mackeyFilt`, `GalleryAlgebra.mackeyFilt_mul_mem`: stability under
  multiplication by elements with parabolic relabellings.
-/

namespace Categorification.WeightedKLR

open MvPolynomial Equiv FullChamber Segment Pointwise

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

/-! ### Leading terms relative to a support -/

omit [DecidableEq I] in
/-- **Leading terms relative to a support.** Let `Y g` be twisted operators with denominators
`M g` and coefficients `a g`, with `a g g` a non-zero-divisor and `a g x ≠ 0` for `x ≠ g` only if
`Λ x < Λ g`, and with `Y g` supported in `T` whenever `g ∈ T`. If `∑_g Y g ∘ (F g * ·)` is
supported in `T`, then `F g = 0` for every `g ∉ T`. -/
theorem IsSupported.eq_zero_of_sum {Y : ColPerm ν → PolyRing ν k →ₗ[k] PolyRing ν k}
    {M : ColPerm ν → PolyRing ν k} {a : ColPerm ν → ColPerm ν → PolyRing ν k}
    (Λ : ColPerm ν → ℕ) (hM : ∀ g, IsRegular (M g)) (hY : ∀ g, IsTwisted (Y g) (M g) (a g))
    (ha : ∀ g, IsRegular (a g g)) (hlt : ∀ g x, a g x ≠ 0 → x ≠ g → Λ x < Λ g)
    {T : Set (ColPerm ν)} (hYT : ∀ g ∈ T, IsSupported (Y g) T) {F : ColPerm ν → PolyRing ν k}
    (hF : IsSupported (∑ g, Y g ∘ₗ LinearMap.mulLeft k (F g)) T) {g : ColPerm ν}
    (hg : g ∉ T) : F g = 0 := by
  classical
  set N : ColPerm ν → PolyRing ν k := fun g => ∏ h ∈ Finset.univ.erase g, M h
  have hN : ∀ g, IsRegular (N g) := fun g => IsRegular.prod fun h _ => hM h
  have hT : IsTwisted (∑ g, Y g ∘ₗ LinearMap.mulLeft k (F g)) (∏ h, M h)
      (fun x => ∑ g, N g * a g x * MvPolynomial.rename ⇑x.1 (F g)) := by
    intro f
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), mul_assoc, hY g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul]
    ring
  by_contra hne
  set S := Finset.univ.filter fun g => g ∉ T ∧ F g ≠ 0
  obtain ⟨g₀, hg₀, hmax⟩ := S.exists_max_image Λ ⟨g, by simp [S, hg, hne]⟩
  obtain ⟨hg₀T, hF₀⟩ := (Finset.mem_filter.1 hg₀).2
  have hcoef := hF.coeff_eq_zero hT hg₀T
  rw [Finset.sum_eq_single g₀ (fun g' _ hg' => ?_) (fun hx => absurd (Finset.mem_univ g₀) hx)]
    at hcoef
  · have h0 : MvPolynomial.rename ⇑g₀.1 (F g₀) = 0 :=
      ((hN g₀).mul (ha g₀)).left.mul_left_eq_zero_iff.1 hcoef
    rw [← map_zero (MvPolynomial.rename (R := k) ⇑g₀.1)] at h0
    exact hF₀ (rename_colPerm_injective g₀ h0)
  · by_cases hT' : g' ∈ T
    · rw [(hYT g' hT').coeff_eq_zero (hY g') hg₀T, mul_zero, zero_mul]
    by_cases hFg : F g' = 0
    · rw [hFg, map_zero, mul_zero]
    · have hle := hmax g' (by simp [S, hT', hFg])
      have hag : a g' g₀ = 0 := by
        by_contra hag
        exact absurd (hlt g' g₀ hag (Ne.symm hg')) (not_lt.2 hle)
      rw [hag, mul_zero, zero_mul]

/-! ### Shuffle types under parabolic relabellings -/

theorem shuffleType_mul_of_image_left (ν' ν₁ : I →₀ ℕ) {y : ColPerm ν}
    (hy : (leftStrands ν₁).image y.1 = leftStrands ν₁) (x : ColPerm ν) :
    shuffleType ν' ν₁ (y * x) = shuffleType ν' ν₁ x := by
  funext i
  rw [shuffleType_eq_card, shuffleType_eq_card]
  have e : (rightStrands ν' i).image (y * x).1 =
      ((rightStrands ν' i).image x.1).image y.1 := by
    rw [Finset.image_image]
    rfl
  have hinv : (leftStrands ν₁).image (y⁻¹).1 = leftStrands (ν := ν) ν₁ := by
    conv_lhs => rw [← hy]
    rw [Finset.image_image]
    convert Finset.image_id (s := leftStrands (ν := ν) ν₁)
    funext t
    exact y.1.symm_apply_apply t
  rw [e, card_inter_image_colPerm y, hinv]

theorem shuffleType_mul_of_image_right (ν' ν₁ : I →₀ ℕ) {y : ColPerm ν}
    (hy : ∀ i, (rightStrands ν' i).image y.1 = rightStrands (ν := ν) ν' i) (x : ColPerm ν) :
    shuffleType ν' ν₁ (x * y) = shuffleType ν' ν₁ x := by
  funext i
  rw [shuffleType_eq_card, shuffleType_eq_card]
  have e : (rightStrands ν' i).image (x * y).1 =
      ((rightStrands ν' i).image y.1).image x.1 := by
    rw [Finset.image_image]
    rfl
  rw [e, hy]

namespace GalleryAlgebra

/-! ### Block operators -/

theorem e_mul_e_self (C : FullChamber Γ ν) : (e C * e C : GalleryAlgebra k Γ ν) = e C := by
  rw [e_mul_e]
  simp

section BlockOp

variable (hΓ : Γ.PSymm)

variable (k) in
/-- The operator of `z` in the polynomial representation from the copy of `C` to the copy of
`D`. -/
noncomputable def blockOp (D C : FullChamber Γ ν) (z : GalleryAlgebra k Γ ν) :
    PolyRing ν k →ₗ[k] PolyRing ν k :=
  LinearMap.proj D ∘ₗ galleryRep k hΓ z ∘ₗ LinearMap.single k (fun _ => PolyRing ν k) C

theorem blockOp_apply (D C : FullChamber Γ ν) (z : GalleryAlgebra k Γ ν) (f : PolyRing ν k) :
    blockOp k hΓ D C z f = galleryRep k hΓ z (Pi.single C f) D := rfl

@[simp]
theorem blockOp_zero (D C : FullChamber Γ ν) : blockOp k hΓ D C 0 = 0 := by
  refine _root_.LinearMap.ext fun f => ?_
  simp [blockOp_apply]

theorem blockOp_add (D C : FullChamber Γ ν) (z z' : GalleryAlgebra k Γ ν) :
    blockOp k hΓ D C (z + z') = blockOp k hΓ D C z + blockOp k hΓ D C z' := by
  refine _root_.LinearMap.ext fun f => ?_
  simp [blockOp_apply]

theorem blockOp_smul (D C : FullChamber Γ ν) (c : k) (z : GalleryAlgebra k Γ ν) :
    blockOp k hΓ D C (c • z) = c • blockOp k hΓ D C z := by
  refine _root_.LinearMap.ext fun f => ?_
  simp [blockOp_apply]

theorem blockOp_sum {ι : Type*} (s : Finset ι) (D C : FullChamber Γ ν)
    (z : ι → GalleryAlgebra k Γ ν) :
    blockOp k hΓ D C (∑ i ∈ s, z i) = ∑ i ∈ s, blockOp k hΓ D C (z i) := by
  refine _root_.LinearMap.ext fun f => ?_
  simp [blockOp_apply, LinearMap.sum_apply, Finset.sum_apply]

theorem blockOp_of_galleryRep_eq_blk {D C : FullChamber Γ ν} {z : GalleryAlgebra k Γ ν}
    {a : PolyRing ν k →ₗ[k] PolyRing ν k} (h : galleryRep k hΓ z = blk k C D a) :
    blockOp k hΓ D C z = a := by
  refine _root_.LinearMap.ext fun f => ?_
  simp [blockOp_apply, h, blk_apply]

theorem galleryRep_single_of_e_mul {D C : FullChamber Γ ν} {z : GalleryAlgebra k Γ ν}
    (hz : e D * z = z) (f : PolyRing ν k) :
    galleryRep k hΓ z (Pi.single C f) = Pi.single D (blockOp k hΓ D C z f) := by
  conv_lhs => rw [← hz]
  rw [map_mul, galleryRep_e, Module.End.mul_apply, blk_apply]
  rfl

/-- Block operators compose. -/
theorem blockOp_mul {D' D C : FullChamber Γ ν} (a : GalleryAlgebra k Γ ν)
    {z : GalleryAlgebra k Γ ν} (hz : e D * z = z) :
    blockOp k hΓ D' C (a * z) = blockOp k hΓ D' D a ∘ₗ blockOp k hΓ D C z := by
  refine _root_.LinearMap.ext fun f => ?_
  rw [blockOp_apply, map_mul, Module.End.mul_apply, galleryRep_single_of_e_mul hΓ hz]
  rfl

end BlockOp

/-! ### The filtration -/

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}

section Filtration

variable (hP : ∀ C E, IsChamberSegment C E (P C E))
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
      a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- The relabellings of shuffle type in `S`. -/
def shuffleSet (ν' ν₁ : I →₀ ℕ) (S : Set (I → ℕ)) : Set (ColPerm ν) :=
  {y | shuffleType ν' ν₁ y ∈ S}

theorem blockOp_cornerBasis (D C : FullChamber Γ ν) (g : ColPerm ν) (m : Strand ν →₀ ℕ) :
    blockOp k hΓ D C (cornerBasis hP hD hZ hΓ hW hL D C (g, m)) = basisOp k P C D g m := by
  rw [cornerBasis_apply]
  exact blockOp_of_galleryRep_eq_blk hΓ (galleryRep_basisElt_eq_blk hP hΓ C D g m)

variable (k) in
/-- **The shuffle-type filtration.** The span of the elements `b(g, m)` of the basis of
`e D * A * e C` whose relabelling `g` has shuffle type in `S`. -/
noncomputable def mackeyFilt (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν) (S : Set (I → ℕ)) :
    Submodule k (GalleryAlgebra k Γ ν) :=
  Submodule.span k (Set.range fun i : {i : ColPerm ν × (Strand ν →₀ ℕ) //
    shuffleType ν' ν₁ i.1 ∈ S} => (cornerBasis hP hD hZ hΓ hW hL D C i.1 : GalleryAlgebra k Γ ν))

theorem mackeyFilt_le_cornerSpace (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν)
    (S : Set (I → ℕ)) : mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S ≤ cornerSpace k D C :=
  Submodule.span_le.2 <| by
    rintro _ ⟨i, rfl⟩
    exact (cornerBasis hP hD hZ hΓ hW hL D C i.1).2

theorem mackeyFilt_mono (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν) {S S' : Set (I → ℕ)}
    (h : S ⊆ S') :
    mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S ≤ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S' :=
  Submodule.span_mono <| by
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.1, h i.2⟩, rfl⟩

/-- The filtration exhausts `e D * A * e C`. -/
theorem mackeyFilt_univ (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν) :
    mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C Set.univ = cornerSpace k D C := by
  refine le_antisymm (mackeyFilt_le_cornerSpace hP hD hZ hΓ hW hL ν' ν₁ D C _) ?_
  intro z hz
  have hb := (cornerBasis hP hD hZ hΓ hW hL D C).mem_span (⟨z, hz⟩ : cornerSpace k D C)
  have := Submodule.apply_mem_span_image_iff_mem_span (f := (cornerSpace k D C).subtype)
    (cornerSpace k D C).injective_subtype (x := ⟨z, hz⟩) (s := Set.range
      (cornerBasis hP hD hZ hΓ hW hL D C))
  rw [← Set.range_comp] at this
  refine (Submodule.span_mono ?_) (this.2 hb)
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, Set.mem_univ _⟩, rfl⟩

/-- The basis of each step of the filtration: the basis elements of shuffle type in `S`. -/
noncomputable def mackeyFiltBasis (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν) (S : Set (I → ℕ)) :
    Module.Basis {i : ColPerm ν × (Strand ν →₀ ℕ) // shuffleType ν' ν₁ i.1 ∈ S} k
      (mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S) :=
  Module.Basis.span (((cornerBasis hP hD hZ hΓ hW hL D C).linearIndependent.map'
    (cornerSpace k D C).subtype (Submodule.ker_subtype _)).comp Subtype.val
    Subtype.val_injective)

@[simp]
theorem mackeyFiltBasis_apply (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν) (S : Set (I → ℕ))
    (i : {i : ColPerm ν × (Strand ν →₀ ℕ) // shuffleType ν' ν₁ i.1 ∈ S}) :
    (mackeyFiltBasis hP hD hZ hΓ hW hL ν' ν₁ D C S i : GalleryAlgebra k Γ ν) =
      cornerBasis hP hD hZ hΓ hW hL D C i.1 := by
  unfold mackeyFiltBasis
  erw [Module.Basis.span_apply]

/-- **The intrinsic description of the shuffle-type filtration.** For rank-ordered `C`, `D` and
a lower set `S` of shuffle types, an element `z` of `e D * A * e C` lies in the span of the basis
elements of shuffle type in `S` exactly when its operator from `C` to `D` in the polynomial
representation is supported in the relabellings of shuffle type in `S`. -/
theorem mem_mackeyFilt_iff (ν' ν₁ : I →₀ ℕ) {D C : FullChamber Γ ν} (hC : C.IsRankOrdered)
    (hD' : D.IsRankOrdered) {S : Set (I → ℕ)} (hS : IsLowerSet S) {z : GalleryAlgebra k Γ ν}
    (hz : z ∈ cornerSpace k D C) :
    z ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S ↔
      IsSupported (blockOp k hΓ D C z) (shuffleSet ν' ν₁ S) := by
  classical
  set b := cornerBasis hP hD hZ hΓ hW hL D C with hbdef
  have hsupp : ∀ g m, shuffleType ν' ν₁ g ∈ S →
      IsSupported (basisOp k P C D g m) (shuffleSet ν' ν₁ S) := fun g m hg =>
    (isSupported_basisOp_shuffleLE hP ν' ν₁ hC hD' g m).mono fun y hy => hS (fun i => hy i) hg
  constructor
  · intro h
    clear hz
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨⟨g, m⟩, hg⟩, rfl⟩ := hx
      rw [blockOp_cornerBasis]
      exact hsupp g m hg
    | zero => rw [blockOp_zero]; exact IsSupported.zero _
    | add x y _ _ hx hy =>
      rw [blockOp_add]
      simpa using hx.add hy
    | smul c x _ hx =>
      rw [blockOp_smul]
      exact hx.smul c
  · intro h
    set z' : cornerSpace k D C := ⟨z, hz⟩
    set l := b.repr z' with hl
    have hz' : z = ∑ i ∈ l.support, l i • (b i : GalleryAlgebra k Γ ν) := by
      have := congrArg Subtype.val (b.linearCombination_repr z')
      rw [Finsupp.linearCombination_apply, Finsupp.sum] at this
      simpa using this.symm
    -- the relabelled galleries and their coefficient polynomials
    set Y : ColPerm ν → PolyRing ν k →ₗ[k] PolyRing ν k := fun g => ren g ∘ₗ
      opList k Γ C (word (hypAff (Γ := Γ)) (P C (g⁻¹ • D)).1 (P C (g⁻¹ • D)).2) with hY
    set F : ColPerm ν → PolyRing ν k := fun g =>
      ∑ i ∈ l.support.filter (fun i => i.1 = g), monomial i.2 (l i) with hF
    have hbasis : ∀ g m, basisOp k P C D g m = Y g ∘ₗ LinearMap.mulLeft k (monomial m 1) :=
      fun _ _ => rfl
    have hsum : blockOp k hΓ D C z = ∑ g, Y g ∘ₗ LinearMap.mulLeft k (F g) := by
      have hb' : ∀ i, blockOp k hΓ D C (b i) = Y i.1 ∘ₗ LinearMap.mulLeft k (monomial i.2 1) :=
        fun i => blockOp_cornerBasis hP hD hZ hΓ hW hL D C i.1 i.2
      rw [hz', blockOp_sum]
      refine _root_.LinearMap.ext fun f => ?_
      simp only [blockOp_smul, hb', LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, LinearMap.mulLeft_apply, hF, Finset.sum_mul, map_sum]
      rw [← Finset.sum_fiberwise l.support Prod.fst]
      refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun i hi => ?_
      rw [← (Finset.mem_filter.1 hi).2, ← map_smul, ← smul_mul_assoc, smul_monomial, smul_eq_mul,
        mul_one]
    choose M a hM hT ha hlt using fun g => exists_isTwisted_ren_opList (k := k) hP hW hL C D g
    have hYT : ∀ g ∈ shuffleSet ν' ν₁ S, IsSupported (Y g) (shuffleSet ν' ν₁ S) := by
      intro g hg
      have := hsupp g 0 hg
      rwa [hbasis, monomial_zero', C_1, LinearMap.mulLeft_one, LinearMap.comp_id] at this
    have hF0 : ∀ g, shuffleType ν' ν₁ g ∉ S → F g = 0 := fun g hg =>
      IsSupported.eq_zero_of_sum (fun x => sepCard C.1 (x⁻¹ • D).1) hM hT ha hlt hYT
        (hsum ▸ h) hg
    have hmem : ∀ i ∈ l.support, shuffleType ν' ν₁ i.1 ∈ S := by
      rintro ⟨g, m⟩ hi
      by_contra hg
      have h0 : (F g).coeff m = 0 := by rw [hF0 g hg]; simp
      simp only [hF, coeff_sum, coeff_monomial] at h0
      rw [Finset.sum_eq_single_of_mem (s := l.support.filter fun x => x.1 = g) (g, m)
        (Finset.mem_filter.2 ⟨hi, rfl⟩)] at h0
      · exact Finsupp.mem_support_iff.1 hi (by simpa using h0)
      · rintro ⟨g', m'⟩ hb hne
        obtain ⟨-, hg'⟩ := Finset.mem_filter.1 hb
        simp only at hg'
        subst hg'
        exact ite_eq_right_iff.2 fun hm => absurd (by subst hm; rfl) hne
    rw [hz']
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨⟨i, hmem i hi⟩, rfl⟩

/-- **Left module structure of the filtration.** Multiplying on the left by an element of
`e D' * A * e D` whose operator from `D` to `D'` only involves relabellings preserving the
strands of the first block at the top preserves the filtration. -/
theorem mul_mem_mackeyFilt (ν' ν₁ : I →₀ ℕ) {D' D C : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered) (hD'' : D'.IsRankOrdered)
    {S : Set (I → ℕ)} (hS : IsLowerSet S) {a z : GalleryAlgebra k Γ ν}
    (ha : a ∈ cornerSpace k D' D)
    (hpar : IsSupported (blockOp k hΓ D' D a)
      {y | (leftStrands ν₁).image y.1 = leftStrands (ν := ν) ν₁})
    (hz : z ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S) :
    a * z ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D' C S := by
  have hzc := mackeyFilt_le_cornerSpace hP hD hZ hΓ hW hL ν' ν₁ D C S hz
  have hze : e D * z = z := by
    rw [mem_cornerSpace_iff] at hzc
    rw [← hzc, ← mul_assoc, ← mul_assoc, e_mul_e_self]
  have hzr : z * e C = z := by
    rw [mem_cornerSpace_iff] at hzc
    rw [← hzc, mul_assoc, e_mul_e_self]
  have ha' : e D' * a = a := by
    rw [mem_cornerSpace_iff] at ha
    rw [← ha, ← mul_assoc, ← mul_assoc, e_mul_e_self]
  have hac : a * z ∈ cornerSpace k D' C := by
    rw [mem_cornerSpace_iff, mul_assoc, mul_assoc, hzr, ← mul_assoc, ha']
  rw [mem_mackeyFilt_iff hP hD hZ hΓ hW hL ν' ν₁ hC hD'' hS hac, blockOp_mul hΓ a hze]
  have := hpar.comp ((mem_mackeyFilt_iff hP hD hZ hΓ hW hL ν' ν₁ hC hD' hS hzc).1 hz)
  refine this.mono fun y hy => ?_
  obtain ⟨u, hu, x, hx, rfl⟩ := Set.mem_mul.1 hy
  show shuffleType ν' ν₁ (u * x) ∈ S
  rw [shuffleType_mul_of_image_left ν' ν₁ hu]
  exact hx

/-- **Right module structure of the filtration.** Multiplying on the right by an element of
`e C * A * e C'` whose operator from `C'` to `C` only involves relabellings preserving the
strands of the second block at the bottom preserves the filtration. -/
theorem mackeyFilt_mul_mem (ν' ν₁ : I →₀ ℕ) {D C C' : FullChamber Γ ν}
    (hC : C.IsRankOrdered) (hC' : C'.IsRankOrdered) (hD' : D.IsRankOrdered)
    {S : Set (I → ℕ)} (hS : IsLowerSet S) {z b : GalleryAlgebra k Γ ν}
    (hb : b ∈ cornerSpace k C C')
    (hpar : IsSupported (blockOp k hΓ C C' b)
      {y | ∀ i, (rightStrands ν' i).image y.1 = rightStrands (ν := ν) ν' i})
    (hz : z ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S) :
    z * b ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C' S := by
  have hzc := mackeyFilt_le_cornerSpace hP hD hZ hΓ hW hL ν' ν₁ D C S hz
  have hbe : e C * b = b := by
    rw [mem_cornerSpace_iff] at hb
    rw [← hb, ← mul_assoc, ← mul_assoc, e_mul_e_self]
  have hzl : e D * z = z := by
    rw [mem_cornerSpace_iff] at hzc
    rw [← hzc, ← mul_assoc, ← mul_assoc, e_mul_e_self]
  have hbr : b * e C' = b := by
    rw [mem_cornerSpace_iff] at hb
    rw [← hb, mul_assoc, e_mul_e_self]
  have hzb : z * b ∈ cornerSpace k D C' := by
    rw [mem_cornerSpace_iff, mul_assoc, mul_assoc, hbr, ← mul_assoc, hzl]
  rw [mem_mackeyFilt_iff hP hD hZ hΓ hW hL ν' ν₁ hC' hD' hS hzb, blockOp_mul hΓ z hbe]
  have := ((mem_mackeyFilt_iff hP hD hZ hΓ hW hL ν' ν₁ hC hD' hS hzc).1 hz).comp hpar
  refine this.mono fun y hy => ?_
  obtain ⟨x, hx, u, hu, rfl⟩ := Set.mem_mul.1 hy
  show shuffleType ν' ν₁ (x * u) ∈ S
  rw [shuffleType_mul_of_image_right ν' ν₁ hu]
  exact hx

end Filtration

end GalleryAlgebra

end Categorification.WeightedKLR
