/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.MiddleResInd
import Categorification.WeightedKLR.Induction.Restriction

/-!
# The subquotient of `Res ∘ Ind` of one shuffle type is the middle balanced tensor product

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18). In the layout
`ν = (a + b) + (c + d)`, `ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d`, the descended map
`middleResIndMap : (W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d}) → S / S'`,
`t ⊗ y ↦ [ι(t) ψ_c ι(y)]`, is a linear isomorphism onto the subquotient of shuffle type `c` of
the Mackey filtration of `Res_{a+c;b+d} Ind_{a+b;c+d}`, compatible with the bimodule structures.
The proof assembles the corner isomorphisms `middleCornerEquiv` over the juxtaposed corners.

## Main results

* `GalleryAlgebra.resIndSubquotientMul_one`, `resIndSubquotientMul_sum_left`,
  `resIndSubquotientMul_sum_right`: the bimodule structure is unital and additive.
* `GalleryAlgebra.resIndCornerProj_resIndSubquotientMul`,
  `GalleryAlgebra.resIndSubquotientMul_eq_zero_of_corner`: multiplication by a pair of
  idempotents `e D`, `e C` is detected by the corner `D`, `C`.
* `Juxtapose.middleResIndEquiv`: the isomorphism, with `middleResIndEquiv_tmul` and the bimodule
  property `middleResIndMap_comp_middleCornerMap`.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose MulOpposite
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k}

namespace GalleryAlgebra

/-- `ι(e C' ⊗ e C'') = e (C' C'')`. -/
theorem inductionVal_rankE_tmul_rankE {ν ν' ν'' : I →₀ ℕ} (h : ν' + ν'' = ν)
    {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''} (hC' : C'.IsRankOrdered)
    (hC'' : C''.IsRankOrdered) :
    inductionVal k h (rankE k hC' ⊗ₜ rankE k hC'') = e (castChamber h (chamber C' C'')) := by
  have hcast : ∀ {μ : I →₀ ℕ} (h : ν' + ν'' = μ) (C : FullChamber Γ (ν' + ν'')),
      castGallery k Γ h (e C) = e (castChamber h C) := by
    intro μ h C
    subst h
    rfl
  rw [inductionVal_apply, inductionMap_rankE_tmul_rankE]
  exact hcast _ _

variable {ν ν₁ ν₂ ν' ν'' : I →₀ ℕ}
  {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))
  (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) {S' S : Set (I → ℕ)}
  (hS' : IsLowerSet S') (hS : IsLowerSet S)

theorem resIndSubquotientMul_one (q : ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S) :
    resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS' hS 1 1 q = q := by
  induction q using Submodule.Quotient.induction_on with
  | H z =>
    rw [resIndSubquotientMul_mk]
    congr 1
    refine Subtype.ext ?_
    rw [coe_resIndFiltMul, z.2.1, z.2.2.1]

theorem resIndSubquotientMul_sum_left {α : Type*} (s : Finset α)
    (u : α → WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    (q : ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S) :
    resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS' hS (∑ i ∈ s, u i) w q =
      ∑ i ∈ s, resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS' hS (u i) w q := by
  induction q using Submodule.Quotient.induction_on with
  | H z =>
    simp only [resIndSubquotientMul_mk]
    refine (congrArg (Submodule.mkQ _) (Subtype.ext ?_)).trans (map_sum _ _ _)
    simp only [coe_resIndFiltMul, Submodule.coe_sum, map_sum, Finset.sum_mul]

theorem resIndSubquotientMul_sum_right {α : Type*} (s : Finset α)
    (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (w : α → WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    (q : ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S) :
    resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS' hS u (∑ i ∈ s, w i) q =
      ∑ i ∈ s, resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS' hS u (w i) q := by
  induction q using Submodule.Quotient.induction_on with
  | H z =>
    simp only [resIndSubquotientMul_mk]
    refine (congrArg (Submodule.mkQ _) (Subtype.ext ?_)).trans (map_sum _ _ _)
    simp only [coe_resIndFiltMul, Submodule.coe_sum, map_sum, Finset.mul_sum]

variable {D C : FullChamber Γ ν} (hD' : D.IsRankOrdered) (hC' : C.IsRankOrdered)
  {u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂}
  {w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν''}

/-- The corner `D`, `C` of `ι(u) q ι(w)` is that of `q`, for `ι(u) = e D`, `ι(w) = e C`. -/
theorem resIndCornerProj_resIndSubquotientMul (hu : inductionVal k hν₁ u = e D)
    (hw : inductionVal k hν' w = e C) (q : ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S) :
    resIndCornerProj hP hD hZ hΓ hW hL hν' hν₁ hD' hC'
        (resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS' hS u w q) =
      resIndCornerProj hP hD hZ hΓ hW hL hν' hν₁ hD' hC' q := by
  induction q using Submodule.Quotient.induction_on with
  | H z =>
    rw [resIndSubquotientMul_mk, resIndCornerProj_mk, resIndCornerProj_mk]
    congr 1
    refine Subtype.ext ?_
    rw [coe_resIndCorner, coe_resIndCorner, coe_resIndFiltMul, hu, hw,
      show e D * (e D * z.1 * e C) * e C = (e D * e D) * z.1 * (e C * e C) by
        simp only [mul_assoc], e_mul_e_self, e_mul_e_self]

/-- `ι(u) q ι(w)` vanishes if the corner `D`, `C` of `q` does, for `ι(u) = e D`, `ι(w) = e C`. -/
theorem resIndSubquotientMul_eq_zero_of_corner (hu : inductionVal k hν₁ u = e D)
    (hw : inductionVal k hν' w = e C) {q : ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S}
    (hq : resIndCornerProj hP hD hZ hΓ hW hL hν' hν₁ hD' hC' q = 0) :
    resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS' hS u w q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | H z =>
    rw [resIndCornerProj_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, coe_resIndCorner] at hq
    rw [resIndSubquotientMul_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, coe_resIndFiltMul]
    refine ⟨?_, ?_, fun D₁ C₁ _ _ => ?_⟩
    · rw [← mul_assoc, ← mul_assoc, ← inductionVal_mul, one_mul]
    · rw [mul_assoc, ← inductionVal_mul, mul_one]
    · rw [hu, hw, show e D₁ * (e D * z.1 * e C) * e C₁ = (e D₁ * e D) * z.1 * (e C * e C₁) by
        simp only [mul_assoc], e_mul_e, e_mul_e]
      split_ifs with h1 h2
      · subst h1 h2
        exact hq
      all_goals
        simp only [zero_mul, mul_zero]
        exact zero_mem _

end GalleryAlgebra

namespace Juxtapose

variable {a b c d : I →₀ ℕ}

section CornerMap

theorem middleCornerMap_add_left
    (zL zL' : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (zR : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) :
    middleCornerMap (zL + zL') zR = middleCornerMap zL zR + middleCornerMap zL' zR :=
  BalancedTensor.ext fun t y => by
    rw [LinearMap.add_apply, middleCornerMap_tmul, middleCornerMap_tmul, middleCornerMap_tmul,
      add_smul, BalancedTensor.add_tmul]

theorem middleCornerMap_add_right
    (zL : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (zR zR' : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) :
    middleCornerMap zL (zR + zR') = middleCornerMap zL zR + middleCornerMap zL zR' :=
  BalancedTensor.ext fun t y => by
    rw [LinearMap.add_apply, middleCornerMap_tmul, middleCornerMap_tmul, middleCornerMap_tmul,
      ← BalancedTensor.tmul_add]
    congr 1
    exact Subtype.ext (mul_add _ _ _)

theorem middleCornerMap_one_one :
    middleCornerMap (1 : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
      (1 : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) =
      LinearMap.id :=
  BalancedTensor.ext fun t y => by
    rw [middleCornerMap_tmul, LinearMap.id_apply, one_smul]
    congr 1
    exact Subtype.ext (mul_one _)

theorem middleCornerMap_sum_left {α : Type*} (s : Finset α)
    (u : α → WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (zR : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) :
    middleCornerMap (∑ i ∈ s, u i) zR = ∑ i ∈ s, middleCornerMap (u i) zR := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have h := middleCornerMap_add_left (0 : WeightedKLRAlgebra k Γ (a + c) ⊗[k] _) 0 zR
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, middleCornerMap_add_left, ih]

theorem middleCornerMap_sum_right {α : Type*} (s : Finset α)
    (zL : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d))
    (w : α → WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)) :
    middleCornerMap zL (∑ i ∈ s, w i) = ∑ i ∈ s, middleCornerMap zL (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have h := middleCornerMap_add_right zL (0 : WeightedKLRAlgebra k Γ (a + b) ⊗[k] _) 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, middleCornerMap_add_right, ih]

end CornerMap

variable (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hΓ : Γ.PSymm)
  (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))
  {S' S : Set (I → ℕ)} (hS : IsLowerSet S) (hcS : ⇑c ∈ S) (hS' : Set.Iio ⇑c ⊆ S')
  (hS'l : IsLowerSet S') (hcS' : ⇑c ∉ S') (hc : ∀ μ' ∈ S, μ' ∉ S' → μ' = ⇑c)

include hS'l hcS' hc in
/-- `middleResIndMap` is injective. -/
theorem middleResIndMap_injective :
    Function.Injective (middleResIndMap hD hZ hP hΓ hW hL hS hcS hS') := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  have key : ∀ (L' : {C : FullChamber Γ (a + c) // C.IsRankOrdered})
      (L'' : {C : FullChamber Γ (b + d) // C.IsRankOrdered})
      (R' : {C : FullChamber Γ (a + b) // C.IsRankOrdered})
      (R'' : {C : FullChamber Γ (c + d) // C.IsRankOrdered}),
      middleCornerMap (rankE k L'.2 ⊗ₜ rankE k L''.2) (rankE k R'.2 ⊗ₜ rankE k R''.2) w = 0 := by
    intro L' L'' R' R''
    have hRc := (isRankOrdered_chamber_iff R'.1 R''.1).2 ⟨R'.2, R''.2⟩
    have hLc := (isRankOrdered_castChamber_chamber_iff (layout_eq a b c d) L'.1 L''.1).2
      ⟨L'.2, L''.2⟩
    set π := middleCornerMap (rankE k L'.2 ⊗ₜ rankE k L''.2) (rankE k R'.2 ⊗ₜ rankE k R''.2)
    have h1 : middleResIndMap hD hZ hP hΓ hW hL hS hcS hS' (π w) = 0 := by
      rw [← LinearMap.comp_apply,
        middleResIndMap_comp_middleCornerMap hD hZ hP hΓ hW hL hS hcS hS' hS'l,
        LinearMap.comp_apply, hw, map_zero]
    have h2 : middleTensorMap hP hD hZ hΓ hW hL hRc hLc hS hcS hS' (π w) = 0 := by
      rw [← resIndCornerProj_comp_middleResIndMap hD hZ hP hΓ hW hL hS hcS hS' hLc hRc,
        LinearMap.comp_apply, h1, map_zero]
    have h3 : (⟨π w, LinearMap.mem_range_self π w⟩ : LinearMap.range π) = 0 :=
      (middleCornerEquiv hP hD hZ hΓ hW hL L'.2 L''.2 R'.2 R''.2 hS hcS hS' hcS' hc).injective
        (by rw [map_zero]; exact h2)
    exact congrArg Subtype.val h3
  have hw1 : w = middleCornerMap 1 1 w := by rw [middleCornerMap_one_one, LinearMap.id_apply]
  rw [hw1, one_tensor_eq_sum (ν' := a + c) (ν'' := b + d),
    one_tensor_eq_sum (ν' := a + b) (ν'' := c + d)]
  simp only [middleCornerMap_sum_left, middleCornerMap_sum_right, LinearMap.sum_apply, key,
    Finset.sum_const_zero]

include hS'l hcS' hc in
/-- `middleResIndMap` is surjective. -/
theorem middleResIndMap_surjective :
    Function.Surjective (middleResIndMap hD hZ hP hΓ hW hL hS hcS hS') := by
  classical
  intro q
  rw [← LinearMap.mem_range]
  rw [← resIndSubquotientMul_one hP hD hZ hΓ hW hL _ _ hS'l hS q,
    one_tensor_eq_sum (ν' := a + c) (ν'' := b + d), one_tensor_eq_sum (ν' := a + b) (ν'' := c + d)]
  simp only [resIndSubquotientMul_sum_left]
  simp only [resIndSubquotientMul_sum_right]
  refine Submodule.sum_mem _ fun L' _ => Submodule.sum_mem _ fun L'' _ =>
    Submodule.sum_mem _ fun R' _ => Submodule.sum_mem _ fun R'' _ => ?_
  have hRc := (isRankOrdered_chamber_iff R'.1 R''.1).2 ⟨R'.2, R''.2⟩
  have hLc := (isRankOrdered_castChamber_chamber_iff (layout_eq a b c d) L'.1 L''.1).2
    ⟨L'.2, L''.2⟩
  have hu := inductionVal_rankE_tmul_rankE (k := k) (layout_eq a b c d) L'.2 L''.2
  have hw := inductionVal_rankE_tmul_rankE (k := k)
    (rfl : a + b + (c + d) = a + b + (c + d)) R'.2 R''.2
  set π := middleCornerMap (rankE k L'.2 ⊗ₜ rankE k L''.2) (rankE k R'.2 ⊗ₜ rankE k R''.2)
  set Φ := middleResIndMap hD hZ hP hΓ hW hL hS hcS hS'
  set corner := resIndCornerProj hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
    (layout_eq a b c d) (S' := S') (S := S) hLc hRc
  obtain ⟨⟨x, x₀, rfl⟩, hx⟩ := (middleCornerEquiv hP hD hZ hΓ hW hL L'.2 L''.2 R'.2 R''.2 hS hcS
    hS' hcS' hc).surjective (corner q)
  change middleTensorMap hP hD hZ hΓ hW hL hRc hLc hS hcS hS' (π x₀) = corner q at hx
  refine ⟨π x₀, ?_⟩
  have hΦπ : Φ (π x₀) = resIndSubquotientMul hP hD hZ hΓ hW hL _ _ hS'l hS
      (rankE k L'.2 ⊗ₜ rankE k L''.2) (rankE k R'.2 ⊗ₜ rankE k R''.2) (Φ x₀) := by
    rw [← LinearMap.comp_apply,
      middleResIndMap_comp_middleCornerMap hD hZ hP hΓ hW hL hS hcS hS' hS'l,
      LinearMap.comp_apply]
  rw [hΦπ, ← sub_eq_zero, ← map_sub]
  refine resIndSubquotientMul_eq_zero_of_corner hP hD hZ hΓ hW hL _ _ hS'l hS hLc hRc hu hw ?_
  rw [map_sub, sub_eq_zero, ← hx, ← LinearMap.comp_apply,
    resIndCornerProj_comp_middleResIndMap hD hZ hP hΓ hW hL hS hcS hS' hLc hRc,
    ← LinearMap.comp_apply (middleTensorMap hP hD hZ hΓ hW hL hRc hLc hS hcS hS') π,
    middleTensorMap_comp_middleCornerMap hP hD hZ hΓ hW hL L'.2 L''.2 R'.2 R''.2 hRc hLc hS hcS
      hS']

/-- **The subquotient of shuffle type `c` of the Mackey filtration of `Res ∘ Ind` is the middle
balanced tensor product** (B. Webster, arXiv:1209.2463v4, proof of Theorem 2.19; after
Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18). In the layout `ν' = a + b`, `ν'' = c + d`,
`ν₁ = a + c`, `ν₂ = b + d`, for a lower set `S ∋ c` of shuffle types whose only type outside the
lower set `S' ⊇ {μ < c}` is `c`, the map `t ⊗ y ↦ [ι(t) ψ_c ι(y)]` is a linear isomorphism
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d}) ≃ S / S'`; it is a bimodule map by
`middleResIndMap_comp_middleCornerMap`. The hypotheses `hP`, `hW`, `hL` are those of Webster,
Theorem 2.8, for the weight `a + b + c + d`. -/
noncomputable def middleResIndEquiv :
    MiddleTensor k Γ a b c d ≃ₗ[k]
      ResIndSubquotient k hP hD hZ hΓ hW hL (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) S' S :=
  LinearEquiv.ofBijective (middleResIndMap hD hZ hP hΓ hW hL hS hcS hS')
    ⟨middleResIndMap_injective hD hZ hP hΓ hW hL hS hcS hS' hS'l hcS' hc,
      middleResIndMap_surjective hD hZ hP hΓ hW hL hS hcS hS' hS'l hcS' hc⟩

theorem middleResIndEquiv_apply (x : MiddleTensor k Γ a b c d) :
    middleResIndEquiv hD hZ hP hΓ hW hL hS hcS hS' hS'l hcS' hc x =
      middleResIndMap hD hZ hP hΓ hW hL hS hcS hS' x := rfl

/-- **The subquotient of one shuffle type of the Mackey filtration of `Res ∘ Ind` is the middle
balanced tensor product, as a bimodule** (B. Webster, arXiv:1209.2463v4, proof of Theorem 2.19;
after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18), for arbitrary weights: if
`ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d` and `μ = c`, and `S` is a lower set of
shuffle types whose only type outside the lower set `S' ⊇ {μ' < μ}` is `μ`, there is a linear
isomorphism `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d}) ≃ S / S'` intertwining
`t ⊗ y ↦ z_L t ⊗ y z_R` with `[x] ↦ [ι(z_L) x ι(z_R)]`. The hypotheses `hP`, `hW`, `hL` are those
of Webster, Theorem 2.8, for the weight `ν`. -/
theorem exists_middleResInd_equiv {ν ν' ν'' ν₁ ν₂ : I →₀ ℕ}
    {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
    (hP : ∀ C E, IsChamberSegment C E (P C E)) (hΓ : Γ.PSymm)
    (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
    (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand ν), Γ.loop s.1 = some Q → s ≠ t →
      s.1 = t.1 → IsRegular (loopFactor Q s t))
    (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) {S' S : Set (I → ℕ)} (hS : IsLowerSet S)
    (hS'l : IsLowerSet S') {μ : I → ℕ} (hμS : μ ∈ S) (hlow : Set.Iio μ ⊆ S') (hμS' : μ ∉ S')
    (hone : ∀ μ' ∈ S, μ' ∉ S' → μ' = μ) (hab : a + b = ν') (hcd : c + d = ν'')
    (hac : a + c = ν₁) (hbd : b + d = ν₂) (hμc : μ = ⇑c) :
    ∃ f : MiddleTensor k Γ a b c d ≃ₗ[k]
        ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S,
      ∀ zL zR, f.toLinearMap ∘ₗ middleCornerMap zL zR =
        resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS'l hS
            (Algebra.TensorProduct.congr (castW k Γ hac) (castW k Γ hbd) zL)
            (Algebra.TensorProduct.congr (castW k Γ hab) (castW k Γ hcd) zR) ∘ₗ
          f.toLinearMap := by
  subst hab hcd hac hbd hμc hν'
  refine ⟨middleResIndEquiv hD hZ hP hΓ hW hL hS hμS hlow hS'l hμS' hone, fun zL zR => ?_⟩
  have h := middleResIndMap_comp_middleCornerMap hD hZ hP hΓ hW hL hS hμS hlow hS'l zL zR
  simp only [castW, Algebra.TensorProduct.congr_refl]
  exact h

end Juxtapose

end Categorification.WeightedKLR
