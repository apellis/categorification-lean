/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.TypeTensor

/-!
# The corners of `Res ∘ Ind`

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19. The bimodule `Res_{ν₁,ν₂} Ind_{ν',ν''} W` is
`ι(1) W_ν ι(1)`, and `ι(1)` is the sum of the idempotents `e (chamber C' C'')` of the
juxtapositions of rank-ordered chambers (`GalleryAlgebra.inductionVal_one`). So the corners
`e D W_ν e C` of `Res ∘ Ind` are those with `D` a juxtaposition for `ν₁ + ν₂` and `C` a
juxtaposition for `ν' + ν''`, both rank-ordered.

Such chambers are separated by the strands of the left factor
(`Juxtapose.isSeparated_castChamber_chamber`), so the separation hypotheses of the surjectivity
theorems of the Mackey subquotients hold automatically for these corners
(`GalleryAlgebra.exists_layout_middleTensor_surjective_of_chamber`,
`Juxtapose.middleTensorMap_surjective_of_chamber`).

For any other rank-ordered corner the separation hypotheses cannot be dropped: if `C` is not
separated by the strands of `ν'` (or `D` by those of `ν₁`), then `ι(y) e C = 0` (or
`e D ι(x) = 0`), so the map `x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]` is zero
(`GalleryAlgebra.typeInductionMap_eq_zero_of_not_isSeparated_right`, `..._left`), while the
subquotient of a shuffle type `μ ∈ S \ S'` is nonzero
(`GalleryAlgebra.nontrivial_mackeySubquotient`).
So the map is not surjective (`GalleryAlgebra.typeInductionMap_not_surjective_of_not_isSeparated`).

## Main results

* `GalleryAlgebra.inductionVal_one`: `ι(1)` is the sum of the idempotents of juxtapositions.
* `GalleryAlgebra.exists_layout_middleTensor_surjective_of_chamber`,
  `Juxtapose.middleTensorMap_surjective_of_chamber`: surjectivity onto the subquotients for the
  corners of `Res ∘ Ind`, with no separation hypothesis.
* `GalleryAlgebra.typeInductionMap_not_surjective_of_not_isSeparated`: the separation hypotheses
  are needed for other corners.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

namespace Juxtapose

omit [DecidableEq I] in
/-- A juxtaposition, read in `ν` along `ν' + ν'' = ν`, is separated by the strands of `ν'`. -/
theorem isSeparated_castChamber_chamber (h : ν' + ν'' = ν) (C' : FullChamber Γ ν')
    (C'' : FullChamber Γ ν'') :
    IsSeparated (fun t => decide (t.IsLeft ν')) (castChamber h (chamber C' C'')) := by
  subst h
  exact isSeparated_chamber C' C''

omit [DecidableEq I] in
theorem isRankOrdered_castChamber_chamber_iff (h : ν' + ν'' = ν) (C' : FullChamber Γ ν')
    (C'' : FullChamber Γ ν'') :
    (castChamber h (chamber C' C'')).IsRankOrdered ↔ C'.IsRankOrdered ∧ C''.IsRankOrdered := by
  subst h
  exact isRankOrdered_chamber_iff C' C''

end Juxtapose

namespace GalleryAlgebra

/-- **The unit of `Res ∘ Ind`**: `ι(1)`, read in `W_ν` along `ν₁ + ν₂ = ν`, is the sum of the
idempotents of the juxtapositions of rank-ordered chambers. -/
theorem inductionVal_one (hν : ν₁ + ν₂ = ν) :
    inductionVal k hν 1 =
      ∑ C' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
        ∑ C'' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
          e (castChamber hν (chamber (Γ := Γ) C' C'')) := by
  have hcast : ∀ {ν μ : I →₀ ℕ} (h : ν = μ) (C : FullChamber Γ ν),
      castGallery k Γ h (e C) = e (castChamber h C) := fun h C => by
    subst h
    rfl
  rw [inductionVal_apply, inductionMap_one, splitIdem, map_sum]
  simp only [map_sum, hcast]

/-- If `C` is not separated by the strands of `ν₁`, then `ι(y) e C = 0`. -/
theorem inductionVal_mul_e_eq_zero (hν : ν₁ + ν₂ = ν) {C : FullChamber Γ ν}
    (hC : ¬ IsSeparated (fun t => decide (t.IsLeft ν₁)) C)
    (y : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) :
    inductionVal k hν y * e C = 0 := by
  rw [← mul_one y, inductionVal_mul, mul_assoc, inductionVal_one, Finset.sum_mul,
    Finset.sum_eq_zero fun C' _ => ?_, mul_zero]
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun C'' _ => ?_
  rw [e_mul_e, ite_eq_right_iff]
  intro hEq
  exact absurd (hEq ▸ isSeparated_castChamber_chamber hν C' C'') hC

/-- If `D` is not separated by the strands of `ν₁`, then `e D ι(x) = 0`. -/
theorem e_mul_inductionVal_eq_zero (hν : ν₁ + ν₂ = ν) {D : FullChamber Γ ν}
    (hD : ¬ IsSeparated (fun t => decide (t.IsLeft ν₁)) D)
    (x : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) :
    e D * inductionVal k hν x = 0 := by
  rw [← one_mul x, inductionVal_mul, ← mul_assoc, inductionVal_one, Finset.mul_sum,
    Finset.sum_eq_zero fun C' _ => ?_, zero_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_eq_zero fun C'' _ => ?_
  rw [e_mul_e, ite_eq_right_iff]
  intro hEq
  exact absurd (hEq ▸ isSeparated_castChamber_chamber hν C' C'') hD

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand ν), Γ.loop s.1 = some Q → s ≠ t →
    s.1 = t.1 → IsRegular (loopFactor Q s t))

/-- **The map of a shuffle type vanishes off the corners of `Res ∘ Ind`, on the right**: if `C`
is not separated by the strands of `ν'`, then `x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]` is zero. -/
theorem typeInductionMap_eq_zero_of_not_isSeparated_right (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : ¬ IsSeparated (fun t => decide (t.IsLeft ν')) C) (S' : Set (I → ℕ))
    {S : Set (I → ℕ)} (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) :
    typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hμS hμ = 0 := by
  refine TensorProduct.ext' fun x y => ?_
  rw [typeInductionMap_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  have h0 : typeInductionAux k hD hZ hν' hν₁ D C (blockLeft ν' ν₁ μ) (x ⊗ₜ y) = 0 := by
    rw [typeInductionAux_tmul, mul_assoc, inductionVal_mul_e_eq_zero hν' hCs, mul_zero]
  simp only [h0]
  exact Submodule.zero_mem _

/-- **The map of a shuffle type vanishes off the corners of `Res ∘ Ind`, on the left**: if `D`
is not separated by the strands of `ν₁`, then `x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]` is zero. -/
theorem typeInductionMap_eq_zero_of_not_isSeparated_left (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hDs : ¬ IsSeparated (fun t => decide (t.IsLeft ν₁)) D) (S' : Set (I → ℕ))
    {S : Set (I → ℕ)} (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) :
    typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hμS hμ = 0 := by
  refine TensorProduct.ext' fun x y => ?_
  rw [typeInductionMap_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
  have h0 : typeInductionAux k hD hZ hν' hν₁ D C (blockLeft ν' ν₁ μ) (x ⊗ₜ y) = 0 := by
    rw [typeInductionAux_tmul, e_mul_inductionVal_eq_zero hν₁ hDs]
    simp only [zero_mul]
  simp only [h0]
  exact Submodule.zero_mem _

/-- **The subquotient of a shuffle type is nonzero**: for a shuffle type `μ` of a relabelling,
with `μ ∈ S` and `μ ∉ S'`, the quotient of the step `S` of the Mackey filtration of `e D W e C`
by the step `S'` is nontrivial. -/
theorem nontrivial_mackeySubquotient [Nontrivial k] (ν' ν₁ : I →₀ ℕ) (D C : FullChamber Γ ν)
    {S' S : Set (I → ℕ)} (h : S' ⊆ S) {μ : I → ℕ} (hμS : μ ∈ S) (hμS' : μ ∉ S')
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) :
    Nontrivial (MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S) := by
  obtain ⟨g, hg⟩ := hμ
  let j : ({i | shuffleType ν' ν₁ i.1.1 ∈ S'}ᶜ :
      Set {i : ColPerm ν × (Strand ν →₀ ℕ) // shuffleType ν' ν₁ i.1 ∈ S}) :=
    ⟨⟨(g, 0), by simpa [hg] using hμS⟩, by simpa [hg] using hμS'⟩
  exact ⟨⟨_, 0, (mackeySubquotientBasis hP hD hZ hΓ hW hL ν' ν₁ D C h).ne_zero j⟩⟩

/-- **The separation hypotheses are needed.** If `C` is not separated by the strands of `ν'`, or
`D` is not separated by the strands of `ν₁`, then for a shuffle type `μ ∈ S \ S'` the map
`x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]` is not onto the subquotient of the Mackey filtration. -/
theorem typeInductionMap_not_surjective_of_not_isSeparated [Nontrivial k] (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hsep : ¬ IsSeparated (fun t => decide (t.IsLeft ν')) C ∨
      ¬ IsSeparated (fun t => decide (t.IsLeft ν₁)) D)
    {S' S : Set (I → ℕ)} (h : S' ⊆ S) (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμS' : μ ∉ S') (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) :
    ¬ Function.Surjective (typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hμS hμ) := by
  have := nontrivial_mackeySubquotient hP hD hZ hΓ hW hL ν' ν₁ D C h hμS hμS' hμ
  have h0 : typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hμS hμ = 0 := by
    rcases hsep with hCs | hDs
    · exact typeInductionMap_eq_zero_of_not_isSeparated_right hP hD hZ hΓ hW hL hν' hν₁ hC hD'
        hCs S' hS hμS hμ
    · exact typeInductionMap_eq_zero_of_not_isSeparated_left hP hD hZ hΓ hW hL hν' hν₁ hC hD'
        hDs S' hS hμS hμ
  rw [h0]
  intro hs
  obtain ⟨z, hz⟩ := exists_ne (0 : MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S)
  obtain ⟨w, hw⟩ := hs z
  exact hz (hw ▸ LinearMap.zero_apply w)

/-- **The subquotient of a single shuffle type of a corner of `Res ∘ Ind` is a quotient of a
balanced tensor product** (B. Webster, arXiv:1209.2463v4, Theorem 2.19, surjectivity half).
This is `exists_layout_middleTensor_surjective` for the corners `e D W e C` of
`Res_{ν₁,ν₂} Ind_{ν',ν''}`: `C` the juxtaposition of chambers for `ν'` and `ν''`, `D` that of
chambers for `ν₁` and `ν₂`, both rank-ordered. The separation hypotheses hold automatically. -/
theorem exists_layout_middleTensor_surjective_of_chamber (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) {C' : FullChamber Γ ν'} {C'' : FullChamber Γ ν''}
    {D' : FullChamber Γ ν₁} {D'' : FullChamber Γ ν₂}
    (hC : (castChamber hν' (chamber C' C'')).IsRankOrdered)
    (hD' : (castChamber hν₁ (chamber D' D'')).IsRankOrdered) {S' S : Set (I → ℕ)}
    (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) (hlow : Set.Iio μ ⊆ S')
    (hone : ∀ μ' ∈ S, μ' ∉ S' → μ' = μ) :
    ∃ (a b c d : I →₀ ℕ) (hab : a + b = ν') (hcd : c + d = ν'') (hac : a + c = ν₁)
      (hbd : b + d = ν₂), μ = ⇑c ∧ ∃ f : MiddleTensor k Γ a b c d →ₗ[k]
        MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ (castChamber hν₁ (chamber D' D''))
          (castChamber hν' (chamber C' C'')) S' S,
      Function.Surjective f ∧ ∀ t y, f (BalancedTensor.tmul t y) =
        typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hμS hμ
          (Algebra.TensorProduct.congr (castW k Γ hac) (castW k Γ hbd) t.1 ⊗ₜ
            Algebra.TensorProduct.congr (castW k Γ hab) (castW k Γ hcd) y.1) :=
  exists_layout_middleTensor_surjective hP hD hZ hΓ hW hL hν' hν₁ hC hD'
    (isSeparated_castChamber_chamber hν' C' C'') (isSeparated_castChamber_chamber hν₁ D' D'') hS
    hμS hμ hlow hone

end GalleryAlgebra

namespace Juxtapose

variable {a b c d : I →₀ ℕ}
  {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))),
    Γ.loop s.1 = some Q → s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))

/-- **The descended map is onto the subquotient of `c`, for the corners of `Res ∘ Ind`**: the
form of `middleTensorMap_surjective` for `R` the juxtaposition of chambers for `a + b` and
`c + d` and `L` that of chambers for `a + c` and `b + d`, with no separation hypothesis. -/
theorem middleTensorMap_surjective_of_chamber {R' : FullChamber Γ (a + b)}
    {R'' : FullChamber Γ (c + d)} {L' : FullChamber Γ (a + c)} {L'' : FullChamber Γ (b + d)}
    (hR : (chamber R' R'').IsRankOrdered)
    (hL' : (castChamber (layout_eq a b c d) (chamber L' L'')).IsRankOrdered)
    {S' S : Set (I → ℕ)} (hS : IsLowerSet S) (hcS : ⇑c ∈ S) (hS' : Set.Iio ⇑c ⊆ S')
    (hc : ∀ μ' ∈ S, μ' ∉ S' → μ' = ⇑c) :
    Function.Surjective (middleTensorMap hP hD hZ hΓ hW hL hR hL' hS hcS hS') :=
  middleTensorMap_surjective hP hD hZ hΓ hW hL hR hL' hS hcS hS' (isSeparated_chamber R' R'')
    (isSeparated_castChamber_chamber (layout_eq a b c d) L' L'') hc

end Juxtapose

end Categorification.WeightedKLR
