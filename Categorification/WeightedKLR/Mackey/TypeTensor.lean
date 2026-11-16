/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockTensor

/-!
# The subquotient of a shuffle type as a quotient of a balanced tensor product

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19. Every shuffle type `μ` of `ν = ν' + ν'' = ν₁ + ν₂` comes from a
four-block layout: `ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d` with `c = μ`
(`exists_layout_of_shuffleType`). Transporting along these equalities, the subquotient of the
Mackey filtration of the single shuffle type `μ` is the image of the balanced tensor product
`(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})` under `x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]`
(`GalleryAlgebra.exists_middleTensor_surjective`).

## Main results

* `exists_layout_of_shuffleType`: the four-block layout of a shuffle type.
* `GalleryAlgebra.exists_middleTensor_surjective`: the descended map onto the subquotient of a
  single shuffle type, for arbitrary `ν', ν'', ν₁, ν₂` and a given layout.
* `GalleryAlgebra.exists_layout_middleTensor_surjective`: the same, with the layout found from
  the shuffle type.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

/-- The colour counts of a shuffle type: at every colour `i`, `μ i ≤ ν₁ i`, `μ i ≤ ν'' i` and
`ν₁ i ≤ ν' i + μ i`. -/
theorem shuffleType_le (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (y : ColPerm ν) (i : I) :
    shuffleType ν' ν₁ y i ≤ ν₁ i ∧ shuffleType ν' ν₁ y i ≤ ν'' i ∧
      ν₁ i ≤ ν' i + shuffleType ν' ν₁ y i := by
  classical
  by_cases hi : i ∈ ν.support
  · set j : ν.support := ⟨i, hi⟩
    have hcol : ∀ t : Strand ν, t.1.1 = i ↔ t.1 = j := fun t => ⟨fun h => Subtype.ext h,
      fun h => by rw [h]⟩
    have hY := card_filter_isLeft_colPerm hν₁ y j
    have hL := card_filter_isLeft_colPerm hν' 1 j
    have hT := card_filter_isLeft_colPerm (add_zero ν) 1 j
    have hνi := congrArg (fun f : I →₀ ℕ => f i) hν'
    simp only [Finsupp.add_apply] at hνi
    have e1 : (Finset.univ.filter fun t : Strand ν => t.1 = j ∧
        ((1 : ColPerm ν).1 t).IsLeft ν) = Finset.univ.filter fun t : Strand ν => t.1 = j := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      intro _
      exact t.2.isLt
    rw [e1] at hT
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun t : Strand ν => t.1 = j) (fun t => t.IsLeft ν')
    simp only [Finset.filter_filter] at hsplit
    have hμ : shuffleType ν' ν₁ y i = (Finset.univ.filter fun t : Strand ν =>
        t.1 = j ∧ ¬ t.IsLeft ν' ∧ (y.1 t).IsLeft ν₁).card := by
      simp only [shuffleType, hcol]
    have hL' : (Finset.univ.filter fun t : Strand ν => t.1 = j ∧ t.IsLeft ν').card = ν' i := hL
    refine ⟨?_, ?_, ?_⟩
    · rw [hμ, ← hY]
      refine Finset.card_le_card fun t ht => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨ht.1, ht.2.2⟩
    · rw [hμ]
      refine (Finset.card_le_card (t := Finset.univ.filter fun t : Strand ν =>
        t.1 = j ∧ ¬ t.IsLeft ν') fun t ht => ?_).trans ?_
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        exact ⟨ht.1, ht.2.1⟩
      · have h1 : ν j.1 = ν' j.1 + ν'' j.1 := hνi.symm
        have h2 : (Finset.univ.filter fun t : Strand ν => t.1 = j ∧ t.IsLeft ν').card =
          ν' j.1 := hL'
        have h3 : (Finset.univ.filter fun t : Strand ν => t.1 = j).card = ν j.1 := hT
        refine Nat.le_of_add_le_add_left (a := ν' j.1) ?_
        rw [← h1, ← h3, ← hsplit, h2]
    · rw [hμ, ← hY, ← hL']
      refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at ht ⊢
      by_cases h : t.IsLeft ν'
      · exact Or.inl ⟨ht.1, h⟩
      · exact Or.inr ⟨ht.1, h, ht.2⟩
  · have h0 : ν i = 0 := Finsupp.notMem_support_iff.1 hi
    have h1 := congrArg (fun f : I →₀ ℕ => f i) hν'
    have h2 := congrArg (fun f : I →₀ ℕ => f i) hν₁
    simp only [Finsupp.add_apply, h0] at h1 h2
    have h3 : shuffleType ν' ν₁ y i = 0 := by
      refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun t _ h => ?_)
      exact hi (h.1 ▸ t.1.2)
    omega

/-- **The four-block layout of a shuffle type.** Every shuffle type `μ` of a relabelling of
`ν = ν' + ν'' = ν₁ + ν₂` comes from a layout `ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`,
`ν₂ = b + d` with `c = μ`: `a = ν₁ - μ`, `b = ν' - a`, `d = ν'' - μ`. -/
theorem exists_layout_of_shuffleType (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (y : ColPerm ν) :
    ∃ a b c d : I →₀ ℕ, a + b = ν' ∧ c + d = ν'' ∧ a + c = ν₁ ∧ b + d = ν₂ ∧
      ⇑c = shuffleType ν' ν₁ y := by
  classical
  let c : I →₀ ℕ := Finsupp.onFinset ν₁.support (shuffleType ν' ν₁ y) fun i hi =>
    Finsupp.mem_support_iff.2 fun h0 => hi (by
      have := (shuffleType_le hν' hν₁ y i).1
      omega)
  have hc : ∀ i, c i = shuffleType ν' ν₁ y i := fun i => Finsupp.onFinset_apply
  have h := fun i => shuffleType_le hν' hν₁ y i
  have e1 := fun i => congrArg (fun f : I →₀ ℕ => f i) hν'
  have e2 := fun i => congrArg (fun f : I →₀ ℕ => f i) hν₁
  simp only [Finsupp.add_apply] at e1 e2
  refine ⟨ν₁ - c, ν' - (ν₁ - c), c, ν'' - c, ?_, ?_, ?_, ?_, funext hc⟩ <;> ext i <;>
    simp only [Finsupp.add_apply, Finsupp.coe_tsub, Pi.sub_apply, hc] <;>
    · have := h i
      have := e1 i
      have := e2 i
      omega

namespace GalleryAlgebra

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand ν), Γ.loop s.1 = some Q → s ≠ t →
    s.1 = t.1 → IsRegular (loopFactor Q s t))

/-- **The subquotient of a single shuffle type is a quotient of a balanced tensor product** (the
surjectivity half of the identification of the subquotients of the Mackey filtration in
B. Webster, arXiv:1209.2463v4, Theorem 2.19). Let `C`, `D` be rank-ordered, with the strands of
`ν'` to the left in `C` and those of `ν₁` to the left in `D`; let `μ` be a shuffle type with the
layout `ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d`, `c = μ`
(`exists_layout_of_shuffleType`), the only type in `S` but not in `S'`, with all types below `μ`
in `S'`. Then `x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]` (read along these equalities) descends to a
surjection from `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})`,
`W' = (W_a ⊗ W_b) ⊗ (W_c ⊗ W_d)`, onto the quotient of the step `S` of the filtration of
`e D * A * e C` by the step `S'`. -/
theorem exists_middleTensor_surjective (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) {S' S : Set (I → ℕ)}
    (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) (hlow : Set.Iio μ ⊆ S')
    (hone : ∀ μ' ∈ S, μ' ∉ S' → μ' = μ) {a b c d : I →₀ ℕ} (hab : a + b = ν')
    (hcd : c + d = ν'') (hac : a + c = ν₁) (hbd : b + d = ν₂) (hμc : μ = ⇑c) :
    ∃ f : MiddleTensor k Γ a b c d →ₗ[k]
        MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S,
      Function.Surjective f ∧ ∀ t y, f (BalancedTensor.tmul t y) =
        typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hμS hμ
          (Algebra.TensorProduct.congr (castW k Γ hac) (castW k Γ hbd) t.1 ⊗ₜ
            Algebra.TensorProduct.congr (castW k Γ hab) (castW k Γ hcd) y.1) := by
  subst hab hcd hac hbd hμc hν'
  refine ⟨middleTensorMap hP hD hZ hΓ hW hL hC hD' hS hμS hlow,
    middleTensorMap_surjective hP hD hZ hΓ hW hL hC hD' hS hμS hlow hCs hDs hone,
    fun t y => ?_⟩
  rw [middleTensorMap_tmul]
  congr 1
  simp only [castW, Algebra.TensorProduct.congr_refl]
  rfl

/-- **The subquotient of a single shuffle type is a quotient of a balanced tensor product**, with
the layout of the shuffle type found by `exists_layout_of_shuffleType` (B. Webster,
arXiv:1209.2463v4, Theorem 2.19, surjectivity half): for every shuffle type `μ` of a relabelling
there are `a, b, c, d` with `ν' = a + b`, `ν'' = c + d`, `ν₁ = a + c`, `ν₂ = b + d`, `c = μ` and a
surjection from `(W_{a+c} ⊗ W_{b+d}) e' ⊗_{W'} e (W_{a+b} ⊗ W_{c+d})` onto the subquotient of `μ`,
given by `x ⊗ y ↦ [e D ι(x) ψ_μ ι(y) e C]`. -/
theorem exists_layout_middleTensor_surjective (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {D C : FullChamber Γ ν} (hC : C.IsRankOrdered) (hD' : D.IsRankOrdered)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C)
    (hDs : IsSeparated (fun t => decide (t.IsLeft ν₁)) D) {S' S : Set (I → ℕ)}
    (hS : IsLowerSet S) {μ : I → ℕ} (hμS : μ ∈ S)
    (hμ : μ ∈ Set.range (shuffleType (ν := ν) ν' ν₁)) (hlow : Set.Iio μ ⊆ S')
    (hone : ∀ μ' ∈ S, μ' ∉ S' → μ' = μ) :
    ∃ (a b c d : I →₀ ℕ) (hab : a + b = ν') (hcd : c + d = ν'') (hac : a + c = ν₁)
      (hbd : b + d = ν₂), μ = ⇑c ∧ ∃ f : MiddleTensor k Γ a b c d →ₗ[k]
        MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S,
      Function.Surjective f ∧ ∀ t y, f (BalancedTensor.tmul t y) =
        typeInductionMap k hP hD hZ hΓ hW hL hν' hν₁ hC hD' S' hS hμS hμ
          (Algebra.TensorProduct.congr (castW k Γ hac) (castW k Γ hbd) t.1 ⊗ₜ
            Algebra.TensorProduct.congr (castW k Γ hab) (castW k Γ hcd) y.1) := by
  obtain ⟨g, rfl⟩ := id hμ
  obtain ⟨a, b, c, d, hab, hcd, hac, hbd, hc⟩ := exists_layout_of_shuffleType hν' hν₁ g
  exact ⟨a, b, c, d, hab, hcd, hac, hbd, hc.symm, exists_middleTensor_surjective hP hD hZ hΓ hW
    hL hν' hν₁ hC hD' hCs hDs hS hμS hμ hlow hone hab hcd hac hbd hc.symm⟩

end GalleryAlgebra

end Categorification.WeightedKLR
