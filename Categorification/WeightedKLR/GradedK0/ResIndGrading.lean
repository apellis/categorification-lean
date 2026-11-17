/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.MiddleResIndEquiv
import Categorification.WeightedKLR.Mackey.MiddleGraded
import Categorification.WeightedKLR.GradedK0.Grading

/-!
# The grading of the Mackey filtration of `Res ∘ Ind`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19, filters the bimodule `e_{ν₁;ν₂} W_ν e_{ν';ν''}` by shuffle types
(`GalleryAlgebra.resIndFilt`). This file shows that each step of that filtration is a homogeneous
subspace of the graded algebra `W_ν`: the idempotents `e_{ν₁;ν₂} = ι(1)`, `e_{ν';ν''} = ι(1)` and
the chamber idempotents `e D` have degree `0`, and the corner steps are homogeneous
(`GalleryAlgebra.decompose_mem_mackeyFilt`). This is the first step of the graded form of the
Mackey filtration.

## Main results
* `inductionVal_one_mem_grade`: `ι_{ν₁;ν₂}(1)` has degree `0`.
* `decompose_mem_resIndFilt`: the degree components of an element of a step lie in that step.
* `resIndFiltGrading`, `resIndFiltProj`: the grading of a step and its degree projections.
* `resIndSubquotientGrading`, `resIndSubquotientProj`: the induced grading of the subquotients
  `ResIndSubquotient S' S`, with degree projections.
* `Juxtapose.middleAux_mem_grade`, `Juxtapose.middleResIndMap_mem_grading`: the comparison map
  `t ⊗ y ↦ [ι(t) ψ_c ι(y)]` raises degrees by `middleShift`.
* `Juxtapose.iSup_middleGrading`: the middle balanced tensor product is spanned by homogeneous
  vectors.
* `Juxtapose.middleResIndGradedEquiv`, `Juxtapose.middleResIndGradedEquivIic`: the subquotient of shuffle type `c` is the middle balanced
  tensor product shifted by `middleShift`, as a graded space.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose _root_.Categorification.Graded

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

attribute [local instance] ColPerm.fintype

namespace GalleryAlgebra

variable {ν₁ ν₂ ν' ν'' : I →₀ ℕ}

/-- The idempotent `ι_{ν₁;ν₂}(1)` of `W_ν` has degree `0`. -/
theorem inductionVal_one_mem_grade (G : GradingDatum Γ) (hν : ν₁ + ν₂ = ν) :
    inductionVal k hν 1 ∈ G.grade ν 0 := by
  have h := inductionVal_tmul_mem_grade G hν (x := 1) (y := 1)
    (rankIdem_mem_grade G ν₁) (rankIdem_mem_grade G ν₂)
  rwa [← Algebra.TensorProduct.one_def, add_zero] at h

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b)) (G : GradingDatum Γ)

/-- **The steps of the Mackey filtration of `Res ∘ Ind` are homogeneous** (Webster,
arXiv:1209.2463v4, proof of Theorem 2.19). -/
theorem decompose_mem_resIndFilt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S : Set (I → ℕ))
    {z : GalleryAlgebra k Γ ν} (hz : z ∈ resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S) (n : ℤ) :
    (DirectSum.decompose (G.grade ν) z n : GalleryAlgebra k Γ ν) ∈
      resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S := by
  have h₁ := inductionVal_one_mem_grade G hν₁
  have h' := inductionVal_one_mem_grade G hν'
  refine ⟨?_, ?_, fun D C hD' hC' => ?_⟩
  · rw [← DirectSum.coe_decompose_mul_of_left_mem_zero (G.grade ν) h₁, hz.1]
  · rw [← DirectSum.coe_decompose_mul_of_right_mem_zero (G.grade ν) h', hz.2.1]
  · rw [← DirectSum.coe_decompose_mul_of_left_mem_zero (G.grade ν) (G.e_mem_grade D),
      ← DirectSum.coe_decompose_mul_of_right_mem_zero (G.grade ν) (G.e_mem_grade C)]
    exact decompose_mem_mackeyFilt hP hD hZ hΓ hW hL G ν' ν₁ D C S (hz.2.2 D C hD' hC') n

/-- The grading of a step of the Mackey filtration of `Res ∘ Ind`. -/
noncomputable def resIndFiltGrading (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S : Set (I → ℕ))
    (n : ℤ) : Submodule k (resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S) :=
  (G.grade ν n).comap (resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S).subtype

/-- The degree `n` projection on a step of the Mackey filtration of `Res ∘ Ind`. -/
noncomputable def resIndFiltProj (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S : Set (I → ℕ))
    (n : ℤ) :
    resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S →ₗ[k] resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S :=
  ((GradedAlgebra.proj (G.grade ν) n).comp (resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S).subtype)
    |>.codRestrict _ fun x => decompose_mem_resIndFilt hP hD hZ hΓ hW hL G hν' hν₁ S x.2 n

theorem resIndFiltProj_mem (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S : Set (I → ℕ)) (n : ℤ)
    (x : resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S) :
    resIndFiltProj hP hD hZ hΓ hW hL G hν' hν₁ S n x ∈
      resIndFiltGrading hP hD hZ hΓ hW hL G hν' hν₁ S n :=
  (DirectSum.decompose (G.grade ν) (x : GalleryAlgebra k Γ ν) n).2

/-- A step of the Mackey filtration is the sum of its homogeneous components. -/
theorem iSup_resIndFiltGrading (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S : Set (I → ℕ)) :
    ⨆ n, resIndFiltGrading hP hD hZ hΓ hW hL G hν' hν₁ S n = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x = ∑ n ∈ (DirectSum.decompose (G.grade ν) (x : GalleryAlgebra k Γ ν)).support,
      resIndFiltProj hP hD hZ hΓ hW hL G hν' hν₁ S n x := by
    refine Subtype.ext ?_
    simp only [resIndFiltProj, Submodule.coe_sum]
    exact (DirectSum.sum_support_decompose (G.grade ν) (x : GalleryAlgebra k Γ ν)).symm
  rw [hx]
  exact Submodule.sum_mem _ fun n _ =>
    Submodule.mem_iSup_of_mem n (resIndFiltProj_mem hP hD hZ hΓ hW hL G hν' hν₁ S n x)

/-- The grading of the subquotient `S / S'` of the Mackey filtration of `Res ∘ Ind`: the image of
the homogeneous elements of the step `S`. -/
noncomputable def resIndSubquotientGrading (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (S' S : Set (I → ℕ)) (n : ℤ) :
    Submodule k (ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S) :=
  (resIndFiltGrading hP hD hZ hΓ hW hL G hν' hν₁ S n).map (Submodule.mkQ _)

/-- The degree `n` projection on the subquotient `S / S'` of the Mackey filtration of
`Res ∘ Ind`. -/
noncomputable def resIndSubquotientProj (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (S' S : Set (I → ℕ)) (n : ℤ) :
    ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S →ₗ[k]
      ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S :=
  Submodule.mapQ _ _ (resIndFiltProj hP hD hZ hΓ hW hL G hν' hν₁ S n) fun _ hx =>
    decompose_mem_resIndFilt hP hD hZ hΓ hW hL G hν' hν₁ S' hx n

theorem resIndSubquotientProj_of_mem (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (S' S : Set (I → ℕ)) ⦃n : ℤ⦄ ⦃y : ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S⦄
    (hy : y ∈ resIndSubquotientGrading hP hD hZ hΓ hW hL G hν' hν₁ S' S n) :
    resIndSubquotientProj hP hD hZ hΓ hW hL G hν' hν₁ S' S n y = y := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  refine congrArg (Submodule.mkQ _) (Subtype.ext ?_)
  exact DirectSum.decompose_of_mem_same (G.grade ν) hx

theorem resIndSubquotientProj_of_mem_ne (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (S' S : Set (I → ℕ)) ⦃n n' : ℤ⦄ ⦃y : ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S⦄
    (hy : y ∈ resIndSubquotientGrading hP hD hZ hΓ hW hL G hν' hν₁ S' S n') (h : n' ≠ n) :
    resIndSubquotientProj hP hD hZ hΓ hW hL G hν' hν₁ S' S n y = 0 := by
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  refine (congrArg (Submodule.mkQ _) (Subtype.ext ?_)).trans (map_zero _)
  exact DirectSum.decompose_of_mem_ne (G.grade ν) hx h

/-- The subquotient `S / S'` is the sum of its homogeneous components. -/
theorem iSup_resIndSubquotientGrading (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (S' S : Set (I → ℕ)) :
    ⨆ n, resIndSubquotientGrading hP hD hZ hΓ hW hL G hν' hν₁ S' S n = ⊤ := by
  simp only [resIndSubquotientGrading, ← Submodule.map_iSup,
    iSup_resIndFiltGrading hP hD hZ hΓ hW hL G hν' hν₁ S, Submodule.map_top, Submodule.range_mkQ]

end GalleryAlgebra

namespace Juxtapose

variable {a b c d : I →₀ ℕ} (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (G : GradingDatum Γ)

/-- **`middleAux` raises degrees by `middleShift`**: for `t` of degree `i` and `y` of degree `j`,
`ι(t) ψ_c ι(y)` has degree `i + middleShift + j` (Webster, arXiv:1209.2463v4, proof of
Theorem 2.19). -/
theorem middleAux_mem_grade {i j : ℤ}
    {t : WeightedKLRAlgebra k Γ (a + c) ⊗[k] WeightedKLRAlgebra k Γ (b + d)}
    (ht : t ∈ tensorGrading (G.klrGrade (a + c)) (G.klrGrade (b + d)) i)
    {y : WeightedKLRAlgebra k Γ (a + b) ⊗[k] WeightedKLRAlgebra k Γ (c + d)}
    (hy : y ∈ tensorGrading (G.klrGrade (a + b)) (G.klrGrade (c + d)) j) :
    middleAux k hD hZ (t ⊗ₜ y) ∈
      G.grade (a + b + (c + d)) (i + middleShift G a b c d + j) := by
  have h := inductionVal_one_mul_middleAux hD hZ (t ⊗ₜ y)
  have hz : middleAux k hD hZ (t ⊗ₜ y) = inductionVal k (layout_eq a b c d) 1 *
      middleAux k hD hZ (t ⊗ₜ y) * inductionVal k (rfl : a + b + (c + d) = a + b + (c + d)) 1 := by
    rw [h.1, h.2]
  rw [hz, inductionVal_one_mul_mul_one]
  refine Submodule.sum_mem _ fun _ _ => Submodule.sum_mem _ fun _ _ =>
    Submodule.sum_mem _ fun _ _ => Submodule.sum_mem _ fun _ _ => ?_
  rw [e_mul_middleAux_mul_e]
  exact typeInductionAux_middle_mem_grade G hD hZ _ _ ht hy

section Descent

variable {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hΓ : Γ.PSymm)
  (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))
  {S' S : Set (I → ℕ)} (hS : IsLowerSet S) (hcS : ⇑c ∈ S)

/-- **The comparison map of the middle parabolic raises degrees by `middleShift`** (Webster,
arXiv:1209.2463v4, proof of Theorem 2.19): `middleResIndMap` sends the degree `n` part of
`MiddleTensor` into the degree `n + middleShift` part of the subquotient `S / S'` of the Mackey
filtration of `Res ∘ Ind`. -/
theorem middleResIndMap_mem_grading (hS' : Set.Iio ⇑c ⊆ S') {n : ℤ}
    {x : MiddleTensor k Γ a b c d} (hx : x ∈ middleGrading G a b c d n) :
    middleResIndMap hD hZ hP hΓ hW hL hS hcS hS' x ∈
      resIndSubquotientGrading hP hD hZ hΓ hW hL G (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) S' S (n + middleShift G a b c d) := by
  refine balancedGrading_map_mem
    (fun n' => resIndSubquotientGrading hP hD hZ hΓ hW hL G
      (rfl : a + b + (c + d) = a + b + (c + d)) (layout_eq a b c d) S' S
      (n' + middleShift G a b c d)) _ (fun i j t y ht hy => ?_) hx
  rw [middleResIndMap_tmul]
  refine Submodule.mem_map_of_mem (f := Submodule.mkQ _) ?_
  have := middleAux_mem_grade hD hZ G ht hy
  rwa [show i + middleShift G a b c d + j = i + j + middleShift G a b c d by ring] at this

end Descent

section Isomorphism

variable {P : FullChamber Γ (a + b + (c + d)) → FullChamber Γ (a + b + (c + d)) →
    (Strand (a + b + (c + d)) → 𝕜) × (Strand (a + b + (c + d)) → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hΓ : Γ.PSymm)
  (hW : ∀ w : Wall Γ (a + b + (c + d)), IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (s t : Strand (a + b + (c + d))), Γ.loop s.1 = some Q →
    s ≠ t → s.1 = t.1 → IsRegular (loopFactor Q s t))

include hD hZ hΓ hW hL in
/-- **The middle balanced tensor product is spanned by homogeneous vectors**: it is the sum of
its juxtaposed corners, each of which is spanned by homogeneous vectors. -/
theorem iSup_middleGrading : ⨆ n, middleGrading G a b c d n = ⊤ := by
  classical
  refine eq_top_iff.2 fun w _ => ?_
  have key : ∀ (L' : {C : FullChamber Γ (a + c) // C.IsRankOrdered})
      (L'' : {C : FullChamber Γ (b + d) // C.IsRankOrdered})
      (R' : {C : FullChamber Γ (a + b) // C.IsRankOrdered})
      (R'' : {C : FullChamber Γ (c + d) // C.IsRankOrdered}),
      middleCornerMap (rankE k L'.2 ⊗ₜ rankE k L''.2) (rankE k R'.2 ⊗ₜ rankE k R''.2) w ∈
        ⨆ n, middleGrading G a b c d n := by
    intro L' L'' R' R''
    set π := middleCornerMap (rankE k L'.2 ⊗ₜ rankE k L''.2) (rankE k R'.2 ⊗ₜ rankE k R''.2)
    have hmem : (⟨π w, LinearMap.mem_range_self π w⟩ : LinearMap.range π) ∈
        ⨆ n, middleCornerGrading G L'.2 L''.2 R'.2 R''.2 n := by
      rw [iSup_middleCornerGrading G hD hZ hΓ hW hL]
      exact Submodule.mem_top
    have := Submodule.mem_map_of_mem (f := (LinearMap.range π).subtype) hmem
    rw [Submodule.map_iSup] at this
    exact iSup_mono (fun n => Submodule.map_comap_le _ _) this
  have hw1 : w = middleCornerMap 1 1 w := by rw [middleCornerMap_one_one, LinearMap.id_apply]
  rw [hw1, one_tensor_eq_sum (ν' := a + c) (ν'' := b + d),
    one_tensor_eq_sum (ν' := a + b) (ν'' := c + d)]
  simp only [middleCornerMap_sum_left, middleCornerMap_sum_right, LinearMap.sum_apply]
  repeat refine Submodule.sum_mem _ fun _ _ => ?_
  exact key _ _ _ _

variable {S' S : Set (I → ℕ)} (hS : IsLowerSet S) (hcS : ⇑c ∈ S) (hS' : Set.Iio ⇑c ⊆ S')
  (hS'l : IsLowerSet S') (hcS' : ⇑c ∉ S') (hc : ∀ μ' ∈ S, μ' ∉ S' → μ' = ⇑c)

/-- **The subquotient of one shuffle type of the Mackey filtration of `Res ∘ Ind`, as a graded
space** (B. Webster, arXiv:1209.2463v4, proof of Theorem 2.19): `middleResIndEquiv` is an
isomorphism of graded spaces from the middle balanced tensor product, shifted by
`middleShift G a b c d = ∑_{i, j} b_i c_j pairDeg i j`, onto the subquotient `S / S'`. In
Webster's normalization of the grading (half of ours) the shift is `-(b · c)`. -/
noncomputable def middleResIndGradedEquiv :
    Graded.shift (middleGrading G a b c d) (middleShift G a b c d) ≃ᵍ[k]
      resIndSubquotientGrading hP hD hZ hΓ hW hL G (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) S' S :=
  GradedEquiv.ofProjections
    (middleResIndEquiv hD hZ hP hΓ hW hL hS hcS hS' hS'l hcS' hc)
    (middleShift G a b c d)
    (fun _ _ hx => middleResIndMap_mem_grading hD hZ G hP hΓ hW hL hS hcS hS' hx)
    (iSup_middleGrading hD hZ G hΓ hW hL)
    (resIndSubquotientProj hP hD hZ hΓ hW hL G _ _ S' S)
    (resIndSubquotientProj_of_mem hP hD hZ hΓ hW hL G _ _ S' S)
    (resIndSubquotientProj_of_mem_ne hP hD hZ hΓ hW hL G _ _ S' S)

theorem middleResIndGradedEquiv_apply (x : MiddleTensor k Γ a b c d) :
    middleResIndGradedEquiv hD hZ G hP hΓ hW hL hS hcS hS' hS'l hcS' hc x =
      middleResIndMap hD hZ hP hΓ hW hL hS hcS hS' x := rfl

/-- `middleResIndGradedEquiv` for the steps `S = {μ ≤ c}` and `S' = {μ < c}`. -/
noncomputable def middleResIndGradedEquivIic :
    Graded.shift (middleGrading G a b c d) (middleShift G a b c d) ≃ᵍ[k]
      resIndSubquotientGrading hP hD hZ hΓ hW hL G (rfl : a + b + (c + d) = a + b + (c + d))
        (layout_eq a b c d) (Set.Iio ⇑c) (Set.Iic ⇑c) :=
  middleResIndGradedEquiv hD hZ G hP hΓ hW hL (isLowerSet_Iic _) (Set.mem_Iic.2 le_rfl)
    subset_rfl (isLowerSet_Iio _) (fun h => lt_irrefl _ (Set.mem_Iio.1 h))
    (fun _ h h' => (Set.mem_Iic.1 h).eq_or_lt.resolve_right h')

end Isomorphism

end Juxtapose

end Categorification.WeightedKLR
