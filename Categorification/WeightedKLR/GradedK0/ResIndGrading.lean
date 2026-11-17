/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.ResIndFiltration
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
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose

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

end Categorification.WeightedKLR
