/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.MiddleLeading

/-!
# The Mackey filtration of `Res ∘ Ind`

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18). For
`ν₁ + ν₂ = ν = ν' + ν''`, the bimodule `Res_{ν₁;ν₂} Ind_{ν';ν''}` is `ι(1) W_ν ι(1)`, a
`(W_{ν₁} ⊗ W_{ν₂}, W_{ν'} ⊗ W_{ν''})`-bimodule through `ι_{ν₁;ν₂}` and `ι_{ν';ν''}`. It is filtered
by the shuffle type of the strands passing from the first block at the bottom to the first block
at the top.

Here this filtration is defined on the elements `z` of the gallery algebra with
`ι_{ν₁;ν₂}(1) z = z = z ι_{ν';ν''}(1)`: the step `S` consists of those `z` whose corners
`e D z e C` (`D`, `C` rank-ordered) lie in the step `S` of the corner filtration `mackeyFilt`.

## Main definitions and results

* `resIndFilt hν' hν₁ S`: the step `S` of the filtration.
* `resIndFilt_mono`, `resIndFilt_empty` (`= ⊥`).
* `inductionVal_mul_mul_mem_resIndFilt`: for `S` a lower set, the step `S` is stable under
  `z ↦ ι_{ν₁;ν₂}(u) z ι_{ν';ν''}(w)`.
* `ResIndSubquotient S' S`: the quotient of the step `S` by the step `S'`, with the corner
  projections `resIndCornerProj` onto the subquotients `MackeySubquotient` of the corners and the
  multiplication maps `resIndSubquotientMul` (the bimodule structure).
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

variable {ν₁ ν₂ ν' ν'' : I →₀ ℕ}

/-- `ι_{ν₁;ν₂}(1) z ι_{ν';ν''}(1)` is the sum of the corners `e D z e C` with `D`, `C` the
juxtapositions of rank-ordered chambers. -/
theorem inductionVal_one_mul_mul_one (hν₁ : ν₁ + ν₂ = ν) (hν' : ν' + ν'' = ν)
    (z : GalleryAlgebra k Γ ν) :
    inductionVal k hν₁ 1 * z * inductionVal k hν' 1 =
      ∑ D' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
        ∑ D'' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
          ∑ C' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
            ∑ C'' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
              e (castChamber hν₁ (chamber (Γ := Γ) D' D'')) * z *
                e (castChamber hν' (chamber (Γ := Γ) C' C'')) := by
  rw [inductionVal_one, inductionVal_one, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun D' _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun D'' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun C' _ => ?_
  rw [Finset.mul_sum]

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

variable (k) in
/-- **The Mackey filtration of `Res_{ν₁;ν₂} Ind_{ν';ν''}`** (B. Webster, arXiv:1209.2463v4,
proof of Theorem 2.19). The step of shuffle types `S`: the elements `z` with
`ι_{ν₁;ν₂}(1) z = z = z ι_{ν';ν''}(1)` whose corners `e D z e C` (`D`, `C` rank-ordered) lie in the
step `S` of the corner filtration. -/
noncomputable def resIndFilt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S : Set (I → ℕ)) :
    Submodule k (GalleryAlgebra k Γ ν) where
  carrier := {z | inductionVal k hν₁ 1 * z = z ∧ z * inductionVal k hν' 1 = z ∧
    ∀ D C : FullChamber Γ ν, D.IsRankOrdered → C.IsRankOrdered →
      e D * z * e C ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S}
  add_mem' {x y} hx hy := ⟨by rw [mul_add, hx.1, hy.1], by rw [add_mul, hx.2.1, hy.2.1],
    fun D C hD' hC' => by
      rw [mul_add, add_mul]
      exact add_mem (hx.2.2 D C hD' hC') (hy.2.2 D C hD' hC')⟩
  zero_mem' := ⟨mul_zero _, zero_mul _, fun D C _ _ => by
    rw [mul_zero, zero_mul]
    exact zero_mem _⟩
  smul_mem' c x hx := ⟨by rw [mul_smul_comm, hx.1], by rw [smul_mul_assoc, hx.2.1],
    fun D C hD' hC' => by
      rw [mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ c (hx.2.2 D C hD' hC')⟩

theorem mem_resIndFilt_iff (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S : Set (I → ℕ))
    (z : GalleryAlgebra k Γ ν) :
    z ∈ resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S ↔
      inductionVal k hν₁ 1 * z = z ∧ z * inductionVal k hν' 1 = z ∧
        ∀ D C : FullChamber Γ ν, D.IsRankOrdered → C.IsRankOrdered →
          e D * z * e C ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S := Iff.rfl

theorem resIndFilt_mono (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) {S S' : Set (I → ℕ)}
    (h : S ⊆ S') :
    resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S ≤ resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S' :=
  fun _ hz => ⟨hz.1, hz.2.1, fun D C hD' hC' =>
    mackeyFilt_mono hP hD hZ hΓ hW hL ν' ν₁ D C h (hz.2.2 D C hD' hC')⟩

/-- An element of the filtration is the sum of its juxtaposed corners. -/
theorem eq_sum_corner_of_mem_resIndFilt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {S : Set (I → ℕ)} {z : GalleryAlgebra k Γ ν}
    (hz : z ∈ resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S) :
    z = ∑ D' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
        ∑ D'' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
          ∑ C' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
            ∑ C'' ∈ Finset.univ.filter FullChamber.IsRankOrdered,
              e (castChamber hν₁ (chamber (Γ := Γ) D' D'')) * z *
                e (castChamber hν' (chamber (Γ := Γ) C' C'')) := by
  rw [← inductionVal_one_mul_mul_one hν₁ hν', hz.1, hz.2.1]

/-- The bottom step of the filtration is zero. -/
theorem resIndFilt_empty (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) :
    resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ ∅ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun z hz => ?_
  rw [eq_sum_corner_of_mem_resIndFilt hP hD hZ hΓ hW hL hν' hν₁ hz]
  refine Finset.sum_eq_zero fun D' hD' => Finset.sum_eq_zero fun D'' hD'' =>
    Finset.sum_eq_zero fun C' hC' => Finset.sum_eq_zero fun C'' hC'' => ?_
  have := hz.2.2 _ _
    ((isRankOrdered_castChamber_chamber_iff hν₁ D' D'').2
      ⟨(Finset.mem_filter.1 hD').2, (Finset.mem_filter.1 hD'').2⟩)
    ((isRankOrdered_castChamber_chamber_iff hν' C' C'').2
      ⟨(Finset.mem_filter.1 hC').2, (Finset.mem_filter.1 hC'').2⟩)
  rwa [mackeyFilt_empty, Submodule.mem_bot] at this

/-- **The steps of the Mackey filtration of `Res ∘ Ind` are sub-bimodules** (B. Webster,
arXiv:1209.2463v4, proof of Theorem 2.19). For a lower set `S` of shuffle types, the step `S` is
stable under `z ↦ ι_{ν₁;ν₂}(u) z ι_{ν';ν''}(w)`. -/
theorem inductionVal_mul_mul_mem_resIndFilt (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {S : Set (I → ℕ)} (hS : IsLowerSet S)
    (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    {z : GalleryAlgebra k Γ ν} (hz : z ∈ resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S) :
    inductionVal k hν₁ u * z * inductionVal k hν' w ∈
      resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S := by
  refine ⟨?_, ?_, fun D C hD₁ hC₁ => ?_⟩
  · rw [← mul_assoc, ← mul_assoc, ← inductionVal_mul, one_mul]
  · rw [mul_assoc, ← inductionVal_mul, mul_one]
  · rw [eq_sum_corner_of_mem_resIndFilt hP hD hZ hΓ hW hL hν' hν₁ hz]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun D' hD' => Submodule.sum_mem _ fun D'' hD'' =>
      Submodule.sum_mem _ fun C' hC' => Submodule.sum_mem _ fun C'' hC'' => ?_
    have hDj := (isRankOrdered_castChamber_chamber_iff hν₁ D' D'').2
      ⟨(Finset.mem_filter.1 hD').2, (Finset.mem_filter.1 hD'').2⟩
    have hCj := (isRankOrdered_castChamber_chamber_iff hν' C' C'').2
      ⟨(Finset.mem_filter.1 hC').2, (Finset.mem_filter.1 hC'').2⟩
    have := inductionMap_mul_mul_mem_mackeyFilt hP hD hZ hΓ hW hL hν₁ hν' hCj hC₁ hDj hD₁ hS u w
      (hz.2.2 _ _ hDj hCj)
    simpa only [mul_assoc, inductionVal_apply] using this

variable (k) in
/-- **The subquotients of the Mackey filtration of `Res ∘ Ind`**: the quotient of the step `S`
by the step `S'`. -/
abbrev ResIndSubquotient (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S' S : Set (I → ℕ)) :=
  resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S ⧸
    (resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S').comap
      (resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S).subtype

/-- The corner `z ↦ e D z e C` of a step of the filtration. -/
noncomputable def resIndCorner (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S : Set (I → ℕ))
    {D C : FullChamber Γ ν} (hD' : D.IsRankOrdered) (hC' : C.IsRankOrdered) :
    resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S →ₗ[k] mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S :=
  LinearMap.codRestrict _
    ((LinearMap.mulRight k (e C) ∘ₗ LinearMap.mulLeft k (e D)) ∘ₗ
      (resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S).subtype)
    fun x => x.2.2.2 D C hD' hC'

theorem coe_resIndCorner (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) (S : Set (I → ℕ))
    {D C : FullChamber Γ ν} (hD' : D.IsRankOrdered) (hC' : C.IsRankOrdered)
    (z : resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S) :
    (resIndCorner hP hD hZ hΓ hW hL hν' hν₁ S hD' hC' z : GalleryAlgebra k Γ ν) =
      e D * z.1 * e C := rfl

/-- **The corner projections of the subquotients**: `[z] ↦ [e D z e C]`, from the subquotient of
`Res ∘ Ind` to that of the corner `e D W_ν e C`. -/
noncomputable def resIndCornerProj (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {S' S : Set (I → ℕ)} {D C : FullChamber Γ ν} (hD' : D.IsRankOrdered)
    (hC' : C.IsRankOrdered) :
    ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S →ₗ[k]
      MackeySubquotient k hP hD hZ hΓ hW hL ν' ν₁ D C S' S :=
  Submodule.mapQ _ _ (resIndCorner hP hD hZ hΓ hW hL hν' hν₁ S hD' hC') fun _ hz =>
    hz.2.2 D C hD' hC'

theorem resIndCornerProj_mk (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {S' S : Set (I → ℕ)} {D C : FullChamber Γ ν} (hD' : D.IsRankOrdered)
    (hC' : C.IsRankOrdered) (z : resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S) :
    resIndCornerProj hP hD hZ hΓ hW hL hν' hν₁ (S' := S') hD' hC' (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (resIndCorner hP hD hZ hΓ hW hL hν' hν₁ S hD' hC' z) := rfl

/-- Multiplication `z ↦ ι_{ν₁;ν₂}(u) z ι_{ν';ν''}(w)` on a step of the filtration. -/
noncomputable def resIndFiltMul (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) {S : Set (I → ℕ)}
    (hS : IsLowerSet S) (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S →ₗ[k] resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S :=
  LinearMap.codRestrict _
    ((LinearMap.mulRight k (inductionVal k hν' w) ∘ₗ LinearMap.mulLeft k (inductionVal k hν₁ u))
      ∘ₗ (resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S).subtype)
    fun x => inductionVal_mul_mul_mem_resIndFilt hP hD hZ hΓ hW hL hν' hν₁ hS u w x.2

theorem coe_resIndFiltMul (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν) {S : Set (I → ℕ)}
    (hS : IsLowerSet S) (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    (z : resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S) :
    (resIndFiltMul hP hD hZ hΓ hW hL hν' hν₁ hS u w z : GalleryAlgebra k Γ ν) =
      inductionVal k hν₁ u * z.1 * inductionVal k hν' w := rfl

/-- **The bimodule structure of the subquotients**: `[z] ↦ [ι_{ν₁;ν₂}(u) z ι_{ν';ν''}(w)]`, for
lower sets `S' ⊆ S`. -/
noncomputable def resIndSubquotientMul (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {S' S : Set (I → ℕ)} (hS' : IsLowerSet S') (hS : IsLowerSet S)
    (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S →ₗ[k]
      ResIndSubquotient k hP hD hZ hΓ hW hL hν' hν₁ S' S :=
  Submodule.mapQ _ _ (resIndFiltMul hP hD hZ hΓ hW hL hν' hν₁ hS u w) fun _ hz =>
    inductionVal_mul_mul_mem_resIndFilt hP hD hZ hΓ hW hL hν' hν₁ hS' u w hz

theorem resIndSubquotientMul_mk (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    {S' S : Set (I → ℕ)} (hS' : IsLowerSet S') (hS : IsLowerSet S)
    (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    (z : resIndFilt k hP hD hZ hΓ hW hL hν' hν₁ S) :
    resIndSubquotientMul hP hD hZ hΓ hW hL hν' hν₁ hS' hS u w (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (resIndFiltMul hP hD hZ hΓ hW hL hν' hν₁ hS u w z) := rfl

end GalleryAlgebra

end Categorification.WeightedKLR
