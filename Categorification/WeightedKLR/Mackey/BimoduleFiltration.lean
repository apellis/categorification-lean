/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Categorification.WeightedKLR.Mackey.Parabolic

/-!
# The Mackey filtration of Webster's algebra as a filtration by sub-bimodules

B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*, arXiv:1209.2463v4, proof of
Theorem 2.19 (after Khovanov–Lauda, arXiv:0803.4121v2, Proposition 2.18), filters `W_ν`, for
`ν₁ + ν₂ = ν = ν' + ν''`, by the shuffle type of the strands passing from the first block at the
bottom to the first block at the top, and uses that the steps are sub-bimodules for the left
action of `W_{ν₁} ⊗ W_{ν₂}` (through `ι_{ν₁;ν₂}`) and the right action of `W_{ν'} ⊗ W_{ν''}`
(through `ι_{ν';ν''}`).

The corner pieces `e D W_ν e C` of this filtration are `mackeyFilt`, whose sub-bimodule property
is `inductionMap_mul_mul_mem_mackeyFilt`. Here they are assembled into a filtration of the whole
algebra.

## Main definitions and results

* `bimoduleFilt ν' ν₁ S` : the elements `x ∈ W_ν` with `e D x e C` in the step `S` of the corner
  filtration for all rank-ordered chambers `D`, `C`.
* `bimoduleFilt_mono`, `bimoduleFilt_empty` (`= ⊥`), `bimoduleFilt_univ` (`= ⊤`).
* `inductionMap_mul_mul_mem_bimoduleFilt` : for `S` a lower set, the step `S` is stable under
  `x ↦ ι_{ν₁;ν₂}(u) x ι_{ν';ν''}(w)`.
* `e_mul_mul_e_mem_bimoduleFilt_iff` : the corner pieces of a step are the steps of the corner
  filtrations.
-/

namespace Categorification.WeightedKLR

open GalleryAlgebra
open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

namespace GalleryAlgebra

variable {P : FullChamber Γ ν → FullChamber Γ ν → (Strand ν → 𝕜) × (Strand ν → 𝕜)}
  (hP : ∀ C E, IsChamberSegment C E (P C E)) (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops)
  (hΓ : Γ.PSymm) (hW : ∀ w : Wall Γ ν, IsRegular (w.factor (k := k)))
  (hL : ∀ (Q : MvPolynomial (Fin 2) k) (a b : Strand ν), Γ.loop a.1 = some Q → a ≠ b →
    a.1 = b.1 → IsRegular (loopFactor Q a b))

/-- An element of `W_ν` is the sum of its corner pieces `e D x e C` over rank-ordered chambers. -/
theorem val_eq_sum_corner (x : WeightedKLRAlgebra k Γ ν) :
    x.1 = ∑ D ∈ Finset.univ.filter FullChamber.IsRankOrdered,
      ∑ C ∈ Finset.univ.filter FullChamber.IsRankOrdered, e D * x.1 * e C := by
  have hx := (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).1 x.2
  conv_lhs => rw [← hx.2, ← hx.1]
  simp only [rankIdem, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

variable (k) in
/-- **The Mackey filtration of `W_ν`.** The step of shuffle types `S`: the elements `x` whose
corner pieces `e D x e C` (`D`, `C` rank-ordered) lie in the step `S` of the corner filtration. -/
noncomputable def bimoduleFilt (ν' ν₁ : I →₀ ℕ) (S : Set (I → ℕ)) :
    Submodule k (WeightedKLRAlgebra k Γ ν) where
  carrier := {x | ∀ D C : FullChamber Γ ν, D.IsRankOrdered → C.IsRankOrdered →
    e D * x.1 * e C ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S}
  add_mem' {x y} hx hy D C hD' hC' := by
    have : e D * (x + y).1 * e C = e D * x.1 * e C + e D * y.1 * e C := by
      change e D * (x.1 + y.1) * e C = _
      rw [mul_add, add_mul]
    rw [this]
    exact add_mem (hx D C hD' hC') (hy D C hD' hC')
  zero_mem' D C _ _ := by
    change e D * (0 : GalleryAlgebra k Γ ν) * e C ∈ _
    rw [mul_zero, zero_mul]
    exact zero_mem _
  smul_mem' c x hx D C hD' hC' := by
    have : e D * (c • x).1 * e C = c • (e D * x.1 * e C) := by
      change e D * (c • x.1) * e C = _
      rw [mul_smul_comm, smul_mul_assoc]
    rw [this]
    exact Submodule.smul_mem _ c (hx D C hD' hC')

theorem mem_bimoduleFilt_iff (ν' ν₁ : I →₀ ℕ) (S : Set (I → ℕ)) (x : WeightedKLRAlgebra k Γ ν) :
    x ∈ bimoduleFilt k hP hD hZ hΓ hW hL ν' ν₁ S ↔
      ∀ D C : FullChamber Γ ν, D.IsRankOrdered → C.IsRankOrdered →
        e D * x.1 * e C ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S := Iff.rfl

theorem bimoduleFilt_mono (ν' ν₁ : I →₀ ℕ) {S S' : Set (I → ℕ)} (h : S ⊆ S') :
    bimoduleFilt k hP hD hZ hΓ hW hL ν' ν₁ S ≤ bimoduleFilt k hP hD hZ hΓ hW hL ν' ν₁ S' :=
  fun _ hx D C hD' hC' => mackeyFilt_mono hP hD hZ hΓ hW hL ν' ν₁ D C h (hx D C hD' hC')

/-- The bottom step of the filtration of `W_ν` is zero. -/
theorem bimoduleFilt_empty (ν' ν₁ : I →₀ ℕ) :
    bimoduleFilt k hP hD hZ hΓ hW hL ν' ν₁ ∅ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun x hx => Subtype.ext ?_
  rw [val_eq_sum_corner x]
  refine Finset.sum_eq_zero fun D hD' => Finset.sum_eq_zero fun C hC' => ?_
  have := hx D C (Finset.mem_filter.1 hD').2 (Finset.mem_filter.1 hC').2
  rwa [mackeyFilt_empty, Submodule.mem_bot] at this

/-- The filtration of `W_ν` exhausts `W_ν`. -/
theorem bimoduleFilt_univ (ν' ν₁ : I →₀ ℕ) :
    bimoduleFilt k hP hD hZ hΓ hW hL ν' ν₁ Set.univ = ⊤ := by
  refine eq_top_iff.2 fun x _ D C _ _ => ?_
  rw [mackeyFilt_univ, mem_cornerSpace_iff, ← mul_assoc, ← mul_assoc, e_mul_e_self,
    mul_assoc _ _ (e C), mul_assoc _ _ (e C), e_mul_e_self, ← mul_assoc]

/-- The corner pieces of a step of the filtration of `W_ν` are the steps of the corner
filtrations. -/
theorem e_mul_mul_e_mem_bimoduleFilt_iff (ν' ν₁ : I →₀ ℕ) {S : Set (I → ℕ)}
    {D C : FullChamber Γ ν} (hD' : D.IsRankOrdered) (hC' : C.IsRankOrdered)
    {z : GalleryAlgebra k Γ ν} (hz : z ∈ cornerSpace k D C) :
    (⟨z, (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).2
        (by
          rw [mem_cornerSpace_iff] at hz
          constructor
          · rw [← hz, ← mul_assoc, ← mul_assoc, rankIdem_mul_e]
            simp [hD']
          · rw [← hz, mul_assoc, e_mul_rankIdem]
            simp [hC'])⟩ :
        WeightedKLRAlgebra k Γ ν) ∈ bimoduleFilt k hP hD hZ hΓ hW hL ν' ν₁ S ↔
      z ∈ mackeyFilt k hP hD hZ hΓ hW hL ν' ν₁ D C S := by
  have hz' := (mem_cornerSpace_iff).1 hz
  constructor
  · intro h
    have := h D C hD' hC'
    simp only at this
    rwa [hz'] at this
  · intro h D' C' _ _
    simp only
    have hzl : e D * z = z := by rw [← hz', ← mul_assoc, ← mul_assoc, e_mul_e_self]
    have hzr : z * e C = z := by rw [← hz', mul_assoc, e_mul_e_self]
    by_cases hDD : D' = D
    · subst hDD
      by_cases hCC : C' = C
      · subst hCC
        rwa [hz']
      · have hCC' : ¬ C = C' := fun h => hCC h.symm
        rw [← hzr, mul_assoc, mul_assoc, e_mul_e]
        simp [hCC']
    · rw [← hzl, ← mul_assoc, e_mul_e]
      simp [hDD]

/-- **The steps of the Mackey filtration of `W_ν` are sub-bimodules** (B. Webster,
arXiv:1209.2463v4, proof of Theorem 2.19). For `ν₁ + ν₂ = ν = ν' + ν''` and a lower set `S` of
shuffle types, the step `S` is stable under `x ↦ ι_{ν₁;ν₂}(u) x ι_{ν';ν''}(w)`. -/
theorem inductionMap_mul_mul_mem_bimoduleFilt {ν₁ ν₂ ν' ν'' : I →₀ ℕ} (h : ν₁ + ν₂ = ν)
    (h' : ν' + ν'' = ν) {S : Set (I → ℕ)} (hS : IsLowerSet S)
    (u : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (w : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'')
    {x : WeightedKLRAlgebra k Γ ν} (hx : x ∈ bimoduleFilt k hP hD hZ hΓ hW hL ν' ν₁ S) :
    castW k Γ h (Juxtapose.inductionMap k Γ ν₁ ν₂ u) * x *
        castW k Γ h' (Juxtapose.inductionMap k Γ ν' ν'' w) ∈
      bimoduleFilt k hP hD hZ hΓ hW hL ν' ν₁ S := by
  intro D' C' hD₁ hC₁
  change e D' * ((castW k Γ h (Juxtapose.inductionMap k Γ ν₁ ν₂ u)).1 * x.1 *
    (castW k Γ h' (Juxtapose.inductionMap k Γ ν' ν'' w)).1) * e C' ∈ _
  rw [castW_val, castW_val, val_eq_sum_corner x]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun D hD₀ => Submodule.sum_mem _ fun C hC₀ => ?_
  have hD₀' := (Finset.mem_filter.1 hD₀).2
  have hC₀' := (Finset.mem_filter.1 hC₀).2
  have := inductionMap_mul_mul_mem_mackeyFilt hP hD hZ hΓ hW hL h h' hC₀' hC₁ hD₀' hD₁ hS u w
    (hx D C hD₀' hC₀')
  simpa only [mul_assoc] using this

end GalleryAlgebra

end Categorification.WeightedKLR
