/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Categorification.WeightedKLR.Mackey.FourBlockType

/-!
# The shuffle element of a shuffle type

A step of the proof of B. Webster, *Weighted Khovanov–Lauda–Rouquier algebras*,
arXiv:1209.2463v4, Theorem 2.19 (the Mackey filtration of §2.4, after Khovanov–Lauda,
arXiv:0803.4121v2, Proposition 2.18). The generator of the subquotient of type `μ` is not the
shuffle element `ψ^W_g` of one relabelling `g` (these depend on the chamber `C`), but the sum
`ψ_μ` of the four-block shuffle elements over all four-block chambers for the set
`blockLeft ν' ν₁ μ` (`GalleryAlgebra.typeShuffle`). Every `ψ^W_g` of type `μ` is
`ψ_μ * e (rankShuffleBot g C)` (`GalleryAlgebra.rankShuffleElt_eq_typeShuffle_mul_e`), and the
idempotent `e (rankShuffleBot g C)` is the image under `ι` of an idempotent of
`W_{ν'} ⊗ W_{ν''}`. Hence the map `x ⊗ y ↦ e D ι(x) ψ^W_g ι(y) e C` factors through
`x ⊗ y ↦ e D ι(x) ψ_μ ι(y) e C` (`GalleryAlgebra.shuffleInductionAux_eq_comp`), and its range
lies in the range of the latter (`GalleryAlgebra.range_shuffleInductionAux_le`): one map per
shuffle type.

## Main definitions

* `GalleryAlgebra.typeShuffle`: the sum `ψ_μ` of the four-block shuffle elements.
* `GalleryAlgebra.typeInductionAux`: `x ⊗ y ↦ e D ι(x) ψ_μ ι(y) e C`.

## Main results

* `GalleryAlgebra.rankShuffleElt_eq_typeShuffle_mul_e`: `ψ^W_g = ψ_μ * e (rankShuffleBot g C)`.
* `GalleryAlgebra.range_shuffleInductionAux_le`: the range of the map of `g` lies in the range
  of the map of the shuffle type of `g`.
-/

namespace Categorification.WeightedKLR

open FullChamber GalleryAlgebra Juxtapose

open scoped TensorProduct

variable {I : Type*} [DecidableEq I] {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] {k : Type*} [CommRing k] {Γ : WeightedGraph I 𝕜 k} {ν : I →₀ ℕ}

omit [DecidableEq I] in
/-- A four-block chamber for `X` and `Z` is separated by `X`. -/
theorem FullChamber.IsFourBlock.isSeparated {X Z : Strand ν → Bool} {B : FullChamber Γ ν}
    (hB : IsFourBlock X Z B) : IsSeparated X B := by
  rw [← hB.2]
  exact isSeparated_sep _ _ _

namespace GalleryAlgebra

variable {ν' ν'' ν₁ ν₂ : I →₀ ℕ}

variable (k) in
open Classical in
/-- **The shuffle element of a shuffle type.** The sum of the four-block shuffle elements
`fourShuffle Z B` over all four-block chambers `B` for `X` and `Z`; for `X` the strands of `ν'`
and `Z = blockLeft ν' ν₁ μ`, Webster's generator of the subquotient of type `μ` of the Mackey
filtration (arXiv:1209.2463v4, Theorem 2.19). -/
noncomputable def typeShuffle (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (X Z : Strand ν → Bool) :
    GalleryAlgebra k Γ ν :=
  ∑ B ∈ Finset.univ.filter fun B : FullChamber Γ ν => IsFourBlock X Z B, fourShuffle k hD hZ Z B

theorem typeShuffle_mul_e (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {X Z : Strand ν → Bool}
    {B : FullChamber Γ ν} (hB : IsFourBlock X Z B) :
    typeShuffle k hD hZ X Z * e B = fourShuffle k hD hZ Z B := by
  classical
  rw [typeShuffle, Finset.sum_mul,
    Finset.sum_eq_single_of_mem B (Finset.mem_filter.2 ⟨Finset.mem_univ _, hB⟩)
      fun B' _ hne => fourShuffle_mul_e_of_ne hD hZ Z hne,
    fourShuffle_mul_e]

theorem typeShuffle_mul_e_of_not (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) {X Z : Strand ν → Bool}
    {B : FullChamber Γ ν} (hB : ¬ IsFourBlock X Z B) : typeShuffle k hD hZ X Z * e B = 0 := by
  classical
  rw [typeShuffle, Finset.sum_mul]
  refine Finset.sum_eq_zero fun B' hB' => fourShuffle_mul_e_of_ne hD hZ Z fun h => hB ?_
  rw [← h]
  exact (Finset.mem_filter.1 hB').2

/-- **`ψ^W_g` is the shuffle element of its type, cut down to its bottom chamber.** For `C`
separated by the strands of `ν'`, `ψ^W_g = ψ_μ * e (rankShuffleBot g C)`, `μ` the shuffle type
of `g` (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem rankShuffleElt_eq_typeShuffle_mul_e (hν' : ν' + ν'' = ν) (hν₁ : ν₁ + ν₂ = ν)
    (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (g : ColPerm ν) {C : FullChamber Γ ν}
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) :
    rankShuffleElt k hν' hν₁ hD hZ g C =
      typeShuffle k hD hZ (fun t => decide (t.IsLeft ν')) (blockLeft ν' ν₁ (shuffleType ν' ν₁ g)) *
        e (rankShuffleBot hν' ν₁ g C) := by
  obtain ⟨h1, h2⟩ := rankShuffleElt_eq_fourShuffle_blockLeft hν' hν₁ hD hZ g hCs
  rw [typeShuffle_mul_e hD hZ h2, h1]

/-- `ι` is multiplicative. -/
theorem inductionVal_mul (hν : ν₁ + ν₂ = ν)
    (a b : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) :
    inductionVal k hν (a * b) = inductionVal k hν a * inductionVal k hν b := by
  rw [inductionVal_apply, inductionVal_apply, inductionVal_apply, map_mul]
  exact map_mul (castGallery k Γ hν) _ _

/-- The idempotent of a rank-ordered chamber separated by the strands of `ν₁` is the image under
`ι` of an idempotent of `W_{ν₁} ⊗ W_{ν₂}`. -/
theorem exists_inductionVal_eq_e (hν : ν₁ + ν₂ = ν) {B : FullChamber Γ ν}
    (hB : B.IsRankOrdered) (hBs : IsSeparated (fun t => decide (t.IsLeft ν₁)) B) :
    ∃ z : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂,
      inductionVal k hν z = e B := by
  subst hν
  have hEq : B = chamber ((leftEmb ν₁ ν₂).restrict B) ((rightEmb ν₁ ν₂).restrict B) :=
    eq_chamber_of_isSeparated hBs
  rw [hEq] at hB ⊢
  obtain ⟨h', h''⟩ := (isRankOrdered_chamber_iff _ _).1 hB
  refine ⟨⟨e ((leftEmb ν₁ ν₂).restrict B), (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).2
      ⟨by rw [rankIdem_mul_e, ite_eq_left h'], by rw [e_mul_rankIdem, ite_eq_left h']⟩⟩ ⊗ₜ
    ⟨e ((rightEmb ν₁ ν₂).restrict B), (Subsemigroup.mem_corner_iff isIdempotentElem_rankIdem).2
      ⟨by rw [rankIdem_mul_e, ite_eq_left h''], by rw [e_mul_rankIdem, ite_eq_left h'']⟩⟩, ?_⟩
  rw [inductionVal_apply, castGallery_rfl]
  exact inductionMap_e_tmul_e h' h''

variable (k) in
/-- `x ⊗ y ↦ e D ι(x) ψ_μ ι(y) e C`, for the shuffle element `ψ_μ = typeShuffle X Z` of a
shuffle type. -/
noncomputable def typeInductionAux (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) (D C : FullChamber Γ ν) (Z : Strand ν → Bool) :
    (WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂) ⊗[k]
        (WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') →ₗ[k]
      GalleryAlgebra k Γ ν :=
  TensorProduct.lift <| LinearMap.mk₂ k
    (fun x y => e D * inductionVal k hν₁ x *
      typeShuffle k hD hZ (fun t => decide (t.IsLeft ν')) Z * inductionVal k hν' y * e C)
    (fun a b y => by simp only [map_add, mul_add, add_mul])
    (fun c a y => by simp only [map_smul, mul_smul_comm, smul_mul_assoc])
    (fun x a b => by simp only [map_add, mul_add, add_mul])
    (fun c x a => by simp only [map_smul, mul_smul_comm, smul_mul_assoc])

theorem typeInductionAux_tmul (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) (D C : FullChamber Γ ν) (Z : Strand ν → Bool)
    (x : WeightedKLRAlgebra k Γ ν₁ ⊗[k] WeightedKLRAlgebra k Γ ν₂)
    (y : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'') :
    typeInductionAux k hD hZ hν' hν₁ D C Z (x ⊗ₜ y) =
      e D * inductionVal k hν₁ x * typeShuffle k hD hZ (fun t => decide (t.IsLeft ν')) Z *
        inductionVal k hν' y * e C := rfl

/-- **The map of `g` factors through the map of its shuffle type.** For `C` separated by the
strands of `ν'`, `x ⊗ y ↦ e D ι(x) ψ^W_g ι(y) e C` is `x ⊗ y ↦ e D ι(x) ψ_μ ι(z y) e C` for an
idempotent `z` of `W_{ν'} ⊗ W_{ν''}`, `μ` the shuffle type of `g` (Webster,
arXiv:1209.2463v4, Theorem 2.19). -/
theorem shuffleInductionAux_eq_comp (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) (D C : FullChamber Γ ν) (g : ColPerm ν)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) :
    ∃ z : WeightedKLRAlgebra k Γ ν' ⊗[k] WeightedKLRAlgebra k Γ ν'',
      shuffleInductionAux k hD hZ hν' hν₁ D C g =
        typeInductionAux k hD hZ hν' hν₁ D C (blockLeft ν' ν₁ (shuffleType ν' ν₁ g)) ∘ₗ
          TensorProduct.map LinearMap.id (LinearMap.mulLeft k z) := by
  have hB := (rankShuffleElt_eq_fourShuffle_blockLeft (k := k) hν' hν₁ hD hZ g hCs).2
  obtain ⟨z, hz⟩ := exists_inductionVal_eq_e (k := k) hν'
    (isRankOrdered_rankShuffleBot (k := k) hν' ν₁ g C) hB.isSeparated
  refine ⟨z, TensorProduct.ext' fun x y => ?_⟩
  rw [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply,
    typeInductionAux_tmul, inductionVal_mul, hz]
  change e D * inductionVal k hν₁ x * rankShuffleElt k hν' hν₁ hD hZ g C *
    inductionVal k hν' y * e C = _
  rw [rankShuffleElt_eq_typeShuffle_mul_e hν' hν₁ hD hZ g hCs]
  simp only [mul_assoc]

/-- **One map per shuffle type.** For `C` separated by the strands of `ν'`, the range of
`x ⊗ y ↦ e D ι(x) ψ^W_g ι(y) e C` lies in the range of `x ⊗ y ↦ e D ι(x) ψ_μ ι(y) e C`, `μ` the
shuffle type of `g` (Webster, arXiv:1209.2463v4, Theorem 2.19). -/
theorem range_shuffleInductionAux_le (hD : Γ.Dagger) (hZ : Γ.NoZeroLoops) (hν' : ν' + ν'' = ν)
    (hν₁ : ν₁ + ν₂ = ν) (D C : FullChamber Γ ν) (g : ColPerm ν)
    (hCs : IsSeparated (fun t => decide (t.IsLeft ν')) C) :
    LinearMap.range (shuffleInductionAux k hD hZ hν' hν₁ D C g) ≤
      LinearMap.range
        (typeInductionAux k hD hZ hν' hν₁ D C (blockLeft ν' ν₁ (shuffleType ν' ν₁ g))) := by
  obtain ⟨z, hz⟩ := shuffleInductionAux_eq_comp (k := k) hD hZ hν' hν₁ D C g hCs
  rw [hz]
  exact LinearMap.range_comp_le_range _ _

end GalleryAlgebra

end Categorification.WeightedKLR
